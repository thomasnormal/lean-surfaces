// Parser-native floating literal observations for the C extractor.
// APFloat's bit pattern is the frontend-decided, rounded value; no source
// spelling is decoded by this probe.
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/AST/Expr.h"
#include "clang/Basic/Version.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/JSON.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <vector>

#if CLANG_VERSION_MAJOR != 21 || CLANG_VERSION_MINOR != 1 || CLANG_VERSION_PATCHLEVEL != 8
#error "floating bits probe supports only Clang 21.1.8"
#endif
#if LLVM_VERSION_MAJOR != 21 || LLVM_VERSION_MINOR != 1 || LLVM_VERSION_PATCH != 8
#error "floating bits probe supports only LLVM 21.1.8"
#endif

namespace {
class Visitor : public clang::RecursiveASTVisitor<Visitor> {
public:
  llvm::json::Array records;
  const clang::SourceManager *sources = nullptr;
  bool VisitFloatingLiteral(clang::FloatingLiteral *literal) {
    const auto loc = sources->getExpansionLoc(literal->getBeginLoc());
    // Offsets are joined to the source file's JSON AST.  Header literals and
    // macro-only locations have no such identity and must not collide with a
    // source-file offset from another buffer.
    if (!sources->isWrittenInMainFile(loc)) return true;
    const auto expansion_end = sources->getExpansionLoc(literal->getEndLoc());
    const auto end = clang::Lexer::getLocForEndOfToken(
        expansion_end, 0, *sources, clang::LangOptions());
    const auto begin = sources->getFileOffset(loc);
    const auto finish = end.isValid() ? sources->getFileOffset(end) : begin;
    const auto bits = literal->getValue().bitcastToAPInt();
    llvm::SmallString<32> bits_text;
    bits.toStringUnsigned(bits_text, 16);
    llvm::json::Object record{
      {"kind", "FloatingLiteral"},
      {"offset", static_cast<int64_t>(begin)},
      {"token_length", static_cast<int64_t>(finish - begin)},
      {"bit_width", static_cast<int64_t>(bits.getBitWidth())},
      {"bits_hex", bits_text.str().str()},
      {"type", literal->getType().getAsString()}};
    records.push_back(std::move(record));
    return true;
  }
};
class Consumer : public clang::ASTConsumer {
public:
  void HandleTranslationUnit(clang::ASTContext &context) override {
    Visitor v; v.sources = &context.getSourceManager();
    if (!v.TraverseDecl(context.getTranslationUnitDecl())) return;
    llvm::outs() << llvm::json::Value(std::move(v.records)) << "\n";
  }
};
class Action : public clang::PluginASTAction {
public:
  std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
      clang::CompilerInstance &, llvm::StringRef) override {
    return std::make_unique<Consumer>();
  }
  bool ParseArgs(const clang::CompilerInstance &compiler,
                 const std::vector<std::string> &args) override {
    if (!args.empty()) {
      auto id = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error,
          "floating bits probe accepts no plugin arguments");
      compiler.getDiagnostics().Report(id);
      return false;
    }
    const std::string expected = "clang version " CLANG_VERSION_STRING;
    const std::string runtime = clang::getClangFullVersion();
    if (runtime != expected &&
        !llvm::StringRef(runtime).starts_with(expected + " ")) {
      auto id = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error,
          "floating bits probe header/runtime version mismatch");
      compiler.getDiagnostics().Report(id);
      return false;
    }
    return true;
  }
  ActionType getActionType() override { return ReplaceAction; }
};
clang::FrontendPluginRegistry::Add<Action> registration(
    "lean-c-floating-bits", "emit parser-rounded floating literal bits");
}
