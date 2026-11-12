// Parser-native StringLiteral byte observations for the C extractor.
//
// This is deliberately a Clang AST plugin: the JSON AST exposes the source
// spelling (`"\\n"`), while StringLiteral::getBytes() is Clang's decoded
// semantic byte sequence.  The extractor may join these records by the
// source offset already carried by its envelope; it must never decode the
// spelling itself.
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/AST/Expr.h"
#include "clang/Basic/Version.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

#include <memory>
#include <string>
#include <vector>

#if CLANG_VERSION_MAJOR != 21 || CLANG_VERSION_MINOR != 1 || CLANG_VERSION_PATCHLEVEL != 8
#error "string byte probe supports only Clang 21.1.8 headers"
#endif

#if LLVM_VERSION_MAJOR != 21 || LLVM_VERSION_MINOR != 1 || LLVM_VERSION_PATCH != 8
#error "string byte probe supports only LLVM 21.1.8 headers"
#endif

namespace {

class Visitor : public clang::RecursiveASTVisitor<Visitor> {
public:
  llvm::json::Array records;
  const clang::SourceManager *sources = nullptr;

  bool VisitStringLiteral(clang::StringLiteral *literal) {
    llvm::json::Array bytes;
    for (unsigned char byte : literal->getBytes())
      bytes.push_back(static_cast<int64_t>(byte));
    const auto location = sources->getExpansionLoc(literal->getBeginLoc());
    if (!sources->isWrittenInMainFile(location)) return true;
    const auto end_location = sources->getExpansionLoc(literal->getEndLoc());
    const auto end = clang::Lexer::getLocForEndOfToken(
        end_location, 0, *sources, clang::LangOptions());
    const auto begin_offset = sources->getFileOffset(location);
    const auto end_offset = end.isValid() ? sources->getFileOffset(end) : begin_offset;
    llvm::json::Object record{
        {"kind", "StringLiteral"},
        {"offset", static_cast<int64_t>(begin_offset)},
        {"token_length", static_cast<int64_t>(end_offset - begin_offset)},
        {"char_byte_width", static_cast<int64_t>(literal->getCharByteWidth())},
        {"kind_name", literal->isOrdinary() ? "ordinary" :
                       literal->isWide() ? "wide" :
                       literal->isUTF8() ? "utf8" :
                       literal->isUTF16() ? "utf16" :
                       literal->isUTF32() ? "utf32" : "unevaluated"},
        {"bytes", std::move(bytes)}};
    records.push_back(std::move(record));
    return true;
  }
};

class Consumer : public clang::ASTConsumer {
public:
  void HandleTranslationUnit(clang::ASTContext &context) override {
    Visitor visitor;
    visitor.sources = &context.getSourceManager();
    if (!visitor.TraverseDecl(context.getTranslationUnitDecl()))
      return;
    llvm::outs() << llvm::json::Value(std::move(visitor.records)) << "\n";
  }
};

class Action : public clang::PluginASTAction {
public:
  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &, llvm::StringRef) override {
    return std::make_unique<Consumer>();
  }

  bool ParseArgs(const clang::CompilerInstance &compiler,
                 const std::vector<std::string> &arguments) override {
    if (!arguments.empty()) {
      auto id = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error,
          "string byte probe accepts no plugin arguments");
      compiler.getDiagnostics().Report(id);
      return false;
    }
    const std::string expected = "clang version " CLANG_VERSION_STRING;
    const std::string runtime = clang::getClangFullVersion();
    if (runtime != expected && !llvm::StringRef(runtime).starts_with(expected + " ")) {
      auto id = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error,
          "string byte probe header/runtime version mismatch");
      compiler.getDiagnostics().Report(id);
      return false;
    }
    return true;
  }

  ActionType getActionType() override { return ReplaceAction; }
};

clang::FrontendPluginRegistry::Add<Action>
    registration("lean-c-string-bytes", "emit parser-decoded StringLiteral bytes");

} // namespace
