// Parser-native record-layout observations for the C extractor.
//
// ASTRecordLayout is Clang's own target/profile answer.  This probe reports
// it verbatim and joins records by their source span, never by a type spelling
// or a fabricated address.  It is an observation instrument; it does not
// make aggregate semantics live in Lean.
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/RecordLayout.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <vector>

#if CLANG_VERSION_MAJOR != 21 || CLANG_VERSION_MINOR != 1 || CLANG_VERSION_PATCHLEVEL != 8
#error "record layout probe supports only Clang 21.1.8"
#endif
#if LLVM_VERSION_MAJOR != 21 || LLVM_VERSION_MINOR != 1 || LLVM_VERSION_PATCH != 8
#error "record layout probe supports only LLVM 21.1.8"
#endif

namespace {
class Visitor : public clang::RecursiveASTVisitor<Visitor> {
public:
  llvm::json::Array records;
  const clang::ASTContext *context = nullptr;

  bool VisitRecordDecl(clang::RecordDecl *record) {
    if (!record->isCompleteDefinition()) return true;
    const auto &sources = context->getSourceManager();
    const auto loc = sources.getExpansionLoc(record->getBeginLoc());
    if (!sources.isWrittenInMainFile(loc)) return true;
    const auto end_loc = clang::Lexer::getLocForEndOfToken(
        sources.getExpansionLoc(record->getEndLoc()), 0, sources,
        clang::LangOptions());
    const auto begin = sources.getFileOffset(loc);
    const auto finish = end_loc.isValid() ? sources.getFileOffset(end_loc) : begin;
    const auto &layout = context->getASTRecordLayout(record);
    llvm::json::Array fields;
    unsigned index = 0;
    for (const clang::FieldDecl *field : record->fields()) {
      llvm::json::Object item{
          {"name", field->getNameAsString()},
          {"offset_bits", static_cast<int64_t>(layout.getFieldOffset(index))},
          {"bitfield", field->isBitField()},
          {"incomplete_array", field->getType()->isIncompleteArrayType()}};
      if (field->isBitField()) {
        if (const auto *width = field->getBitWidth()) {
          const llvm::APSInt value = width->EvaluateKnownConstInt(*context);
          item["width_bits"] = static_cast<int64_t>(value.getZExtValue());
        }
      }
      fields.push_back(std::move(item));
      ++index;
    }
    llvm::json::Object item{
        {"kind", "RecordLayout"},
        {"offset", static_cast<int64_t>(begin)},
        {"token_length", static_cast<int64_t>(finish - begin)},
        {"name", record->getNameAsString()},
        {"tag_kind", record->isUnion() ? "union" : "struct"},
        {"size_bytes", static_cast<int64_t>(layout.getSize().getQuantity())},
        {"alignment_bytes", static_cast<int64_t>(layout.getAlignment().getQuantity())},
        {"fields", std::move(fields)}};
    records.push_back(std::move(item));
    return true;
  }

  bool VisitEnumConstantDecl(clang::EnumConstantDecl *constant) {
    const auto &sources = context->getSourceManager();
    const auto loc = sources.getExpansionLoc(constant->getBeginLoc());
    if (!sources.isWrittenInMainFile(loc)) return true;
    records.push_back(llvm::json::Object{
        {"kind", "EnumValue"},
        {"offset", static_cast<int64_t>(sources.getFileOffset(loc))},
        {"value", static_cast<int64_t>(constant->getInitVal().getSExtValue())}});
    return true;
  }
};

class Consumer : public clang::ASTConsumer {
public:
  void HandleTranslationUnit(clang::ASTContext &context) override {
    Visitor visitor;
    visitor.context = &context;
    if (!visitor.TraverseDecl(context.getTranslationUnitDecl())) return;
    llvm::outs() << llvm::json::Value(std::move(visitor.records)) << "\n";
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
          "record layout probe accepts no plugin arguments");
      compiler.getDiagnostics().Report(id);
      return false;
    }
    const std::string expected = "clang version " CLANG_VERSION_STRING;
    const std::string runtime = clang::getClangFullVersion();
    if (runtime != expected &&
        !llvm::StringRef(runtime).starts_with(expected + " ")) {
      auto id = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error,
          "record layout probe header/runtime version mismatch");
      compiler.getDiagnostics().Report(id);
      return false;
    }
    return true;
  }
  ActionType getActionType() override { return ReplaceAction; }
};

clang::FrontendPluginRegistry::Add<Action> registration(
    "lean-c-record-layout", "emit parser-native record layouts");
} // namespace
