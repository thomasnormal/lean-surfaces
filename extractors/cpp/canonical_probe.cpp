#include "clang/AST/ASTConsumer.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/Module.h"
#include "clang/Basic/Version.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/Support/FormatVariadic.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

#if CLANG_VERSION_MAJOR != 21 || CLANG_VERSION_MINOR != 1 || CLANG_VERSION_PATCHLEVEL != 8
#error "canonical probe supports only Clang 21.1.8 headers"
#endif

#if LLVM_VERSION_MAJOR != 21 || LLVM_VERSION_MINOR != 1 || LLVM_VERSION_PATCH != 8
#error "canonical probe supports only LLVM 21.1.8 headers"
#endif

namespace {

std::string pointerId(const void *pointer) {
  return "0x" + llvm::utohexstr(reinterpret_cast<uintptr_t>(pointer), true);
}

llvm::json::Value declarationId(const clang::Decl *declaration) {
  if (!declaration)
    return nullptr;
  return pointerId(declaration);
}

llvm::json::Value contextId(const clang::DeclContext *context) {
  if (!context)
    return nullptr;
  return declarationId(clang::Decl::castFromDeclContext(context));
}

std::string linkageName(clang::Linkage linkage) {
  switch (linkage) {
  case clang::Linkage::Invalid: return "Invalid";
  case clang::Linkage::None: return "None";
  case clang::Linkage::Internal: return "Internal";
  case clang::Linkage::UniqueExternal: return "UniqueExternal";
  case clang::Linkage::VisibleNone: return "VisibleNone";
  case clang::Linkage::Module: return "Module";
  case clang::Linkage::External: return "External";
  }
  return "unrepresented";
}

std::string languageLinkageName(clang::LanguageLinkage linkage) {
  switch (linkage) {
  case clang::CLanguageLinkage: return "C";
  case clang::CXXLanguageLinkage: return "C++";
  case clang::NoLanguageLinkage: return "None";
  }
  return "unrepresented";
}

void functionShapeEvidence(const clang::FunctionDecl *function,
                           llvm::json::Object &record) {
  record["function_has_skipped_body"] = function->hasSkippedBody();
  record["function_has_skipped_body_api"] = "FunctionDecl.hasSkippedBody";
  record["function_will_have_body"] = function->willHaveBody();
  record["function_will_have_body_api"] = "FunctionDecl.willHaveBody";
  record["function_has_defining_attr"] = function->hasDefiningAttr();
  record["function_has_defining_attr_api"] = "FunctionDecl.hasDefiningAttr";
  record["function_late_template_parsed"] = function->isLateTemplateParsed();
  record["function_late_template_parsed_api"] = "FunctionDecl.isLateTemplateParsed";
  record["function_explicitly_defaulted"] = function->isExplicitlyDefaulted();
  record["function_explicitly_defaulted_api"] = "FunctionDecl.isExplicitlyDefaulted";
  record["function_attribute_count"] =
      static_cast<int64_t>(function->hasAttrs() ? function->getAttrs().size() : 0);
  record["function_attribute_count_api"] = "Decl.hasAttrs/Decl.getAttrs.size";
  record["own_body_kind"] = nullptr;
  record["own_body_owner"] = nullptr;
  record["own_body_api"] = "FunctionDecl.getBody";
  if (function->doesThisDeclarationHaveABody() && !function->isLateTemplateParsed()) {
    const clang::FunctionDecl *owner = nullptr;
    const clang::Stmt *body = function->getBody(owner);
    record["own_body_owner"] = declarationId(owner);
    if (body)
      record["own_body_kind"] = body->getStmtClassName();
  }
}

void definitionEvidence(const clang::Decl *declaration,
                        llvm::json::Object &record) {
  record["definition"] = nullptr;
  record["definition_api"] = "not-queried";
  if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(declaration)) {
    record["definition"] = function->isThisDeclarationADefinition();
    record["definition_api"] = "FunctionDecl.isThisDeclarationADefinition";
    record["body_present"] = function->doesThisDeclarationHaveABody();
    record["defaulted"] = function->isDefaulted();
    record["deleted_as_written"] = function->isDeletedAsWritten();
    functionShapeEvidence(function, record);
    record["language_linkage"] = languageLinkageName(function->getLanguageLinkage());
  } else if (const auto *variable = llvm::dyn_cast<clang::VarDecl>(declaration)) {
    record["definition_api"] = "VarDecl.isThisDeclarationADefinition";
    record["variable_definition_kind"] =
        static_cast<int>(variable->isThisDeclarationADefinition());
    record["language_linkage"] = languageLinkageName(variable->getLanguageLinkage());
  } else if (const auto *tag = llvm::dyn_cast<clang::TagDecl>(declaration)) {
    record["definition"] = tag->isThisDeclarationADefinition();
    record["definition_api"] = "TagDecl.isThisDeclarationADefinition";
  }
}

void templateEvidence(const clang::Decl *declaration, llvm::json::Object &record) {
  if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(declaration)) {
    record["function_templated_kind"] = static_cast<int>(function->getTemplatedKind());
    record["function_templated_kind_api"] = "FunctionDecl.getTemplatedKind";
    record["template_specialization_kind"] =
        static_cast<int>(function->getTemplateSpecializationKind());
    record["template_specialization_kind_api"] = "FunctionDecl.getTemplateSpecializationKind";
  } else if (const auto *variable = llvm::dyn_cast<clang::VarDecl>(declaration)) {
    record["described_template"] = declarationId(variable->getDescribedVarTemplate());
    record["described_template_api"] = "VarDecl.getDescribedVarTemplate";
    record["template_specialization_kind"] =
        static_cast<int>(variable->getTemplateSpecializationKind());
    record["template_specialization_kind_api"] = "VarDecl.getTemplateSpecializationKind";
  } else if (const auto *classDeclaration = llvm::dyn_cast<clang::CXXRecordDecl>(declaration)) {
    record["described_template"] = declarationId(classDeclaration->getDescribedClassTemplate());
    record["described_template_api"] = "CXXRecordDecl.getDescribedClassTemplate";
    record["template_specialization_kind"] =
        static_cast<int>(classDeclaration->getTemplateSpecializationKind());
    record["template_specialization_kind_api"] = "CXXRecordDecl.getTemplateSpecializationKind";
  } else if (const auto *enumeration = llvm::dyn_cast<clang::EnumDecl>(declaration)) {
    record["template_specialization_kind"] =
        static_cast<int>(enumeration->getTemplateSpecializationKind());
    record["template_specialization_kind_api"] = "EnumDecl.getTemplateSpecializationKind";
  }
}

void classEvidence(const clang::Decl *declaration, llvm::json::Object &record) {
  const auto *classDeclaration = llvm::dyn_cast<clang::CXXRecordDecl>(declaration);
  if (!classDeclaration)
    return;
  record["injected_class_name"] = classDeclaration->isInjectedClassName();
  record["represented_class"] = nullptr;
  if (classDeclaration->isInjectedClassName() && classDeclaration->getTypeForDecl())
    record["represented_class"] =
        declarationId(classDeclaration->getTypeForDecl()->getAsCXXRecordDecl());
}

class DeclarationVisitor : public clang::RecursiveASTVisitor<DeclarationVisitor> {
public:
  llvm::json::Array records;

  bool shouldVisitImplicitCode() const { return true; }
  bool shouldVisitTemplateInstantiations() const { return true; }

  bool VisitDecl(clang::Decl *declaration) {
    llvm::json::Object record{
        {"id", pointerId(declaration)},
        {"kind", std::string(declaration->getDeclKindName()) + "Decl"},
        {"canonical", declarationId(declaration->getCanonicalDecl())},
        {"previous", declarationId(declaration->getPreviousDecl())},
        {"semantic_context", contextId(declaration->getDeclContext())},
        {"lexical_context", contextId(declaration->getLexicalDeclContext())},
        {"implicit", declaration->isImplicit()},
        {"dependent_context", declaration->getDeclContext() &&
             declaration->getDeclContext()->isDependentContext()},
        {"owning_module", nullptr}};
    if (const auto *module = declaration->getOwningModule())
      record["owning_module"] = module->getFullModuleName();
    if (const auto *named = llvm::dyn_cast<clang::NamedDecl>(declaration)) {
      record["name"] = named->getNameAsString();
      record["linkage_internal"] = linkageName(named->getLinkageInternal());
      record["linkage_formal"] = linkageName(named->getFormalLinkage());
    }
    if (const auto *nameSpace = llvm::dyn_cast<clang::NamespaceDecl>(declaration)) {
      record["original_namespace"] = declarationId(nameSpace->getCanonicalDecl());
      record["inline_namespace"] = nameSpace->isInline();
      record["anonymous_namespace"] = nameSpace->isAnonymousNamespace();
    }
    definitionEvidence(declaration, record);
    templateEvidence(declaration, record);
    classEvidence(declaration, record);
    records.push_back(std::move(record));
    return true;
  }
};

class ProbeConsumer : public clang::ASTConsumer {
  clang::CompilerInstance &compiler;

public:
  explicit ProbeConsumer(clang::CompilerInstance &instance) : compiler(instance) {}

  void HandleTranslationUnit(clang::ASTContext &context) override {
    if (compiler.getDiagnostics().hasErrorOccurred())
      return;
    DeclarationVisitor visitor;
    if (!visitor.TraverseDecl(context.getTranslationUnitDecl())) {
      unsigned diagnostic = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error, "canonical probe traversal failed");
      compiler.getDiagnostics().Report(diagnostic);
      return;
    }
    llvm::json::Object metadata{
        {"schema_version", "cpp-canonical-probe-0.3"},
        {"compiled_frontend", CLANG_VERSION_STRING},
        {"runtime_frontend", clang::getClangFullVersion()},
        {"llvm_headers", LLVM_VERSION_STRING},
        {"declarations", std::move(visitor.records)}};
    llvm::outs() << "{\"metadata\":" << llvm::formatv("{0}", llvm::json::Value(std::move(metadata)))
                 << ",\"ast\":";
    context.getTranslationUnitDecl()->dump(llvm::outs(), false, clang::ADOF_JSON);
    llvm::outs() << "}\n";
  }
};

class ProbeAction : public clang::PluginASTAction {
public:
  std::unique_ptr<clang::ASTConsumer>
  CreateASTConsumer(clang::CompilerInstance &compiler, llvm::StringRef) override {
    return std::make_unique<ProbeConsumer>(compiler);
  }

  bool ParseArgs(const clang::CompilerInstance &compiler,
                 const std::vector<std::string> &arguments) override {
    if (!arguments.empty()) {
      unsigned diagnostic = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error, "canonical probe accepts no plugin arguments");
      compiler.getDiagnostics().Report(diagnostic);
      return false;
    }
    const std::string expected = "clang version " CLANG_VERSION_STRING;
    const std::string runtime = clang::getClangFullVersion();
    if (runtime != expected && !llvm::StringRef(runtime).starts_with(expected + " ")) {
      unsigned diagnostic = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error, "canonical probe header/runtime version mismatch");
      compiler.getDiagnostics().Report(diagnostic);
      return false;
    }
    return true;
  }

  ActionType getActionType() override { return ReplaceAction; }
};

clang::FrontendPluginRegistry::Add<ProbeAction>
    registration("leancpp-canonical-probe", "same-process C++ declaration metadata probe");

}
