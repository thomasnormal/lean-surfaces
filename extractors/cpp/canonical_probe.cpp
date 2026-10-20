#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
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
#include "dump_reachability.h"

#include <optional>
#include <unordered_set>
#include <vector>

#if CLANG_VERSION_MAJOR != 21 || CLANG_VERSION_MINOR != 1 || CLANG_VERSION_PATCHLEVEL != 8
#error "canonical probe supports only Clang 21.1.8 headers"
#endif

#if LLVM_VERSION_MAJOR != 21 || LLVM_VERSION_MINOR != 1 || LLVM_VERSION_PATCH != 8
#error "canonical probe supports only LLVM 21.1.8 headers"
#endif

namespace {

class ObservedDumpStream : public llvm::raw_ostream {
  llvm::raw_ostream &destination;
  leancpp::DumpReachability &reachability;
  uint64_t position = 0;

  void write_impl(const char *data, size_t size) override {
    destination.write(data, size);
    reachability.consume(std::string_view(data, size));
    position += size;
  }

  uint64_t current_pos() const override { return position; }

public:
  ObservedDumpStream(llvm::raw_ostream &destination,
                     leancpp::DumpReachability &reachability)
      : llvm::raw_ostream(true), destination(destination), reachability(reachability) {}
};

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

std::string storageClassName(clang::StorageClass storage) {
  switch (storage) {
  case clang::SC_None: return "none";
  case clang::SC_Extern: return "extern";
  case clang::SC_Static: return "static";
  case clang::SC_PrivateExtern: return "private-extern";
  case clang::SC_Auto: return "auto";
  case clang::SC_Register: return "register";
  }
  return "unrepresented";
}

std::string storageDurationName(clang::StorageDuration duration) {
  switch (duration) {
  case clang::SD_FullExpression: return "full-expression";
  case clang::SD_Automatic: return "automatic";
  case clang::SD_Thread: return "thread";
  case clang::SD_Static: return "static";
  case clang::SD_Dynamic: return "dynamic";
  }
  return "unrepresented";
}

std::string tlsKindName(clang::VarDecl::TLSKind kind) {
  switch (kind) {
  case clang::VarDecl::TLS_None: return "none";
  case clang::VarDecl::TLS_Static: return "static";
  case clang::VarDecl::TLS_Dynamic: return "dynamic";
  }
  return "unrepresented";
}

std::string initializationStyleName(clang::VarDecl::InitializationStyle style) {
  switch (style) {
  case clang::VarDecl::CInit: return "c";
  case clang::VarDecl::CallInit: return "call";
  case clang::VarDecl::ListInit: return "list";
  case clang::VarDecl::ParenListInit: return "paren-list";
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

std::optional<std::string> builtinTypeName(const clang::BuiltinType *builtin) {
  switch (builtin->getKind()) {
  case clang::BuiltinType::Bool: return "bool";
  case clang::BuiltinType::Char_S:
  case clang::BuiltinType::Char_U: return "char";
  case clang::BuiltinType::SChar: return "signed char";
  case clang::BuiltinType::UChar: return "unsigned char";
  case clang::BuiltinType::Short: return "short";
  case clang::BuiltinType::UShort: return "unsigned short";
  case clang::BuiltinType::Int: return "int";
  case clang::BuiltinType::UInt: return "unsigned int";
  case clang::BuiltinType::Long: return "long";
  case clang::BuiltinType::ULong: return "unsigned long";
  case clang::BuiltinType::LongLong: return "long long";
  case clang::BuiltinType::ULongLong: return "unsigned long long";
  default: return std::nullopt;
  }
}

std::optional<llvm::json::Value> structuredType(
    clang::QualType qualified, const clang::ASTContext &context, unsigned depth);

std::optional<llvm::json::Value>
structuredUnqualifiedType(clang::QualType unqualified,
                          const clang::ASTContext &context, unsigned depth) {
  const clang::Type *type = unqualified.getTypePtrOrNull();
  if (!type)
    return std::nullopt;
  if (const auto *builtin = llvm::dyn_cast<clang::BuiltinType>(type)) {
    const auto name = builtinTypeName(builtin);
    if (!name)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "builtin";
    result["name"] = *name;
    return llvm::json::Value(std::move(result));
  }
  if (const auto *pointer = llvm::dyn_cast<clang::PointerType>(type)) {
    auto pointee = structuredType(pointer->getPointeeType(), context, depth + 1);
    if (!pointee)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "pointer";
    result["pointee"] = std::move(*pointee);
    return llvm::json::Value(std::move(result));
  }
  if (const auto *reference = llvm::dyn_cast<clang::LValueReferenceType>(type)) {
    auto referent = structuredType(reference->getPointeeType(), context, depth + 1);
    if (!referent)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "lvalue-reference";
    result["referent"] = std::move(*referent);
    return llvm::json::Value(std::move(result));
  }
  if (const auto *reference = llvm::dyn_cast<clang::RValueReferenceType>(type)) {
    auto referent = structuredType(reference->getPointeeType(), context, depth + 1);
    if (!referent)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "rvalue-reference";
    result["referent"] = std::move(*referent);
    return llvm::json::Value(std::move(result));
  }
  if (const auto *function = llvm::dyn_cast<clang::FunctionProtoType>(type)) {
    if (function->hasExceptionSpec() || !function->getMethodQuals().empty() ||
        function->getRefQualifier() != clang::RQ_None ||
        function->getExtInfo() != clang::FunctionType::ExtInfo() ||
        function->hasExtParameterInfos() || function->hasCFIUncheckedCallee() ||
        function->getAArch64SMEAttributes() != 0 ||
        function->getNumFunctionEffects() != 0)
      return std::nullopt;
    auto resultType = structuredType(function->getReturnType(), context, depth + 1);
    if (!resultType)
      return std::nullopt;
    llvm::json::Array parameters;
    for (const clang::QualType parameter : function->param_types()) {
      auto parameterType = structuredType(parameter, context, depth + 1);
      if (!parameterType)
        return std::nullopt;
      parameters.push_back(std::move(*parameterType));
    }
    llvm::json::Object result;
    result["kind"] = "function";
    result["result"] = std::move(*resultType);
    result["parameters"] = std::move(parameters);
    result["variadic"] = function->isVariadic();
    return llvm::json::Value(std::move(result));
  }
  if (const auto *record = llvm::dyn_cast<clang::RecordType>(type)) {
    const clang::RecordDecl *declaration = record->getDecl();
    if (!declaration)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "record";
    result["declaration"] = declarationId(declaration->getCanonicalDecl());
    return llvm::json::Value(std::move(result));
  }
  if (const auto *enumeration = llvm::dyn_cast<clang::EnumType>(type)) {
    const clang::EnumDecl *declaration = enumeration->getDecl();
    if (!declaration)
      return std::nullopt;
    llvm::json::Object result;
    result["kind"] = "enumeration";
    result["declaration"] = declarationId(declaration->getCanonicalDecl());
    return llvm::json::Value(std::move(result));
  }
  return std::nullopt;
}

std::optional<llvm::json::Value> structuredType(
    clang::QualType qualified, const clang::ASTContext &context, unsigned depth) {
  if (qualified.isNull() || depth >= 128)
    return std::nullopt;
  const clang::QualType desugared = qualified.getDesugaredType(context);
  const clang::Qualifiers qualifiers = desugared.getLocalQualifiers();
  if (qualifiers.hasRestrict() || qualifiers.hasNonFastQualifiers())
    return std::nullopt;
  const bool isConst = qualifiers.hasConst();
  const bool isVolatile = qualifiers.hasVolatile();
  auto body = structuredUnqualifiedType(desugared.getLocalUnqualifiedType(), context, depth);
  if (!body)
    return std::nullopt;
  if (!isConst && !isVolatile)
    return body;
  llvm::json::Object result;
  result["kind"] = "qualified";
  result["const"] = isConst;
  result["volatile"] = isVolatile;
  result["base"] = std::move(*body);
  return llvm::json::Value(std::move(result));
}

std::optional<clang::QualType> declarationType(const clang::Decl *declaration) {
  if (const auto *function = llvm::dyn_cast<clang::FunctionDecl>(declaration))
    return function->getType();
  if (const auto *value = llvm::dyn_cast<clang::ValueDecl>(declaration))
    return value->getType();
  return std::nullopt;
}

bool structuredReferencesWitnessed(
    const llvm::json::Value &value,
    const std::unordered_set<std::string> &declarationIds) {
  if (const auto *object = value.getAsObject()) {
    if (const auto kind = object->getString("kind"); kind &&
        (*kind == "record" || *kind == "enumeration")) {
      const auto declaration = object->getString("declaration");
      if (!declaration || !declarationIds.count(declaration->str()))
        return false;
    }
    for (const auto &entry : *object)
      if (!structuredReferencesWitnessed(entry.second, declarationIds))
        return false;
    return true;
  }
  if (const auto *array = value.getAsArray()) {
    for (const auto &entry : *array)
      if (!structuredReferencesWitnessed(entry, declarationIds))
        return false;
  }
  return true;
}

class DeclarationVisitor : public clang::RecursiveASTVisitor<DeclarationVisitor> {
public:
  llvm::json::Array records;
  llvm::json::Array typeEvidence;
  llvm::json::Array typeRefusals;
  llvm::json::Array expressionEvidence;
  llvm::json::Array expressionRefusals;
  llvm::json::Array expressionTypes;
  llvm::json::Array expressionTypeRefusals;
  llvm::json::Array variableEvidence;
  llvm::json::Array variableRefusals;
  std::vector<const clang::Decl *> typedDeclarations;
  std::vector<const clang::BinaryOperator *> binaryExpressions;
  std::vector<const clang::Expr *> typedExpressions;
  std::unordered_set<std::string> declarationIds;
  const clang::ASTContext *astContext = nullptr;

  bool shouldVisitImplicitCode() const { return true; }
  bool shouldVisitTemplateInstantiations() const { return true; }

  bool VisitDecl(clang::Decl *declaration) {
    declarationIds.insert(pointerId(declaration));
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
    if (declarationType(declaration))
      typedDeclarations.push_back(declaration);
    return true;
  }

  bool VisitBinaryOperator(clang::BinaryOperator *expression) {
    binaryExpressions.push_back(expression);
    return true;
  }

  bool VisitExpr(clang::Expr *expression) {
    typedExpressions.push_back(expression);
    return true;
  }

  void buildExpressionTypes(const std::unordered_set<std::string> &visibleNodes) {
    for (const auto *expression : typedExpressions) {
      llvm::json::Object row{{"occurrence", pointerId(expression)},
                             {"kind", expression->getStmtClassName()}};
      auto type = structuredType(expression->getType(), *astContext, 0);
      const bool visible = visibleNodes.count(pointerId(expression));
      const bool supported = type && structuredReferencesWitnessed(*type, declarationIds);
      if (type)
        row["type"] = std::move(*type);
      if (visible && supported) {
        expressionTypes.push_back(std::move(row));
      } else {
        row["dump_visible"] = visible;
        row["projection_supported"] = supported;
        row["reason"] = !visible ? "expression is outside JSON AST inner tree"
                                  : "unrepresented expression type";
        expressionTypeRefusals.push_back(std::move(row));
      }
    }
  }

  void emitBinaryExpression(const clang::BinaryOperator *expression,
                            const std::unordered_set<std::string> &visibleExpressions) {
    llvm::json::Object row{
        {"expression_api", "Clang::BinaryOperator typed operand projection v2"},
        {"occurrence", pointerId(expression)},
        {"kind", "BinaryOperator"},
        {"operator", expression->getOpcodeStr().str()}};
    auto result = structuredType(expression->getType(), *astContext, 0);
    llvm::json::Array operands;
    bool supported = result.has_value();
    for (const clang::Expr *operand : {expression->getLHS(), expression->getRHS()}) {
      llvm::json::Object operandRow{
          {"occurrence", pointerId(operand)},
          {"kind", operand->getStmtClassName()}};
      const clang::Expr *source = operand->IgnoreParenImpCasts();
      auto sourceType = structuredType(source->getType(), *astContext, 0);
      auto operandType = structuredType(operand->getType(), *astContext, 0);
      if (sourceType && structuredReferencesWitnessed(*sourceType, declarationIds))
        operandRow["source"] = std::move(*sourceType);
      else
        supported = false;
      if (operandType && structuredReferencesWitnessed(*operandType, declarationIds))
        operandRow["type"] = std::move(*operandType);
      else
        supported = false;
      operands.push_back(std::move(operandRow));
    }
    supported = result && supported && structuredReferencesWitnessed(*result, declarationIds);
    if (result)
      row["result"] = std::move(*result);
    row["operands"] = std::move(operands);
    if (!visibleExpressions.count(pointerId(expression))) {
      row["dump_visible"] = false;
      row["projection_supported"] = supported;
      row["reason"] = "expression occurrence is outside JSON AST dump";
      expressionRefusals.push_back(std::move(row));
      return;
    }
    if (!supported) {
      row["reason"] = "unrepresented result or operand type";
      expressionRefusals.push_back(std::move(row));
      return;
    }
    expressionEvidence.push_back(std::move(row));
  }

  void buildTypeEvidence(const clang::ASTContext &context) {
    for (const clang::Decl *declaration : typedDeclarations) {
      const auto type = declarationType(declaration);
      if (!type)
        continue;
      auto structured = structuredType(*type, context, 0);
      llvm::json::Object row;
      row["type_api"] = "Clang::QualType structured type projection v1";
      row["occurrence"] = pointerId(declaration);
      row["canonical"] = declarationId(declaration->getCanonicalDecl());
      if (!structured || !structuredReferencesWitnessed(*structured, declarationIds)) {
        row["reason"] = structured ? "unwitnessed record or enumeration declaration"
                                   : "unrepresented type family, qualifiers, function properties or depth";
        typeRefusals.push_back(std::move(row));
        continue;
      }
      row["type"] = std::move(*structured);
      typeEvidence.push_back(std::move(row));
    }
  }

  void buildExpressionEvidence(const std::unordered_set<std::string> &visibleExpressions) {
    for (const clang::BinaryOperator *expression : binaryExpressions)
      emitBinaryExpression(expression, visibleExpressions);
  }

  void initializerTypes(const clang::Stmt *statement,
                        const std::unordered_set<std::string> &visibleNodes,
                        llvm::json::Array &rows) {
    if (!statement || !visibleNodes.count(pointerId(statement)))
      return;
    if (const auto *expression = llvm::dyn_cast<clang::Expr>(statement)) {
      auto type = structuredType(expression->getType(), *astContext, 0);
      if (type && structuredReferencesWitnessed(*type, declarationIds))
        rows.push_back(llvm::json::Object{
            {"occurrence", pointerId(expression)},
            {"kind", expression->getStmtClassName()}, {"type", std::move(*type)}});
    }
    for (const auto *child : statement->children())
      initializerTypes(child, visibleNodes, rows);
  }

  void buildVariableEvidence(const std::unordered_set<std::string> &visibleNodes) {
    for (const clang::Decl *declaration : typedDeclarations) {
      const auto *variable = llvm::dyn_cast<clang::VarDecl>(declaration);
      if (!variable)
        continue;
      llvm::json::Object row{
          {"variable_api", "Clang::VarDecl storage and initializer projection v1"},
          {"occurrence", pointerId(variable)},
          {"canonical", declarationId(variable->getCanonicalDecl())},
          {"kind", std::string(variable->getDeclKindName()) + "Decl"},
          {"local", variable->isLocalVarDecl()},
          {"local_or_parameter", variable->isLocalVarDeclOrParm()},
          {"storage_class", storageClassName(variable->getStorageClass())},
          {"storage_duration", storageDurationName(variable->getStorageDuration())},
          {"tls", tlsKindName(variable->getTLSKind())},
          {"init_style", initializationStyleName(variable->getInitStyle())},
          {"has_initializer", variable->hasInit()},
          {"initializer", nullptr},
          {"constexpr", variable->isConstexpr()},
          {"attribute_count", static_cast<int64_t>(
              variable->hasAttrs() ? variable->getAttrs().size() : 0)}};
      if (const auto *parameter = llvm::dyn_cast<clang::ParmVarDecl>(variable)) {
        if (parameter->hasUnparsedDefaultArg() || parameter->hasUninstantiatedDefaultArg()) {
          row["dump_visible"] = bool(visibleNodes.count(pointerId(variable)));
          row["projection_supported"] = false;
          row["reason"] = "parameter default argument is unparsed or uninstantiated";
          variableRefusals.push_back(std::move(row));
          continue;
        }
      }
      const clang::Expr *initializer = variable->getInit();
      bool visible = visibleNodes.count(pointerId(variable));
      bool supported = variable->hasInit() == (initializer != nullptr);
      auto type = structuredType(variable->getType(), *astContext, 0);
      supported = supported && type && structuredReferencesWitnessed(*type, declarationIds);
      if (initializer) {
        llvm::json::Object init{
            {"occurrence", pointerId(initializer)},
            {"kind", initializer->getStmtClassName()}};
        auto sourceType = structuredType(initializer->IgnoreParenImpCasts()->getType(), *astContext, 0);
        auto convertedType = structuredType(initializer->getType(), *astContext, 0);
        visible = visible && visibleNodes.count(pointerId(initializer));
        if (sourceType && structuredReferencesWitnessed(*sourceType, declarationIds))
          init["source"] = std::move(*sourceType);
        else
          supported = false;
        if (convertedType && structuredReferencesWitnessed(*convertedType, declarationIds))
          init["type"] = std::move(*convertedType);
        else
          supported = false;
        llvm::json::Array types;
        initializerTypes(initializer, visibleNodes, types);
        init["expression_types_api"] = "Clang::Expr initializer type projection v1";
        init["expression_types"] = std::move(types);
        row["initializer"] = std::move(init);
      }
      if (!visible || !supported) {
        row["dump_visible"] = visible;
        row["projection_supported"] = supported;
        row["reason"] = !visible ? "variable or initializer is outside JSON AST inner tree"
                                 : "unrepresented variable or initializer type/shape";
        variableRefusals.push_back(std::move(row));
      } else {
        variableEvidence.push_back(std::move(row));
      }
    }
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
    visitor.astContext = &context;
    if (!visitor.TraverseDecl(context.getTranslationUnitDecl())) {
      unsigned diagnostic = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error, "canonical probe traversal failed");
      compiler.getDiagnostics().Report(diagnostic);
      return;
    }
    visitor.buildTypeEvidence(context);
    llvm::outs() << "{\"ast\":";
    leancpp::DumpReachability reachability;
    ObservedDumpStream dumpStream(llvm::outs(), reachability);
    context.getTranslationUnitDecl()->dump(dumpStream, false, clang::ADOF_JSON);
    dumpStream.flush();
    if (!reachability.complete()) {
      unsigned diagnostic = compiler.getDiagnostics().getCustomDiagID(
          clang::DiagnosticsEngine::Error, "canonical probe dump observation failed");
      compiler.getDiagnostics().Report(diagnostic);
      return;
    }
    visitor.buildExpressionEvidence(reachability.expressionIds());
    visitor.buildExpressionTypes(reachability.astNodeIds());
    visitor.buildVariableEvidence(reachability.astNodeIds());
    llvm::json::Object metadata{
        {"schema_version", "cpp-canonical-probe-0.3"},
        {"compiled_frontend", CLANG_VERSION_STRING},
        {"runtime_frontend", clang::getClangFullVersion()},
        {"llvm_headers", LLVM_VERSION_STRING},
        {"type_evidence_api", "Clang::QualType structured type projection v1"},
        {"type_evidence", std::move(visitor.typeEvidence)},
        {"type_refusals", std::move(visitor.typeRefusals)},
        {"expression_evidence_api", "Clang::BinaryOperator typed operand projection v2"},
        {"expression_evidence", std::move(visitor.expressionEvidence)},
        {"expression_refusals", std::move(visitor.expressionRefusals)},
        {"expression_types_api", "Clang::Expr type projection v1"},
        {"expression_types", std::move(visitor.expressionTypes)},
        {"expression_type_refusals", std::move(visitor.expressionTypeRefusals)},
        {"variable_evidence_api", "Clang::VarDecl storage and initializer projection v1"},
        {"variable_evidence", std::move(visitor.variableEvidence)},
        {"variable_refusals", std::move(visitor.variableRefusals)},
        {"declarations", std::move(visitor.records)}};
    llvm::outs() << ",\"metadata\":" << llvm::formatv("{0}", llvm::json::Value(std::move(metadata)))
                 << "}\n";
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
