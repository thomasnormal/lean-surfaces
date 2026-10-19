import LeanModels.Cpp.VariableEvidence

namespace LeanModels.Cpp.VariableEvidenceTests

private def text := Raw.string
private def object := Raw.object
private def handle (value : String) : FrontendHandle := {value}
private def api := "Clang::VarDecl storage and initializer projection v1"
private def intType : Raw := object [("kind", text "builtin"), ("name", text "int")]
private def typeRow : Raw := object [
  ("type_api", text "Clang::QualType structured type projection v1"),
  ("occurrence", text "0x1"), ("canonical", text "0x1"), ("type", intType)]
private def declaration : DeclarationEvidenceRow := {
  ordinal := 0, id := handle "0x1", kind := "VarDecl", canonical := handle "0x1",
  previous := none, semanticContext := none, lexicalContext := none, implicit := false,
  dependentContext := false, owningModule := none, functionShape := none, raw := object []}
private def initializer : Raw := object [
  ("occurrence", text "0x2"), ("kind", text "IntegerLiteral"),
  ("source", intType), ("type", intType)]
private def row : Raw := object [
  ("variable_api", text api), ("occurrence", text "0x1"), ("canonical", text "0x1"),
  ("kind", text "VarDecl"), ("local", .bool true), ("local_or_parameter", .bool true),
  ("storage_class", text "none"), ("storage_duration", text "automatic"),
  ("tls", text "none"), ("init_style", text "c"), ("has_initializer", .bool true),
  ("initializer", initializer), ("constexpr", .bool false), ("attribute_count", .number "0")]
private def valueNode : Raw := object [("id", text "0x2"), ("kind", text "IntegerLiteral")]
private def node : Raw := object [
  ("id", text "0x1"), ("kind", text "VarDecl"), ("init", text "c"),
  ("inner", .array [valueNode])]
private def set (raw : Raw) (field : String) (value : Raw) : Raw :=
  match raw with
  | .object fields => .object ((field, value) :: fields.filter (·.1 != field))
  | _ => raw
private def erase (raw : Raw) (field : String) : Raw :=
  match raw with
  | .object fields => .object (fields.filter (·.1 != field))
  | _ => raw
private def probe (nodes : List Raw := [node]) (rows : List Raw := [row]) : DeclarationProbe := {
  ast := object [("kind", text "TranslationUnitDecl"), ("id", text "0x0"),
    ("inner", .array nodes)]
  metadata := object [("type_evidence_api", text "Clang::QualType structured type projection v1"),
    ("type_evidence", .array [typeRow]), ("variable_evidence_api", text api),
    ("variable_evidence", .array rows)]
  declarations := [declaration]}
private def accepts (probe : DeclarationProbe) : Bool :=
  match parseValidatedVariableEvidence probe with
  | .ok _ => true
  | .error _ => false
private def parses (row : Raw) : Bool :=
  match parseVariableEvidenceRows (.array [row]) with
  | .ok _ => true
  | .error _ => false

#guard accepts (probe)
#guard accepts (probe [node] [row, row])
#guard !accepts (probe [node] [row, set row "local" (.bool false)])
#guard !accepts {probe with metadata := erase (probe).metadata "variable_evidence_api"}
#guard !accepts {probe with metadata := set (probe).metadata "variable_evidence_api" (text "v2")}
#guard !parses (erase row "has_initializer")
#guard !parses (erase row "initializer")
#guard !parses (set row "has_initializer" (.bool false))
#guard !parses (set row "storage_duration" (text "dynamic"))
#guard !parses (set row "storage_class" (text "mutable"))
#guard !parses (set row "tls" (text "guess"))
#guard !parses (set row "init_style" (text "direct"))
#guard !parses (set row "kind" (text "FieldDecl"))
#guard !accepts {probe with declarations := [{declaration with canonical := handle "0x9"}]}
#guard !accepts {probe with declarations := [{declaration with kind := "ParmVarDecl"}]}
#guard !accepts {probe with metadata := set (probe).metadata "type_evidence" (.array [])}
#guard !accepts (probe [set node "kind" (text "ParmVarDecl")])
#guard !accepts (probe [object [("referencedDecl", node)]])
#guard !accepts (probe [object [("type", node)]])
#guard !accepts (probe [.array [node]])
#guard !accepts (probe [node, set node "init" (text "list")])
#guard !accepts (probe [set node "init" (text "list")])
#guard !accepts (probe [set node "inner" (.array [])])
#guard !accepts (probe [set node "inner" (.array [valueNode, valueNode])])
#guard !accepts (probe [set node "inner" (.array [set valueNode "id" (text "0x3")])])
#guard !accepts (probe [set node "inner" (.array [set valueNode "kind" (text "DeclRefExpr")])])
#guard !accepts (probe [set node "storageClass" (text "static")])
#guard !accepts (probe [set node "tls" (text "dynamic")])
#guard !accepts (probe [set node "constexpr" (.bool true)])
#guard !accepts (probe [set node "constexpr" (text "true")])
#guard !accepts (probe [set node "inner" (.array [valueNode,
  object [("kind", text "UnusedAttr")]])])
#guard accepts (probe [set node "inner" (.array [valueNode,
  object [("kind", text "UnusedAttr")]])] [set row "attribute_count" (.number "1")])
#guard accepts (probe [set node "constexpr" (.bool true)] [set row "constexpr" (.bool true)])
#guard !accepts (probe [node] [set row "initializer" (set initializer "source"
  (object [("kind", text "record"), ("declaration", text "0x9")]))])
#guard !accepts (probe [node] [set row "initializer" (set initializer "type"
  (object [("kind", text "record"), ("declaration", text "0x9")]))])
#guard !accepts (probe [node] [set row "local_or_parameter" (.bool false)])
#guard !accepts (probe [node] [set row "storage_duration" (text "static")])
#guard accepts (probe [erase (erase node "init") "inner"]
  [set (set row "initializer" .null) "has_initializer" (.bool false)])
#guard !accepts (probe [node]
  [set (set row "initializer" .null) "has_initializer" (.bool false)])
#guard !accepts (probe [erase (erase node "init") "inner"])
#guard accepts (probe [set node "init" (text "list")] [set row "init_style" (text "list")])
#guard accepts (probe [set node "init" (text "call")] [set row "init_style" (text "call")])
#guard accepts (probe [set node "init" (text "paren-list")]
  [set row "init_style" (text "paren-list")])

#guard accepts (probe [set node "inner" (.array [
  object [("kind", text "TemplateArgument")], valueNode])])
#guard accepts (probe [set node "inner" (.array [valueNode,
  object [("kind", text "BindingDecl")]])])
#guard !accepts (probe [set node "inner" (.array [valueNode,
  object [("kind", text "DeclRefExpr")]])])

end LeanModels.Cpp.VariableEvidenceTests
