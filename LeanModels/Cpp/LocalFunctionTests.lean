import LeanModels.Cpp.LocalFunction
import LeanModels.Cpp.EvidenceTests

namespace LeanModels.Cpp.LocalFunctionTests

open EvidenceTests

def fields (raw : Raw) (updates : List (String × Raw)) : Raw :=
  match raw with
  | .object entries => .object ((entries.filter fun entry =>
      !updates.any (fun update => update.1 == entry.1)) ++ updates)
  | _ => raw

def rootRow : Raw := fields (commonRow "TranslationUnitDecl") [
  ("id", .string "0x1"), ("canonical", .string "0x1"),
  ("semantic_context", .null), ("lexical_context", .null)]

def sourceFunction : Raw := .object [
  ("id", .string "0x2"), ("kind", .string "FunctionDecl"), ("name", .string "sample"),
  ("inner", .array [.object [("id", .string "parameter"), ("kind", .string "ParmVarDecl")]])]

def document (source row : Raw) (extra : List Raw := []) : Raw := .object [
  ("ast", fields probeAst [("inner", .array [source])]),
  ("metadata", probeMetadata ([rootRow, row] ++ extra))]

def admission (source row : Raw) (extra : List Raw := []) :
    Except String LocalFunctionDeclaration := do
  let probe ← parseDeclarationProbe (document source row extra)
  admitLocalFunctionDeclaration probe [0]

def body (kind : String) : Raw := .object [("kind", .string kind), ("inner", .array [])]

def bodySource (kind : String) : Raw := fields sourceFunction [
  ("inner", .array [body kind])]

def bodyRow (kind : String) : Raw := fields functionRow [
  ("definition", .bool true), ("body_present", .bool true),
  ("own_body_kind", .string kind), ("own_body_owner", .string "0x2")]

def scopedAdmission (sourceName metadataName : String) (sourceInline : Bool := false) :
    Except String LocalFunctionDeclaration := do
  let namespaceRow := fields (commonRow "NamespaceDecl") [
    ("id", .string "0x3"), ("canonical", .string "0x3"),
    ("name", .string metadataName), ("inline_namespace", .bool false),
    ("anonymous_namespace", .bool false)]
  let namespaceSource : Raw := .object [
    ("id", .string "0x3"), ("kind", .string "NamespaceDecl"),
    ("name", .string sourceName), ("isInline", .bool sourceInline),
    ("inner", .array [sourceFunction])]
  let row := fields functionRow [
    ("lexical_context", .string "0x3"), ("semantic_context", .string "0x3")]
  let probe ← parseDeclarationProbe (document namespaceSource row [namespaceRow])
  admitLocalFunctionDeclaration probe [0, 0]

#guard (sourceFunction.atPath [0]).bind (fun raw => raw.text "kind") == some "ParmVarDecl"
#guard sourceFunction.atPath [1] == none
#guard sourceFunction.atPath [0, 0] == none
#guard cppIdentifier "_function_9"
#guard !cppIdentifier "operator+"
#guard !cppIdentifier "héllo"
#guard !cppIdentifier "9function"
#guard !cppIdentifier ""
#guard (admission sourceFunction functionRow).map (·.form.definesEntity) matches .ok false
#guard (admission sourceFunction functionRow).map (·.parameters.length) matches .ok 1
#guard (admission (bodySource "CompoundStmt") (bodyRow "CompoundStmt")).toOption.map
  (·.form) == some (.compound (body "CompoundStmt"))
#guard (admission (bodySource "CXXTryStmt") (bodyRow "CXXTryStmt")).toOption.map
  (·.form) == some (.functionTry (body "CXXTryStmt"))
#guard (admission (fields sourceFunction [("explicitlyDeleted", .bool true)])
  (fields functionRow [("definition", .bool true), ("deleted_as_written", .bool true)])).map
  (·.form) matches .ok LocalFunctionForm.deleted
#guard (admission sourceFunction functionRow [functionRow]).isOk
#guard (scopedAdmission "scope" "scope").isOk
#guard scopedAdmission "scope" "other" matches .error _
#guard scopedAdmission "" "scope" matches .error _
#guard scopedAdmission "scope" "scope" true matches .error _
#guard (admission sourceFunction functionRow
  [fields functionRow [("name", .string "other")]]) matches .error _
#guard (admission sourceFunction (fields functionRow [("implicit", .bool true)])) matches .error _
#guard (admission sourceFunction (fields functionRow [("dependent_context", .bool true)])) matches .error _
#guard (admission sourceFunction (fields functionRow [("owning_module", .string "module")])) matches .error _
#guard (admission sourceFunction (fields functionRow [("function_templated_kind", .number "1")])) matches .error _
#guard (admission sourceFunction (fields functionRow [("template_specialization_kind", .number "2")])) matches .error _
#guard (admission sourceFunction (removeField functionRow "function_templated_kind")) matches .error _
#guard (admission sourceFunction (fields functionRow [("function_has_skipped_body", .bool true)])) matches .error _
#guard (admission sourceFunction (fields functionRow [("function_will_have_body", .bool true)])) matches .error _
#guard (admission sourceFunction (fields functionRow [("function_late_template_parsed", .bool true)])) matches .error _
#guard (admission sourceFunction (fields functionRow [("defaulted", .bool true)])) matches .error _
#guard (admission sourceFunction (fields functionRow [("function_has_defining_attr", .bool true)])) matches .error _
#guard (admission sourceFunction (fields functionRow [("function_attribute_count", .number "1")])) matches .error _
#guard (admission sourceFunction (fields functionRow [("definition", .bool true)])) matches .error _
#guard (admission sourceFunction (bodyRow "CompoundStmt")) matches .error _
#guard (admission sourceFunction (fields functionRow [("deleted_as_written", .bool true)])) matches .error _
#guard (admission (bodySource "CompoundStmt") functionRow) matches .error _
#guard (admission (bodySource "CompoundStmt")
  (fields (bodyRow "CompoundStmt") [("own_body_owner", .string "other")])) matches .error _
#guard (admission (bodySource "CompoundStmt") (bodyRow "CXXTryStmt")) matches .error _
#guard (admission (bodySource "CoroutineBodyStmt") (bodyRow "CoroutineBodyStmt")) matches .error _
#guard (admission (fields sourceFunction [("inner", .array [body "CompoundStmt", body "CompoundStmt"])])
  (bodyRow "CompoundStmt")) matches .error _
#guard (admission (fields sourceFunction [("explicitlyDeleted", .string "yes")]) functionRow) matches .error _
#guard (admission sourceFunction (fields functionRow [("lexical_context", .string "0x2")])) matches .error _
#guard (admission sourceFunction (fields functionRow [("semantic_context", .string "missing")])) matches .error _
#guard (admission (fields sourceFunction [("parentDeclContextId", .string "missing")]) functionRow) matches .error _
#guard (admission (fields sourceFunction [("kind", .string "CXXMethodDecl")]) functionRow) matches .error _

end LeanModels.Cpp.LocalFunctionTests
