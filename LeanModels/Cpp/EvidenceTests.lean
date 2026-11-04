import LeanModels.Cpp.Evidence

namespace LeanModels.Cpp.EvidenceTests

#guard parseStrictRawString "null" matches .ok .null
#guard parseStrictRawString "true" matches .ok (.bool true)
#guard parseStrictRawString "false" matches .ok (.bool false)
#guard parseStrictRawString "-0" matches .ok (.number "-0")
#guard parseStrictRawString "0.125" matches .error _
#guard parseStrictRawString "9007199254740993" matches .ok (.number "9007199254740993")
#guard parseStrictRawString "5e+03" matches .error _
#guard parseStrictRawString "\"héllo\"" matches .ok (.string "héllo")
#guard parseStrictRawString "\"\\u0061\"" matches .ok (.string "a")
#guard parseStrictRawString "\"\\uD83D\\uDE00\"" matches .ok (.string "😀")
#guard parseStrictRawString " \n [null, true, 2] \t " matches
  .ok (.array [.null, .bool true, .number "2"])
#guard parseStrictRawString "{\"null\":null,\"present\":true}" matches
  .ok (.object [("null", .null), ("present", .bool true)])
#guard parseStrictRawString "{\"a\":1,\"a\":2}" matches .error _
#guard parseStrictRawString "{\"a\":1,\"\\u0061\":2}" matches .error _
#guard parseStrictRawString "{\"outer\":[{\"a\":1,\"a\":2}]}" matches .error _
#guard parseStrictRawString "{\"a\":1,\"b\":{\"a\":2}}" matches .ok _
#guard parseStrictRawString "{\"a\":1,}" matches .error _
#guard parseStrictRawString "[1,]" matches .error _
#guard parseStrictRawString "[1 2]" matches .error _
#guard parseStrictRawString "01" matches .error _
#guard parseStrictRawString "-01" matches .error _
#guard parseStrictRawString "+1" matches .error _
#guard parseStrictRawString ".5" matches .error _
#guard parseStrictRawString "-.5" matches .error _
#guard parseStrictRawString "1." matches .error _
#guard parseStrictRawString "1e" matches .error _
#guard parseStrictRawString "1e+" matches .error _
#guard parseStrictRawString "NaN" matches .error _
#guard parseStrictRawString "Infinity" matches .error _
#guard parseStrictRawString "null false" matches .error _
#guard parseStrictRawString "\"\\q\"" matches .error _
#guard parseStrictRawString "\"\\ud800\"" matches .error _
#guard parseStrictRawString "\"\\udc00\"" matches .error _
#guard parseStrictRawString "\"\\ud800\\u0061\"" matches .error _
#guard parseStrictRawString "\"\\u00xz\"" matches .error _
#guard parseStrictRawString (String.ofList ['"', Char.ofNat 1, '"']) matches .error _

def replaceField (raw : Raw) (name : String) (value : Raw) : Raw :=
  match raw with
  | .object fields => .object (fields.map fun field =>
      if field.1 == name then (name, value) else field)
  | _ => raw

def removeField (raw : Raw) (name : String) : Raw :=
  match raw with
  | .object fields => .object (fields.filter fun field => field.1 != name)
  | _ => raw

def commonRow (kind : String) : Raw := .object [
  ("id", .string "0x2"), ("kind", .string kind), ("name", .string "sample"),
  ("canonical", .string "0x2"), ("previous", .null),
  ("semantic_context", .string "0x1"), ("lexical_context", .string "0x1"),
  ("implicit", .bool false), ("dependent_context", .bool false),
  ("owning_module", .null), ("definition", .null),
  ("definition_api", .string "not-queried"),
  ("linkage_internal", .string "External"), ("linkage_formal", .string "External")]

def functionRow : Raw :=
  match commonRow "FunctionDecl" with
  | .object fields => .object ((fields.filter fun field =>
      field.1 != "definition" && field.1 != "definition_api") ++ [
    ("definition", .bool false),
    ("definition_api", .string "FunctionDecl.isThisDeclarationADefinition"),
    ("body_present", .bool false), ("defaulted", .bool false),
    ("deleted_as_written", .bool false),
    ("function_has_skipped_body", .bool false),
    ("function_has_skipped_body_api", .string "FunctionDecl.hasSkippedBody"),
    ("function_will_have_body", .bool false),
    ("function_will_have_body_api", .string "FunctionDecl.willHaveBody"),
    ("function_has_defining_attr", .bool false),
    ("function_has_defining_attr_api", .string "FunctionDecl.hasDefiningAttr"),
    ("function_late_template_parsed", .bool false),
    ("function_late_template_parsed_api", .string "FunctionDecl.isLateTemplateParsed"),
    ("function_explicitly_defaulted", .bool false),
    ("function_explicitly_defaulted_api", .string "FunctionDecl.isExplicitlyDefaulted"),
    ("function_attribute_count", .number "0"),
    ("function_attribute_count_api", .string "Decl.hasAttrs/Decl.getAttrs.size"),
    ("own_body_kind", .null), ("own_body_owner", .null),
    ("own_body_api", .string "FunctionDecl.getBody"),
    ("language_linkage", .string "C++"),
    ("template_specialization_kind", .number "0"),
    ("template_specialization_kind_api", .string "FunctionDecl.getTemplateSpecializationKind"),
    ("function_templated_kind", .number "0"),
    ("function_templated_kind_api", .string "FunctionDecl.getTemplatedKind")])
  | _ => .null

def probeAst : Raw := .object [
  ("id", .string "0x1"), ("kind", .string "TranslationUnitDecl"),
  ("inner", .array []), ("opaque_integer", .number "9007199254740993")]

def probeMetadata (rows : List Raw) : Raw := .object [
  ("schema_version", .string "cpp-canonical-probe-0.3"),
  ("compiled_frontend", .string "21.1.8"),
  ("runtime_frontend", .string "clang version 21.1.8"),
  ("llvm_headers", .string "21.1.8"), ("declarations", .array rows)]

def probeDocument (rows : List Raw) : Raw := .object [
  ("ast", probeAst), ("metadata", probeMetadata rows)]

def rowParses (row : Raw) : Bool :=
  (parseDeclarationProbe (probeDocument [row])).isOk

def metadataParses (metadata : Raw) : Bool :=
  (parseDeclarationProbe (.object [("ast", probeAst), ("metadata", metadata)])).isOk

def functionBooleanFields : List String := [
  "definition", "body_present", "defaulted", "deleted_as_written",
  "function_has_skipped_body", "function_will_have_body", "function_has_defining_attr",
  "function_late_template_parsed", "function_explicitly_defaulted"]

def functionApiFields : List String := [
  "definition_api", "function_has_skipped_body_api", "function_will_have_body_api",
  "function_has_defining_attr_api", "function_late_template_parsed_api",
  "function_explicitly_defaulted_api", "function_attribute_count_api", "own_body_api"]

#guard (parseDeclarationProbe (probeDocument [])).isOk
#guard rowParses functionRow
#guard rowParses (commonRow "FutureDecl")
#guard parseDeclarationProbe .null matches .error _
#guard parseDeclarationProbe (.object []) matches .error _
#guard parseDeclarationProbe (removeField (probeDocument []) "ast") matches .error _
#guard parseDeclarationProbe (replaceField (probeDocument []) "ast" .null) matches .error _
#guard parseDeclarationProbe (replaceField (probeDocument []) "metadata" .null) matches .error _
#guard parseDeclarationProbe (.object [
  ("ast", probeAst), ("metadata", probeMetadata []), ("metadata", probeMetadata [])]) matches .error _
#guard parseDeclarationProbe (.object [
  ("ast", .object [("id", .string "0x1"), ("kind", .string "TranslationUnitDecl"),
    ("nested", .object [("id", .string "first"), ("id", .string "second")])]),
  ("metadata", probeMetadata [])]) matches .error _
#guard metadataParses (replaceField (probeMetadata []) "runtime_frontend"
  (.string "clang version 21.1.8 (distribution build)"))
#guard !metadataParses (replaceField (probeMetadata []) "runtime_frontend"
  (.string "clang version 21.1.80"))
#guard !metadataParses (replaceField (probeMetadata []) "runtime_frontend"
  (.string "clang version 21.1.8suffix"))
#guard ["cpp-canonical-probe-0.1", "cpp-canonical-probe-0.2", "cpp-canonical-probe-0.4"].all
  fun version => !metadataParses (replaceField (probeMetadata []) "schema_version" (.string version))
#guard ["schema_version", "compiled_frontend", "runtime_frontend", "llvm_headers", "declarations"].all
  fun name => !metadataParses (removeField (probeMetadata []) name)
#guard !metadataParses (replaceField (probeMetadata []) "compiled_frontend" (.string "21.1.7"))
#guard !metadataParses (replaceField (probeMetadata []) "llvm_headers" (.string "21.1.7"))
#guard !metadataParses (replaceField (probeMetadata []) "declarations" .null)
#guard !metadataParses (replaceField (probeMetadata []) "declarations" (.array [.null]))
#guard ["id", "kind", "canonical", "previous", "semantic_context", "lexical_context",
  "implicit", "dependent_context", "owning_module"].all
  fun name => !rowParses (removeField functionRow name)
#guard ["id", "kind", "canonical"].all
  fun name => !rowParses (replaceField functionRow name .null)
#guard !rowParses (replaceField (commonRow "FutureDecl") "implicit" (.number "0"))
#guard !rowParses (replaceField (commonRow "FutureDecl") "id" (.number "2"))
#guard !rowParses (replaceField functionRow "previous" (.bool false))
#guard !rowParses (replaceField functionRow "owning_module" (.number "0"))
#guard ["", "0x", "0X2", "2", "0xxyz", "0x2 trailing"].all
  fun value => !rowParses (replaceField functionRow "canonical" (.string value))
#guard functionBooleanFields.all fun name => !rowParses (removeField functionRow name)
#guard functionBooleanFields.all fun name => !rowParses (replaceField functionRow name .null)
#guard functionBooleanFields.all fun name => !rowParses (replaceField functionRow name (.number "0"))
#guard functionApiFields.all fun name => !rowParses (removeField functionRow name)
#guard functionApiFields.all fun name => !rowParses (replaceField functionRow name (.string "unverified"))
#guard functionApiFields.all fun name => !rowParses (replaceField functionRow name .null)
#guard ["function_attribute_count", "own_body_kind", "own_body_owner"].all
  fun name => !rowParses (removeField functionRow name)
#guard [.null, .bool false, .string "0", .number "-1", .number "01", .number "1.0", .number "1e0"].all
  fun value => !rowParses (replaceField functionRow "function_attribute_count" value)
#guard [.bool false, .number "0", .array []].all
  fun value => !rowParses (replaceField functionRow "own_body_kind" value)
#guard [.bool false, .number "0", .array []].all
  fun value => !rowParses (replaceField functionRow "own_body_owner" value)
#guard rowParses (replaceField functionRow "definition" (.bool true))
#guard functionBooleanFields.all fun name => rowParses (replaceField functionRow name (.bool true))
#guard rowParses (replaceField functionRow "function_attribute_count" (.number "3"))
#guard rowParses (replaceField functionRow "own_body_kind" (.string "FutureStmt"))
#guard rowParses (replaceField functionRow "own_body_owner" (.string "0xdead"))
#guard rowParses (replaceField functionRow "canonical" (.string "0xbeef"))
#guard rowParses (replaceField functionRow "template_specialization_kind" (.string "opaque"))

#guard match parseDeclarationProbe (probeDocument [functionRow, functionRow]) with
  | .ok probe => probe.declarations.length == 2 && probe.functions.length == 2 &&
      probe.declarations.map (·.ordinal) == [0, 1] &&
      probe.declarations.map (·.raw) == [functionRow, functionRow]
  | .error _ => false

#guard match parseDeclarationProbe (probeDocument [
    functionRow, replaceField functionRow "definition" (.bool true)]) with
  | .ok probe => probe.functions.length == 2 &&
      probe.functions.map (fun row => row.functionShape.map (·.definition)) == [some false, some true]
  | .error _ => false

#guard match parseDeclarationProbe (probeDocument [commonRow "CXXMethodDecl", functionRow]) with
  | .ok probe => probe.declarations.map (·.ordinal) == [0, 1] &&
      probe.functions.map (·.ordinal) == [1] && probe.ast == probeAst &&
      probe.metadata == probeMetadata [commonRow "CXXMethodDecl", functionRow]
  | .error _ => false

#guard match parseDeclarationProbe (probeDocument [
    replaceField functionRow "own_body_owner" (.string "0xdead")]) with
  | .ok probe =>
      let shape := probe.functions.head?.bind (·.functionShape)
      (shape.bind (·.ownBodyOwner)).map (·.value) == some "0xdead"
  | .error _ => false

end LeanModels.Cpp.EvidenceTests
