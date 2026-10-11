import LeanModels.Cpp.TypeEvidence

namespace LeanModels.Cpp.TypeEvidenceTests

open LeanModels.Cpp

private def handle (value : String) : FrontendHandle := {value}
private def object (fields : List (String × Raw)) : Raw := .object fields
private def text (value : String) : Raw := .string value
private def flag (value : Bool) : Raw := .bool value
private def typeRow (occurrence canonical : String) (type : Raw) : Raw := object [
  ("type_api", text "Clang::QualType structured type projection v1"),
  ("occurrence", text occurrence), ("canonical", text canonical), ("type", type)]
private def builtin (name : String) : Raw := object [("kind", text "builtin"), ("name", text name)]
private def pointer (pointee : Raw) : Raw := object [("kind", text "pointer"), ("pointee", pointee)]
private def qualified (isConst isVolatile : Bool) (base : Raw) : Raw := object [
  ("kind", text "qualified"), ("const", flag isConst), ("volatile", flag isVolatile),
  ("base", base)]
private def recordType (declaration : String) : Raw := object [
  ("kind", text "record"), ("declaration", text declaration)]
private def functionType (result : Raw) (parameters : List Raw) (variadic : Bool) : Raw := object [
  ("kind", text "function"), ("result", result), ("parameters", .array parameters),
  ("variadic", flag variadic)]
private def declarationRow (id canonical : String) : DeclarationEvidenceRow := {
  ordinal := 0, id := handle id, kind := "VarDecl", canonical := handle canonical,
  previous := none, semanticContext := none, lexicalContext := none, implicit := false,
  dependentContext := false, owningModule := none, functionShape := none, raw := .object []}
private def probe (rows : List DeclarationEvidenceRow) : DeclarationProbe := {
  ast := .object [], metadata := .object [], declarations := rows}
private def oneRow : Raw := typeRow "0x1" "0x1" (builtin "int")
private def pointerRow : Raw := typeRow "0x2" "0x2"
  (pointer (qualified true false (builtin "unsigned long")))
private def functionTypeRaw : Raw :=
  functionType (builtin "long") [builtin "short", pointer (builtin "char")] true
private def functionRow : Raw := typeRow "0x3" "0x3" functionTypeRaw

def parsedTypeIs (raw : Raw) (expected : CppTypeEvidence) : Bool :=
  match parseCppTypeEvidence raw with
  | .ok actual => actual == expected
  | .error _ => false

def parsedTypeRefuses (raw : Raw) : Bool :=
  match parseCppTypeEvidence raw with
  | .ok _ => false
  | .error _ => true

def rowsCountIs (raw : Raw) (expected : Nat) : Bool :=
  match parseTypeEvidenceRows raw with
  | .ok rows => rows.length == expected
  | .error _ => false

def rowsParseIsOk (raw : Raw) : Bool :=
  match parseTypeEvidenceRows raw with
  | .ok _ => true
  | .error _ => false

def rowsParseRefuses (raw : Raw) : Bool :=
  match parseTypeEvidenceRows raw with
  | .ok _ => false
  | .error _ => true

def validationIsOk (declarations : List DeclarationEvidenceRow) (raw : Raw) : Bool :=
  match parseTypeEvidenceRows raw with
  | .ok rows => match validateTypeEvidence (probe declarations) rows with
    | .ok _ => true
    | .error _ => false
  | .error _ => false

def validationRefuses (declarations : List DeclarationEvidenceRow) (raw : Raw) : Bool :=
  match parseTypeEvidenceRows raw with
  | .ok rows => match validateTypeEvidence (probe declarations) rows with
    | .ok _ => false
    | .error _ => true
  | .error _ => true

#guard parsedTypeIs (builtin "unsigned long long") (.builtin .unsignedLongLong)
#guard parsedTypeIs (qualified true false (builtin "int"))
  (.qualified true false (.builtin .int))
#guard parsedTypeIs functionTypeRaw (.function (.builtin .long)
  [.builtin .short, .pointer (.builtin .char)] true)
#guard parsedTypeRefuses (object [("kind", text "builtin"), ("name", text "float")])
#guard parsedTypeRefuses (object [("kind", text "pointer"), ("pointee", text "int")])
#guard parsedTypeRefuses (qualified false false (builtin "int"))
#guard parsedTypeRefuses (object [("qualType", text "int")])
#guard rowsCountIs (.array [oneRow, pointerRow, functionRow]) 3
#guard rowsParseRefuses (.array [object [("type_api", text "other")]])
#guard rowsParseIsOk (.array [oneRow])
#guard validationIsOk [declarationRow "0x1" "0x1"] (.array [oneRow])
#guard validationIsOk [declarationRow "0x2" "0x2"] (.array [pointerRow])
#guard validationIsOk [declarationRow "0x3" "0x3"] (.array [functionRow])
#guard validationRefuses [declarationRow "0x1" "0x9"] (.array [oneRow])
#guard validationRefuses [declarationRow "0x1" "0x1"]
  (.array [typeRow "0x9" "0x9" (builtin "int")])
#guard validationIsOk [declarationRow "0x1" "0x1"] (.array [oneRow, oneRow])
#guard validationRefuses [declarationRow "0x1" "0x1"]
  (.array [oneRow, typeRow "0x1" "0x1" (builtin "long")])
#guard validationIsOk [declarationRow "0x4" "0x4", declarationRow "0x5" "0x5"]
  (.array [typeRow "0x4" "0x4" (recordType "0x5")])
#guard validationRefuses [declarationRow "0x4" "0x4"]
  (.array [typeRow "0x4" "0x4" (recordType "0x5")])
def parsedRows : List TypeEvidenceRow :=
  match parseTypeEvidenceRows (.array [oneRow]) with
  | .ok rows => rows
  | .error _ => []

#guard typeEvidenceFor parsedRows (handle "0x1") == some (.builtin .int)

end LeanModels.Cpp.TypeEvidenceTests
