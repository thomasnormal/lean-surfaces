import LeanModels.Cpp
import LeanModels.Cpp.EvidenceTests
import LeanModels.Cpp.CaptureTests

namespace LeanModels.Cpp.Tests

def probe : Artifact := {
  sourceFile := "/probe.cpp", sourceSha256 := String.ofList (List.replicate 64 'a')
  frontend := .object [], dependencies := []
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "ns"), ("kind", .string "NamespaceDecl"),
        ("name", .string "N"), ("inner", .array [
          .object [("id", .string "f1"), ("kind", .string "FunctionDecl"),
            ("name", .string "f"), ("mangledName", .string "_ZN1N1fEi"),
            ("referencedDecl", .object [("id", .string "stub"),
              ("kind", .string "FunctionDecl")])],
          .object [("id", .string "f2"), ("kind", .string "FunctionDecl"),
            ("name", .string "f"), ("mangledName", .string "_ZN1N1fEd")]])],
      .object [("id", .string "out"), ("kind", .string "CXXMethodDecl"),
        ("parentDeclContextId", .string "cls"), ("previousDecl", .string "prior")],
      .object [("kind", .string "FutureNode"), ("payload", .string "retained")]])]
}

#guard probe.ast.text "kind" == some "TranslationUnitDecl"
#guard probe.declarations.length == 5
#guard (probe.declarationsById "tu").map Declaration.path == [[]]
#guard (probe.declarationsById "ns").map Declaration.path == [[0]]
#guard (probe.declarationsById "f1").map Declaration.path == [[0, 0]]
#guard (probe.declarationsById "f2").map Declaration.path == [[0, 1]]
#guard (probe.declarationsById "out").map Declaration.path == [[1]]
#guard (probe.declarationAtPath []).map Declaration.id == some "tu"
#guard (probe.declarationAtPath [0, 1]).map Declaration.id == some "f2"
#guard (probe.declarationAtPath [0, 2]).isNone
#guard match probe.declarationAtPath [1] with
  | some declaration => (probe.previousDeclCandidates declaration).isEmpty
  | none => false
#guard match probe.declarationAtPath [1] with
  | some declaration => (probe.semanticParentCandidates declaration).isEmpty
  | none => false
#guard (probe.declarationsById "f1").map Declaration.lexicalParents == [["tu", "ns"]]
#guard (probe.declarationsById "out").map Declaration.semanticParent == [some "cls"]
#guard (probe.declarationsById "out").map Declaration.previousDecl == [some "prior"]
#guard (probe.declarationsById "stub").isEmpty
#guard (probe.declarations.filter fun declaration => declaration.name == some "f").length == 2
#guard execute probe "f1" matches .error _
#guard execute probe "absent" matches .error _

def repeatedDeclaration : Raw :=
  .object [("id", .string "shared"), ("kind", .string "VarDecl")]

def repeatedReference : Raw :=
  .object [("id", .string "next"), ("kind", .string "VarDecl"),
    ("previousDecl", .string "shared"), ("parentDeclContextId", .string "shared")]

def repeatedProbe : Artifact := { probe with
  ast := .object [("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [.null, repeatedDeclaration,
      .object [("kind", .string "CompoundStmt"), ("inner", .array [.bool false,
        .object [("kind", .string "FutureDecl"),
          ("inner", .array [repeatedDeclaration])]])], repeatedDeclaration,
      repeatedReference])]
}

#guard repeatedProbe.declarations.length == 5
#guard (repeatedProbe.declarationsById "shared").map Declaration.path == [[1], [2, 1, 0], [3]]
#guard (repeatedProbe.declarationAtPath [2, 1, 0]).map Declaration.id == some "shared"
#guard match repeatedProbe.declarationAtPath [4] with
  | some declaration => (repeatedProbe.previousDeclCandidates declaration).map Declaration.path ==
      [[1], [2, 1, 0], [3]]
  | none => false
#guard match repeatedProbe.declarationAtPath [4] with
  | some declaration => (repeatedProbe.semanticParentCandidates declaration).map Declaration.path ==
      [[1], [2, 1, 0], [3]]
  | none => false
#guard (repeatedProbe.declarationsById "shared").map Declaration.lexicalParents ==
  [["tu"], ["tu"], ["tu"]]

def evidenceRow (id kind canonical : String) : DeclarationEvidenceRow := {
  ordinal := 0, id := {value := id}, kind, canonical := {value := canonical}
  previous := none, semanticContext := none, lexicalContext := none
  implicit := false, dependentContext := false, owningModule := none
  functionShape := none, raw := .object []
}

def functionShape (definition bodyPresent : Bool) : FunctionShapeEvidence := {
  definition, bodyPresent, defaulted := false, deletedAsWritten := false
  skippedBody := false, pendingBody := false, definingAttribute := false
  lateParsed := false, explicitlyDefaulted := false, attributeCount := 0
  ownBodyKind := none, ownBodyOwner := none
}

def functionEvidenceRow (id canonical : String) (shape : FunctionShapeEvidence) :
    DeclarationEvidenceRow := {evidenceRow id "FunctionDecl" canonical with
  functionShape := some shape}

def identityProbe : DeclarationProbe := {
  ast := .null, metadata := .null
  declarations := [
    evidenceRow "f1" "FunctionDecl" "f1",
    evidenceRow "f2" "FunctionDecl" "f1",
    evidenceRow "out" "CXXMethodDecl" "missing"]
}

#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match canonicalTargetCandidates probe identityProbe declaration with
      | .ok candidates => candidates.map Declaration.path == [[0, 0]]
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [0, 1] with
  | some declaration =>
      match canonicalTargetCandidates probe identityProbe declaration with
      | .ok candidates => candidates.map Declaration.path == [[0, 0]]
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [1] with
  | some declaration =>
      match canonicalTargetCandidates probe identityProbe declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let conflicting := {identityProbe with
        declarations := [evidenceRow "f1" "FunctionDecl" "f1",
          evidenceRow "f1" "FunctionDecl" "f2"]}
      match canonicalTargetCandidates probe conflicting declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let wrongKind := {identityProbe with
        declarations := [evidenceRow "f1" "VarDecl" "f1"]}
      match canonicalTargetCandidates probe wrongKind declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match repeatedProbe.declarationAtPath [4] with
  | some declaration =>
      let repeatedEvidence := {identityProbe with
        declarations := [evidenceRow "next" "VarDecl" "shared"]}
      match canonicalTargetCandidates repeatedProbe repeatedEvidence declaration with
      | .ok candidates => candidates.map Declaration.path == [[1], [2, 1, 0], [3]]
      | .error _ => false
  | none => false

def definitionProbe : DeclarationProbe := {identityProbe with
  declarations := [functionEvidenceRow "f1" "f1" (functionShape true true),
    functionEvidenceRow "f2" "f1" (functionShape false false)]}

#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match functionDefinitionEvidence definitionProbe declaration with
      | .ok value => value
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [0, 1] with
  | some declaration =>
      match functionDefinitionEvidence definitionProbe declaration with
      | .ok value => !value
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [1] with
  | some declaration =>
      match functionDefinitionEvidence definitionProbe declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let conflicting := {definitionProbe with
        declarations := [functionEvidenceRow "f1" "f1" (functionShape true true),
          functionEvidenceRow "f1" "f1" (functionShape false false)]}
      match functionDefinitionEvidence conflicting declaration with
      | .ok _ => false
      | .error _ => true
  | none => false

#guard parseArtifactString "{}" matches .error _
#guard parseArtifactString "{\"schema_version\":\"cpp-9\"}" matches .error _
#guard requireHash "not-a-hash" matches .error _
#guard (requireHash (String.ofList (List.replicate 64 'a'))).isOk
#guard (rawOfJson (.num 9007199254740993)) == .number "9007199254740993"
#guard validateDependencies [{path := "/same.hpp", sha256 := "first"},
  {path := "/same.hpp", sha256 := "second"}] matches .error _
#guard (validateDependencies [{path := "/first.hpp", sha256 := "first"},
  {path := "/second.hpp", sha256 := "second"}]).isOk

end LeanModels.Cpp.Tests
