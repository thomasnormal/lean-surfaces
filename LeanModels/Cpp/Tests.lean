import LeanModels.Cpp
import LeanModels.Cpp.EvidenceTests
import LeanModels.Cpp.CaptureTests
import LeanModels.Cpp.LocalFunctionTests
import LeanModels.Cpp.IntegralTests
import LeanModels.Cpp.TypeTests
import LeanModels.Cpp.ScalarTypeTests
import LeanModels.Cpp.CompositeTypeTests
import LeanModels.Cpp.ReferenceTypeTests
import LeanModels.Cpp.IntegralExpressionTypeTests
import LeanModels.Cpp.CallableEvaluationTests
import LeanModels.Cpp.ObjectModelTests
import LeanModels.Cpp.IntegralObjectTests
import LeanModels.Cpp.IntegralObjectConversionTests
import LeanModels.Cpp.IntegralObjectExpressionTests
import LeanModels.Cpp.IntegralObjectStatementTests
import LeanModels.Cpp.IntegralObjectFrameTests
import LeanModels.Cpp.AutomaticDeclarationsTests
import LeanModels.Cpp.TypeEvidenceTests
import LeanModels.Cpp.VariableEvidenceTests
import LeanModels.Cpp.CallableTests

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

def contextEvidenceRow (id canonical : String)
    (semantic lexical : Option String) : DeclarationEvidenceRow :=
  {evidenceRow id "FunctionDecl" canonical with
    semanticContext := semantic.map (fun value => {value := value})
    lexicalContext := lexical.map (fun value => {value := value})}

def genericContextEvidenceRow (id kind : String)
    (semantic lexical : Option String) : DeclarationEvidenceRow :=
  {evidenceRow id kind id with
    semanticContext := semantic.map (fun value => {value := value})
    lexicalContext := lexical.map (fun value => {value := value})}

def linkageEvidenceRow (id kind internal formal : String) (language : Option String) :
    DeclarationEvidenceRow :=
  let languageField := match language with
    | none => []
    | some value => [("language_linkage", .string value)]
  {evidenceRow id kind id with
    raw := .object ([
      ("linkage_internal", .string internal),
      ("linkage_formal", .string formal)] ++ languageField)}

def canonicalEvidenceRow (id kind canonical : String) (previous : Option String) :
    DeclarationEvidenceRow := {evidenceRow id kind canonical with
  previous := previous.map (fun value => {value := value})}

def identityProbe : DeclarationProbe := {
  ast := .null, metadata := .null
  declarations := [
    evidenceRow "f1" "FunctionDecl" "f1",
    evidenceRow "f2" "FunctionDecl" "f1",
    evidenceRow "out" "CXXMethodDecl" "missing"]
}

def rootEvidenceProbe : DeclarationProbe := {identityProbe with
  declarations := [canonicalEvidenceRow "f1" "FunctionDecl" "f1" none,
    canonicalEvidenceRow "f2" "FunctionDecl" "f1" (some "f1"),
    canonicalEvidenceRow "out" "CXXMethodDecl" "missing" (some "missing")]}

#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match canonicalTargetCandidates probe identityProbe declaration with
      | .ok candidates => candidates.map Declaration.path == [[0, 0]]
      | .error _ => false
  | none => false

#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match canonicalRootEvidence rootEvidenceProbe declaration with
      | .ok handle => handle.value == "f1"
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [0, 1] with
  | some declaration =>
      match canonicalRootEvidence rootEvidenceProbe declaration with
      | .ok handle => handle.value == "f1"
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [1] with
  | some declaration =>
      match canonicalRootEvidence rootEvidenceProbe declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 1] with
  | some declaration =>
      let missingPredecessor := {rootEvidenceProbe with
        declarations := [canonicalEvidenceRow "f1" "FunctionDecl" "f1" none,
          canonicalEvidenceRow "f2" "FunctionDecl" "f1" none]}
      match canonicalRootEvidence missingPredecessor declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let nonIdempotent := {rootEvidenceProbe with
        declarations := [canonicalEvidenceRow "f1" "FunctionDecl" "f2" none,
          canonicalEvidenceRow "f2" "FunctionDecl" "f1" (some "f1")]}
      match canonicalRootEvidence nonIdempotent declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 1] with
  | some declaration =>
      match canonicalPredecessorChainEvidence rootEvidenceProbe declaration with
      | .ok chain => chain.map (·.value) == ["f2", "f1"]
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match canonicalPredecessorChainEvidence rootEvidenceProbe declaration with
      | .ok chain => chain.map (·.value) == ["f1"]
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [1] with
  | some declaration =>
      match canonicalPredecessorChainEvidence rootEvidenceProbe declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 1] with
  | some declaration =>
      let cyclic := {rootEvidenceProbe with
        declarations := [canonicalEvidenceRow "f1" "FunctionDecl" "f1" (some "f2"),
          canonicalEvidenceRow "f2" "FunctionDecl" "f1" (some "f1")]}
      match canonicalPredecessorChainEvidence cyclic declaration with
      | .ok _ => false
      | .error _ => true
  | none => false

def contextProbe : DeclarationProbe := {identityProbe with
  declarations := [contextEvidenceRow "f1" "f1" (some "ns") (some "ns"),
    contextEvidenceRow "f2" "f1" (some "ns") (some "ns"),
    contextEvidenceRow "out" "missing" (some "cls") (some "cls")]}

def chainProbe : DeclarationProbe := {identityProbe with
  declarations := [
    genericContextEvidenceRow "f1" "FunctionDecl" (some "ns") (some "ns"),
    genericContextEvidenceRow "ns" "NamespaceDecl" (some "tu") (some "tu"),
    genericContextEvidenceRow "tu" "TranslationUnitDecl" none none]}

#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match semanticContextCandidates probe contextProbe declaration with
      | .ok candidates => candidates.map Declaration.path == [[0]]
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match lexicalContextCandidates probe contextProbe declaration with
      | .ok candidates => candidates.map Declaration.path == [[0]]
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [1] with
  | some declaration =>
      match semanticContextCandidates probe contextProbe declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let conflicting := {contextProbe with
        declarations := [contextEvidenceRow "f1" "f1" (some "ns") (some "ns"),
          contextEvidenceRow "f1" "f1" none none]}
      match semanticContextCandidates probe conflicting declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match repeatedProbe.declarationAtPath [4] with
  | some declaration =>
      let repeatedContext := {identityProbe with
        declarations := [
          {evidenceRow "next" "VarDecl" "shared" with
            semanticContext := some {value := "shared"}
            lexicalContext := some {value := "shared"}}]}
      match semanticContextCandidates repeatedProbe repeatedContext declaration with
      | .ok candidates => candidates.map Declaration.path == [[1], [2, 1, 0], [3]]
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match semanticContextChainEvidence probe chainProbe declaration with
      | .ok chain => chain.map (·.value) == ["ns", "tu"]
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match lexicalContextChainEvidence probe chainProbe declaration with
      | .ok chain => chain.map (·.value) == ["ns", "tu"]
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match semanticContextChainEvidence probe contextProbe declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let cyclic := {chainProbe with
        declarations := [
          genericContextEvidenceRow "f1" "FunctionDecl" (some "ns") (some "ns"),
          genericContextEvidenceRow "ns" "NamespaceDecl" (some "f1") (some "f1")]}
      match semanticContextChainEvidence probe cyclic declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let nonroot := {chainProbe with
        declarations := [
          genericContextEvidenceRow "f1" "FunctionDecl" (some "ns") (some "ns"),
          genericContextEvidenceRow "ns" "NamespaceDecl" none none]}
      match semanticContextChainEvidence probe nonroot declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let badRoot := {chainProbe with
        declarations := [
          genericContextEvidenceRow "f1" "FunctionDecl" (some "ns") (some "ns"),
          genericContextEvidenceRow "ns" "NamespaceDecl" (some "tu") (some "tu"),
          genericContextEvidenceRow "tu" "TranslationUnitDecl" (some "ns") (some "ns")]}
      match semanticContextChainEvidence probe badRoot declaration with
      | .ok _ => false
      | .error _ => true
  | none => false

def contextChainsRefuse (artifact : Artifact) (evidence : DeclarationProbe)
    (declaration : Declaration) : Bool :=
  match semanticContextChainEvidence artifact evidence declaration,
      lexicalContextChainEvidence artifact evidence declaration with
  | .error _, .error _ => true
  | _, _ => false

def contextOccurrenceArtifact (extraId extraKind : String) : Artifact := {probe with
  ast := .object [
    ("id", .string "tu"), ("kind", .string "TranslationUnitDecl"),
    ("inner", .array [
      .object [("id", .string "ns"), ("kind", .string "NamespaceDecl"),
        ("inner", .array [
          .object [("id", .string "f1"), ("kind", .string "FunctionDecl")]])],
      .object [("id", .string extraId), ("kind", .string extraKind)]])]
}

#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      [("f1", "NamespaceDecl"), ("ns", "FunctionDecl"),
        ("ns", "TranslationUnitDecl"), ("tu", "NamespaceDecl")].all fun change =>
          let changed := {chainProbe with declarations := chainProbe.declarations.map fun row =>
            if row.id.value == change.1 then {row with kind := change.2} else row}
          contextChainsRefuse probe changed declaration
  | none => false

#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      [{declaration with path := [99]}, {declaration with kind := "NamespaceDecl"}].all
        (contextChainsRefuse probe chainProbe)
  | none => false

#guard
  let repeated := contextOccurrenceArtifact "ns" "NamespaceDecl"
  match repeated.declarationAtPath [0, 0] with
  | some declaration =>
      match semanticContextChainEvidence repeated chainProbe declaration,
          lexicalContextChainEvidence repeated chainProbe declaration with
      | .ok semantic, .ok lexical =>
          semantic.map (·.value) == ["ns", "tu"] && lexical.map (·.value) == ["ns", "tu"]
      | _, _ => false
  | none => false

#guard
  let conflicting := contextOccurrenceArtifact "ns" "VarDecl"
  match conflicting.declarationAtPath [0, 0] with
  | some declaration => contextChainsRefuse conflicting chainProbe declaration
  | none => false

#guard
  let nestedRoot := contextOccurrenceArtifact "nested" "TranslationUnitDecl"
  let changed := {chainProbe with declarations := [
    genericContextEvidenceRow "f1" "FunctionDecl" (some "nested") (some "nested"),
    genericContextEvidenceRow "nested" "TranslationUnitDecl" none none]}
  match nestedRoot.declarationAtPath [0, 0] with
  | some declaration => contextChainsRefuse nestedRoot changed declaration
  | none => false

#guard match probe.declarationAtPath [] with
  | some declaration =>
      match semanticContextChainEvidence probe chainProbe declaration,
          lexicalContextChainEvidence probe chainProbe declaration with
      | .ok [], .ok [] => true
      | _, _ => false
  | none => false

def linkageProbe : DeclarationProbe := {identityProbe with
  declarations := [
    linkageEvidenceRow "f1" "FunctionDecl" "External" "External" (some "C++"),
    linkageEvidenceRow "f2" "FunctionDecl" "Internal" "Internal" (some "C"),
    linkageEvidenceRow "out" "CXXMethodDecl" "External" "External" none]}

#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      match linkageEvidence linkageProbe declaration with
      | .ok evidence => evidence.internal == "External" && evidence.formal == "External" &&
          evidence.language == some "C++"
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [0, 1] with
  | some declaration =>
      match linkageEvidence linkageProbe declaration with
      | .ok evidence => evidence.internal == "Internal" && evidence.language == some "C"
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [1] with
  | some declaration =>
      match linkageEvidence linkageProbe declaration with
      | .ok evidence => evidence.language.isNone
      | .error _ => false
  | none => false
#guard match probe.declarationAtPath [] with
  | some declaration =>
      match linkageEvidence linkageProbe declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let missing := {linkageProbe with
        declarations := [evidenceRow "f1" "FunctionDecl" "f1"]}
      match linkageEvidence missing declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let invalid := {linkageProbe with
        declarations := [linkageEvidenceRow "f1" "FunctionDecl" "Mystery" "External" (some "C++")]}
      match linkageEvidence invalid declaration with
      | .ok _ => false
      | .error _ => true
  | none => false
#guard match probe.declarationAtPath [0, 0] with
  | some declaration =>
      let conflicting := {linkageProbe with
        declarations := [linkageEvidenceRow "f1" "FunctionDecl" "External" "External" (some "C++"),
          linkageEvidenceRow "f1" "FunctionDecl" "Internal" "External" (some "C++")]}
      match linkageEvidence conflicting declaration with
      | .ok _ => false
      | .error _ => true
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
