import LeanModels.Cpp
import LeanModels.Cpp.EvidenceTests

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
#guard (probe.declarationsById "f1").map Declaration.lexicalParents == [["tu", "ns"]]
#guard (probe.declarationsById "out").map Declaration.semanticParent == [some "cls"]
#guard (probe.declarationsById "out").map Declaration.previousDecl == [some "prior"]
#guard (probe.declarationsById "stub").isEmpty
#guard (probe.declarations.filter fun declaration => declaration.name == some "f").length == 2
#guard execute probe "f1" matches .error _
#guard execute probe "absent" matches .error _
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
