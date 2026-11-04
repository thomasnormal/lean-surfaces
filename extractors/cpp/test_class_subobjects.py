#!/usr/bin/env python3
"""Nonvirtual base occurrences, native source getters and evidence refusals."""
import importlib.util
import hashlib
import json
import os
import pathlib
import unittest

_spec = importlib.util.spec_from_file_location("getter_helpers", pathlib.Path(__file__).with_name("test_member_getters.py"))
_helpers = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_helpers)
ROOT = _helpers.ROOT

SUPPLIED = r'''
def suppliedProjection (hierarchy : ClassHierarchy) (getter : IntegralMemberGetter)
    (path : List Nat) (input : Int) (constant : Bool) : Except String ClassReceiverProjection := do
  let slots ← hierarchy.slots
  let some (_, index) := slots.zipIdx.find? (fun (slot, _) => slot.path == path)
    | throw "missing receiver path"
  let format ← (TargetProfile.lp64.format getter.result).mapError (fun _ => "unavailable target format")
  pure {
    hierarchy, objects := List.range slots.length, receiverPath := path,
    snapshot := {
      memory := {
        profile := .lp64,
        objects := {objects := slots.map (fun slot =>
          ⟨.automatic, integralMemberViewType (.record slot.declaration) constant, .aliveInitialized⟩) ++
          [⟨.automatic, integralMemberViewType getter.field.type (constant && !getter.field.isMutable), .aliveInitialized⟩]},
        values := slots.map (fun _ => none) ++ [some ⟨format, input⟩]},
      object := index, member := slots.length, field := getter.field.declaration}}
def agrees (hierarchy : ClassHierarchy) (getter : IntegralMemberGetter)
    (path : List Nat) (input expected : Int) (constant : Bool) : Bool :=
  match suppliedProjection hierarchy getter path input constant with
  | .error _ => false
  | .ok projection => match projection.invoke getter with
    | .ok (memory, value) => memory == projection.snapshot.memory && value.value == expected
    | .error _ => false
'''

class ClassSubobjectTests(unittest.TestCase):
    setUp = _helpers.MemberGetterTests.setUp
    run_ok = _helpers.MemberGetterTests.run_ok
    native = _helpers.MemberGetterTests.native
    lean = _helpers.MemberGetterTests.lean

    def test_compiled_nonvirtual_base_paths_and_refusals(self):
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not library:
            self.skipTest("set matching LEANCPP_PROBE_LIBRARY")
        definitions = r'''
struct Base { int value; virtual void tag() = 0; int read() const { return value; } };
struct Left : Base {};
struct Right : Base {};
struct Diamond : Left, Right { void tag() override {} };
struct Other { int other; };
struct Multiple : Other, Base { void tag() override {} };
struct Plain { int value; int plain() const { return value; } };
struct ConstRoot : Plain {};
struct Cache { mutable int value = 0; int cached() const { return value; } };
struct ConstCache : Cache {};
using Alias = Plain;
struct AliasRoot : Alias {};
class PrivateRoot : Plain {};
struct ProtectedRoot : protected Plain {};
struct Virtual : virtual Plain {};
union Union { int value; };
struct [[gnu::packed]] Packed { int value; };
namespace { struct Hidden { int value; }; }
template<class T> struct Generic { T value; };
'''
        source = self.work / "fixture.cpp"
        source.write_text(definitions, encoding="utf-8")
        probe = self.run_ok([self.clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", str(source), "-Xclang", "-load", "-Xclang", str(pathlib.Path(library).resolve()),
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe"])
        envelope = self.work / "probe.json"
        envelope.write_text(probe, encoding="utf-8")
        oracle = '#include <iostream>\n' + definitions + r'''
int main() {
 for (int input : {-2147483647-1, -1000, -1, 0, 1, 2, 9, 255, 256, 1000, 2147483647}) {
  Diamond d; Base *left = static_cast<Left*>(&d), *right = static_cast<Right*>(&d);
  left->value = input; right->value = 7;
  if (left == right || left->value != input || right->value != 7) return 2;
  std::cout << "Diamond 0 " << left->value << ' ' << left->read() << " 0\n";
  right->value = input;
  std::cout << "Diamond 1 " << right->value << ' ' << right->read() << " 0\n";
  Multiple m; Base *base = &m; base->value = input;
  std::cout << "Multiple 1 " << base->value << ' ' << base->read() << " 0\n";
  const ConstRoot c{{input}};
  std::cout << "ConstRoot 0 " << c.value << ' ' << c.plain() << " 1\n";
  const ConstCache cache; cache.value = input;
  std::cout << "ConstCache 0 " << cache.value << ' ' << cache.cached() << " 1\n";
 }
}
'''
        rows = [line.split() for line in self.native(oracle).splitlines()]
        self.assertEqual(len(rows), 55)
        cases = []
        for name, index, value, expected, constant in rows:
            path = [int(index), 0] if name == "Diamond" else [int(index)]
            method = "plain" if name == "ConstRoot" else "cached" if name == "ConstCache" else "read"
            cases.append(f'({json.dumps(name)}, {json.dumps(method)}, {path}, {value}, {expected}, {str(bool(int(constant))).lower()})')
        doc = json.loads(probe)
        metadata = doc["metadata"]["declarations"]
        root = next(row for row in metadata if row.get("name") == "Multiple" and row.get("record_complete"))
        mutations = [("record_bases_api", ".string \"wrong\""), ("record_base_count", '.number "0"'),
            ("record_abstract", ".bool true"), ("record_union", ".bool true"),
            ("record_field_count", '.number "1"'), ("record_attribute_count", '.number "1"')]
        for key, value in [("virtual", True), ("access", "private"), ("written_access", "private"),
                           ("type_spelling", "Other"), ("type", {"kind": "builtin", "name": "int"})]:
            changed = json.loads(json.dumps(root["record_bases"]))
            changed[1][key] = value
            def raw_term(value):
                if isinstance(value, bool): return ".bool " + str(value).lower()
                if isinstance(value, str): return ".string " + json.dumps(value)
                if isinstance(value, list): return ".array [" + ",".join(map(raw_term, value)) + "]"
                return ".object [" + ",".join("(" + json.dumps(k) + "," + raw_term(v) + ")" for k,v in value.items()) + "]"
            mutations.append(("record_bases", raw_term(changed)))
        derived = []
        for index, (key, raw) in enumerate(mutations):
            derived.append(f'''  let changed := {{probe with declarations := probe.declarations.map (fun row =>
    if row.id == ⟨{json.dumps(root['id'])}⟩ then
      {{row with raw := replaceField row.raw {json.dumps(key)} ({raw})}} else row)}}
  unless !(ClassHierarchyAdmission.admit changed rootPath).isOk do throw "derived hierarchy refusal {index}"''')
        lean = '''import LeanModels.Cpp
import LeanModels.Cpp.ClassSubobjects
open LeanModels.Cpp
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
load_cpp_probe probe from ''' + json.dumps(str(envelope)) + '''
def artifact : Artifact := {sourceFile := "", sourceSha256 := "", frontend := .null, dependencies := [], ast := probe.ast}
def named (name kind : String) : Except String (List Nat) := do
 let some declaration := artifact.declarations.reverse.find? (fun d => d.name == some name && d.kind == kind &&
   (kind != "CXXRecordDecl" || (artifact.ast.atPath d.path).any (·.field "completeDefinition" == some (.bool true))))
   | throw "absent fixture declaration"
 pure declaration.path
def hierarchyNamed (name : String) : Except String ClassHierarchy := do
 ClassHierarchyAdmission.admit probe (← named name "CXXRecordDecl")
def getterNamed (name : String) : Except String IntegralMemberGetter := do
 admitIntegralMemberGetter probe (← named name "CXXMethodDecl")
def replaceField (raw : Raw) (key : String) (value : Raw) : Raw :=
 match raw with
 | .object fields => .object (fields.map (fun (name, old) => (name, if name == key then value else old)))
 | _ => raw
''' + SUPPLIED + '''
def checks : Except String Unit := do
  let cases : List (String × String × List Nat × Int × Int × Bool) := [''' + ",".join(cases) + ''']
  for (name, method, path, input, expected, constant) in cases do
    unless agrees (← hierarchyNamed name) (← getterNamed method) path input expected constant do
      throw "base path differential"
  for name in ["AliasRoot", "PrivateRoot", "ProtectedRoot"] do
    let _ ← hierarchyNamed name
  for name in ["Base", "Left", "Right", "Virtual", "Union", "Packed", "Hidden", "Generic"] do
    unless !(hierarchyNamed name).isOk do throw ("source hierarchy refusal: " ++ name)
  let rootPath ← named "Multiple" "CXXRecordDecl"
''' + "\n".join(derived) + '''
  pure ()
#eval checks
#guard checks.isOk
'''
        self.lean(lean)
        print("class subobjects: 55 defined native rows, O0/O2 UBSan; 8 source and 11 derived refusals")

    def test_original_abstract_base_getter_in_concrete_objects(self):
        directory = os.environ.get("LEANCPP_TINYXML2_DIR")
        if not directory:
            self.skipTest("set LEANCPP_TINYXML2_DIR")
        corpus = pathlib.Path(directory).resolve()
        example = ROOT / "Examples/cpp/tinyxml2"
        manifest = json.loads((example / "class-subobjects-provenance.json").read_text())
        for name, expected in manifest["source_sha256"].items():
            self.assertEqual(hashlib.sha256((corpus / name).read_bytes()).hexdigest(), expected)
        for name, expected in manifest["literal_sha256"].items():
            self.assertEqual(hashlib.sha256((example / name).read_bytes()).hexdigest(), expected)
        oracle = r'''#include <iostream>
#include "tinyxml2.h"
static_assert(sizeof(int) == 4 && sizeof(long) == 8);
template<class Tag, typename Tag::type Member> struct Access {
 friend typename Tag::type member(Tag) { return Member; }
};
struct NodeTag { using type = int tinyxml2::XMLNode::*; friend type member(NodeTag); };
// N4950 [temp.explicit]: access checking does not apply to these instantiation names.
template struct Access<NodeTag, &tinyxml2::XMLNode::_parseLineNum>;
int main() {
 for (int input : {-2147483647-1, -1000, -1, 0, 1, 2, 9, 255, 256, 1000, 2147483647}) {
  tinyxml2::XMLDocument document;
  if (document.Parse("<root/>") != tinyxml2::XML_SUCCESS) return 2;
  tinyxml2::XMLNode *elementBase = document.RootElement();
  tinyxml2::XMLNode *documentBase = &document;
  if (elementBase == documentBase) return 3;
  for (auto *base : {elementBase, documentBase}) {
   base->*member(NodeTag{}) = input;
   std::cout << (base == elementBase ? "element " : "document ")
             << base->*member(NodeTag{}) << ' ' << base->GetLineNum() << '\n';
  }
 }
}
'''
        rows = [line.split() for line in self.native(oracle,
                ["-I", corpus, corpus / "tinyxml2.cpp"]).splitlines()]
        self.assertEqual(len(rows), 22)
        cases = ",".join(f'({json.dumps(name)}, {value}, {expected})'
                         for name, value, expected in rows)
        self.lean('''import Examples.cpp.tinyxml2.ElementHierarchy
import Examples.cpp.tinyxml2.DocumentHierarchy
import Examples.cpp.tinyxml2.BaseGetLineNum
open LeanModels.Cpp
''' + SUPPLIED + '''
def cases : List (String × Int × Int) := [''' + cases + ''']
#guard cases.all (fun (name, input, expected) =>
 agrees (if name == "element" then Examples.cpp.tinyxml2.ElementHierarchy.hierarchy
   else Examples.cpp.tinyxml2.DocumentHierarchy.hierarchy)
   Examples.cpp.tinyxml2.BaseGetLineNum.getter [0] input expected false)
''')
        for name, expected in manifest["source_sha256"].items():
            self.assertEqual(hashlib.sha256((corpus / name).read_bytes()).hexdigest(), expected)
        print("original class subobjects: 22 defined native rows, O0/O2 UBSan; concrete roots, abstract base")

if __name__ == "__main__":
    unittest.main()
