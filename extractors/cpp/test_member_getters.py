#!/usr/bin/env python3
"""Source-backed member getter admission and native differential controls."""
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
EXAMPLE = ROOT / "Examples/cpp/tinyxml2"
KINDS = ["bool", "char", "signed char", "unsigned char", "short", "unsigned short",
         "int", "unsigned int", "long", "unsigned long", "long long", "unsigned long long"]
SUPPLIED = r'''
def supplied (getter : IntegralMemberGetter) (input : Int) : Option IntegralMemberSnapshot := do
  let (kind, _) ← recordIntegralKind getter.field.type
  let format ← match TargetProfile.lp64.format kind with | .ok value => some value | _ => none
  pure {
    memory := {
      profile := .lp64
      objects := {objects := [
        {duration := .automatic, type := .record getter.owner, phase := .aliveInitialized},
        {duration := .automatic, type := getter.field.type, phase := .aliveInitialized}]}
      values := [none, some ⟨format, input⟩]}
    object := 0, member := 1, field := getter.field.declaration}
def agrees (getter : IntegralMemberGetter) (input expected : Int) : Bool :=
  match supplied getter input, TargetProfile.lp64.format getter.result with
  | some state, .ok format => match getter.invoke state with
    | .ok (memory, result) => memory == state.memory && result == ⟨format, expected⟩
    | _ => false
  | _, _ => false
'''


class MemberGetterTests(unittest.TestCase):
    def setUp(self):
        requested = os.environ.get("LEANCPP_CLANG")
        if not requested:
            self.skipTest("set matching LEANCPP_CLANG")
        self.clang, self.lake = shutil.which(requested), shutil.which("lake")
        self.assertIsNotNone(self.clang)
        self.assertIsNotNone(self.lake)
        version = subprocess.run([self.clang, "--version"], capture_output=True, text=True, timeout=20)
        self.assertEqual(version.returncode, 0, version.stderr)
        self.assertTrue(version.stdout.startswith("clang version 21.1.8 "), version.stdout)
        temp = tempfile.TemporaryDirectory(prefix="cpp-member-getters-")
        self.addCleanup(temp.cleanup)
        self.work = pathlib.Path(temp.name)
        self.env = dict(os.environ, SOURCE_DATE_EPOCH="0", LEAN_NUM_THREADS="1")
        self.env.pop("CCC_OVERRIDE_OPTIONS", None)
        self.env.pop("CCC_ADD_ARGS", None)

    def run_ok(self, command, timeout=240):
        result = subprocess.run(command, cwd=ROOT, env=self.env, capture_output=True,
                                text=True, timeout=timeout)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def native(self, source, extra=()):
        oracle = self.work / "oracle.cpp"
        oracle.write_text(source, encoding="utf-8")
        outputs = []
        for level in ("-O0", "-O2"):
            binary = self.work / level[1:]
            self.run_ok([self.clang, "--no-default-config", "-std=c++23", "-pedantic-errors", level,
                         "-fsanitize=undefined", "-fno-sanitize-recover=all",
                         "-static-libstdc++", "-static-libgcc", str(oracle), *map(str, extra),
                         "-o", str(binary)])
            outputs.append(self.run_ok([str(binary)]))
        self.assertEqual(outputs[0], outputs[1])
        return outputs[0]

    def lean(self, text):
        check = self.work / "Check.lean"
        check.write_text(text, encoding="utf-8")
        self.run_ok([self.lake, "env", "lean", "-j", "1", str(check)])

    def test_compiled_signatures_members_conversions_and_refusals(self):
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not library:
            self.skipTest("set matching LEANCPP_PROBE_LIBRARY")
        definitions = """struct Sample {
 int value; mutable int cache; void *opaque;
 Sample() : value(0), cache(0), opaque(nullptr) {}
 /// A documented getter retains a FullComment after its body in Clang's dump.
 int get() const { return value; }
 int ordinary() { return this->value; }
 int paren() const { return (value); }
 bool flag() const { return value; }
 unsigned char narrow() const { return value; }
 int mutable_get() const { return cache; }
 int argument(int) const { return value; }
 int no_throw() const noexcept { return value; }
 int qualified() const & { return value; }
 int vol() volatile { return value; }
 virtual int virt() const { return value; }
 int call() const { return get(); }
 [[nodiscard]] int attributed() const { return value; }
};
struct Base { int base; };
struct Derived : Base { int value; int inherited() const { return value; } };
struct Bits { int value:4; int bitfield() const { return value; } };
struct Vol { volatile int value; int volatile_field() const { return value; } };
struct [[gnu::packed]] Packed { int value; int packed() const { return value; } };
union Union { int value; int union_get() const { return value; } };
struct Ref { int value; int &reference() { return value; } };
struct Out { int value; int outside() const; };
int Out::outside() const { return value; }
struct OwnConst { const int value; int declared_const() const { return value; } };
"""
        for index, type_ in enumerate(KINDS):
            definitions += f"struct Scalar{index} {{ {type_} value; {type_} read_{index}() const {{ return value; }} }};\n"
        source = self.work / "fixture.cpp"
        source.write_text(definitions, encoding="utf-8")
        probe = self.run_ok([self.clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
                             "-fsyntax-only", str(source), "-Xclang", "-load", "-Xclang",
                             str(pathlib.Path(library).resolve()), "-Xclang", "-plugin", "-Xclang",
                             "leancpp-canonical-probe"])
        envelope = self.work / "probe.json"
        envelope.write_text(probe, encoding="utf-8")
        native = "#include <iostream>\n#include <type_traits>\n#include <climits>\n" + definitions
        native += """static_assert(CHAR_BIT == 8 && CHAR_MIN == -128 && sizeof(int) == 4 && sizeof(long) == 8);
template<class T> void number(T value) {
 if constexpr (std::is_unsigned_v<T>) std::cout << static_cast<unsigned long long>(value);
 else std::cout << static_cast<long long>(value);
}
int main() {
"""
        for index, type_ in enumerate(KINDS):
            native += f'''for (int input : {{-3, 0, 1, 127}}) {{
 Scalar{index} object{{static_cast<{type_}>(input)}};
 std::cout << "read_{index} "; number(object.value); std::cout << ' ';
 number(object.read_{index}()); std::cout << '\\n'; }}\n'''
        for name, member in [("get", "value"), ("ordinary", "value"), ("paren", "value"),
                             ("flag", "value"), ("narrow", "value"), ("mutable_get", "cache")]:
            native += f'''for (int input : {{-2147483647-1, -1000, -1, 0, 1, 255, 256, 2147483647}}) {{
 Sample object; object.{member} = input;
 std::cout << "{name} "; number(object.{member}); std::cout << ' ';
 number(object.{name}()); std::cout << '\\n'; }}\n'''
        for type_, name in [("Out", "outside"), ("OwnConst", "declared_const")]:
            native += f'''for (int input : {{-3, 0, 7, 100}}) {{
 {type_} object{{input}}; std::cout << "{name} "; number(object.value); std::cout << ' ';
 number(object.{name}()); std::cout << '\\n'; }}\n'''
        rows = [line.split() for line in self.native(native + "}\n").splitlines()]
        self.assertEqual(len(rows), 104)
        pairs = ", ".join(f"({json.dumps(name)}, {member}, {expected})" for name, member, expected in rows)
        rejected = ["argument", "no_throw", "qualified", "vol", "virt", "call", "attributed",
                    "inherited", "bitfield", "volatile_field", "packed", "union_get", "reference"]
        document = json.loads(probe)
        declarations = document["metadata"]["declarations"]
        owner = next(row for row in declarations
                     if row["kind"] == "CXXRecordDecl" and row.get("name") == "Sample"
                     and row.get("record_complete"))
        method = next(row for row in declarations
                      if row["kind"] == "CXXMethodDecl" and row.get("name") == "get")
        field = next(row for row in declarations
                     if row["kind"] == "FieldDecl" and row.get("name") == "value"
                     and row.get("field_parent") == owner["id"])
        mutations = [(method["id"], key, value) for key, value in (
            ("method_const", False), ("method_virtual", True), ("method_variadic", True),
            ("method_exception_spec", 1), ("method_parent", document["ast"]["id"]))]
        mutations += [(owner["id"], key, value) for key, value in (
            ("record_complete", False), ("record_field_count", 2),
            ("record_attribute_count", 1), ("record_base_count", 1))]
        mutations += [(field["id"], key, value) for key, value in (
            ("field_index", 2), ("field_mutable", True), ("field_bitfield", True),
            ("field_initializer", True), ("field_parent", document["ast"]["id"]))]
        derived = []
        for index, (handle, key, value) in enumerate(mutations):
            raw = (".bool " + str(value).lower() if isinstance(value, bool) else
                   ".number " + json.dumps(str(value)) if isinstance(value, int) else
                   ".string " + json.dumps(value))
            derived.append(f'''  let changed := {{probe with declarations := probe.declarations.map (fun row =>
    if row.id == ⟨{json.dumps(handle)}⟩ then
      {{row with raw := replaceField row.raw {json.dumps(key)} ({raw})}} else row)}}
  unless (admitIntegralMemberGetter changed getter.occurrence.path).isOk == false do
    throw "getter derived refusal {index}"''')
        self.lean('''import LeanModels.Cpp
open LeanModels.Cpp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
load_cpp_probe probe from ''' + json.dumps(str(envelope)) + '''
def artifact : Artifact := {
  sourceFile := "", sourceSha256 := "", frontend := .null,
  dependencies := [], ast := probe.ast}
def getterNamed (name : String) : Except String IntegralMemberGetter := do
 let some declaration := artifact.declarations.reverse.find? (fun declaration => declaration.name == some name)
   | throw "absent fixture method"
 admitIntegralMemberGetter probe declaration.path
''' + SUPPLIED + f'''
def cases : List (String × Int × Int) := [{pairs}]
#guard cases.all (fun (name, input, expected) => match getterNamed name with
 | .ok getter => agrees getter input expected | .error _ => false)
#guard ({json.dumps(rejected)} : List String).all (fun name => !(getterNamed name).isOk)
def replaceField (raw : Raw) (key : String) (value : Raw) : Raw :=
 match raw with
 | .object fields => .object (fields.map (fun (name, old) => (name, if name == key then value else old)))
 | _ => raw
def derivedChecks : Except String Unit := do
  let getter ← getterNamed "get"
''' + "\n".join(derived) + '''
  pure ()
#eval derivedChecks
#guard derivedChecks.isOk
''')
        print("member getters: 104 defined native rows, 12 integral types, -O0/-O2 UBSan; "
              "13 source and 14 derived evidence refusals")

    def test_original_getters_use_independent_member_state(self):
        directory = os.environ.get("LEANCPP_TINYXML2_DIR")
        if not directory:
            self.skipTest("set LEANCPP_TINYXML2_DIR")
        corpus = pathlib.Path(directory).resolve()
        manifest = json.loads((EXAMPLE / "member-getters-provenance.json").read_text())
        for name, expected in manifest["source_sha256"].items():
            self.assertEqual(hashlib.sha256((corpus / name).read_bytes()).hexdigest(), expected)
        for name, expected in manifest["literal_sha256"].items():
            self.assertEqual(hashlib.sha256((EXAMPLE / name).read_bytes()).hexdigest(), expected)
        oracle = r'''#include <iostream>
#include "tinyxml2.h"
template<class Tag, typename Tag::type Member> struct Access {
 friend typename Tag::type member(Tag) { return Member; }
};
struct NodeTag { using type = int tinyxml2::XMLNode::*; friend type member(NodeTag); };
struct AttributeTag { using type = int tinyxml2::XMLAttribute::*; friend type member(AttributeTag); };
// N4950 [temp.explicit]: usual access checking does not apply to these names.
template struct Access<NodeTag, &tinyxml2::XMLNode::_parseLineNum>;
template struct Access<AttributeTag, &tinyxml2::XMLAttribute::_parseLineNum>;
int main() {
 for(int input : {-2147483647-1, -1000, -1, 0, 1, 2, 9, 255, 256, 1000, 2147483647}) {
  tinyxml2::XMLDocument document;
  if(document.Parse("<root key='value'/>") != tinyxml2::XML_SUCCESS) return 2;
  tinyxml2::XMLNode *node = document.FirstChild();
  auto *attribute = const_cast<tinyxml2::XMLAttribute*>(document.RootElement()->FirstAttribute());
  node->*member(NodeTag{}) = input;
  attribute->*member(AttributeTag{}) = input;
  std::cout << "node " << node->*member(NodeTag{}) << ' ' << node->GetLineNum() << '\n';
  std::cout << "attribute " << attribute->*member(AttributeTag{}) << ' ' << attribute->GetLineNum() << '\n';
 }
}
'''
        rows = [line.split() for line in self.native(oracle, ["-I", corpus, corpus / "tinyxml2.cpp"]).splitlines()]
        self.assertEqual(len(rows), 22)
        pairs = ", ".join(f"({json.dumps(name)}, {member}, {expected})" for name, member, expected in rows)
        self.lean('''import Examples.cpp.tinyxml2.NodeGetLineNum
import Examples.cpp.tinyxml2.AttributeGetLineNum
open LeanModels.Cpp
''' + SUPPLIED + f'''
def cases : List (String × Int × Int) := [{pairs}]
#guard cases.all (fun (name, input, expected) =>
 agrees (if name == "node" then Examples.cpp.tinyxml2.NodeGetLineNum.getter
   else Examples.cpp.tinyxml2.AttributeGetLineNum.getter) input expected)
''')
        for name, expected in manifest["source_sha256"].items():
            self.assertEqual(hashlib.sha256((corpus / name).read_bytes()).hexdigest(), expected)
        print("original member getters: 22 defined rows, independent member writes/reads, -O0/-O2 UBSan")

    def test_enum_representation_value_differential(self):
        """Compare an explicit enum representation/value boundary with C++."""
        source = r'''
#include <iostream>
enum Error : unsigned int { zero = 0u, one = 1u, top = 4294967295u };
struct Sample {
 Error value;
 Error get() const { return value; }
};
int main() {
 for (unsigned int input : {0u, 1u, 7u, 4294967295u}) {
  Sample object{static_cast<Error>(input)};
  std::cout << input << ' ' << static_cast<unsigned int>(object.get()) << '\n';
 }
}
'''
        rows = [line.split() for line in self.native(source).splitlines()]
        self.assertEqual(rows, [[value, value] for value in
                                ["0", "1", "7", "4294967295"]])
        pairs = ", ".join(f"({value}, {expected})" for value, expected in rows)
        self.lean('''import LeanModels.Cpp.MemberCalls
open LeanModels.Cpp
private def h (value : String) : FrontendHandle := ⟨value⟩
private def access : IntegralMemberThisFieldAccess := {
  method := h "method", definition := h "method", owner := h "owner", field := h "field",
  name := "value", receiverType := "Sample *", fieldType := "Error", methodName := "get"}
private def profile : IntegralMemberEnumProfile := {
  field := h "field", enum := h "enum", name := "Error", constantCount := 3,
  explicitValueCount := 3, underlyingType := some "unsigned int"}
private def representation : IntegralMemberEnumRepresentation :=
  (IntegralMemberEnumRepresentation.withOracle profile .unsignedInt).toOption.getD
    {profile, underlying := .unsignedInt}
private def hierarchy : ClassHierarchy := {
  root := h "owner",
  classes := [{declaration := h "owner", isAbstract := false, bases := [], fields := [h "field"], friends := [], name := "Sample"}]}
private def callSyntax : IntegralMemberCallSyntax := {
  method := h "method", receiver := h "receiver", receiverType := "Sample *",
  resultType := "Error", name := "get", canonicalMethod := h "method"}
private def memory (input : Int) : IntegralObjectStore := {
  profile := .lp64,
  objects := {objects := [{duration := .automatic, type := .record (h "owner"), phase := .aliveInitialized}, {duration := .automatic, type := .builtin .unsignedInt, phase := .aliveInitialized}]},
  values := [none, some ⟨.unsigned 32, input⟩]}
private def projection (input : Int) : ClassReceiverProjection := {
  hierarchy, objects := [0], receiverPath := [],
  snapshot := {memory := memory input, object := 0, member := 1, field := h "field"}}
def cases : List (Int × Int) := [''' + pairs + ''']
#guard cases.all (fun (input, expected) =>
  match IntegralMemberEnumCall.bind callSyntax access representation (h "receiver")
      (projection input) with
  | .ok call => match call.invoke with
    | .ok (_, value) => value.value.value == expected
    | .error _ => false
  | .error _ => false)
''')
        print("enum representation: 4 native rows, -O0/-O2 UBSan; explicit unsigned underlying type")

    def test_enum_field_mutation_differential(self):
        """Compare writable enum-field assignment and readback with C++."""
        source = r'''
#include <iostream>
enum Error : unsigned int { zero = 0u, one = 1u, top = 4294967295u };
struct Sample {
 Error value;
 void set(Error next) { value = next; }
 Error get() const { return value; }
};
int main() {
 Sample object{static_cast<Error>(7u)};
 for (unsigned int input : {0u, 1u, 7u, 4294967295u}) {
  object.set(static_cast<Error>(input));
  std::cout << input << ' ' << static_cast<unsigned int>(object.get()) << '\n';
 }
}
'''
        rows = [line.split() for line in self.native(source).splitlines()]
        self.assertEqual(rows, [[value, value] for value in
                                ["0", "1", "7", "4294967295"]])
        pairs = ", ".join(f"({value}, {expected})" for value, expected in rows)
        self.lean('''import LeanModels.Cpp.MemberCalls
open LeanModels.Cpp
private def h (value : String) : FrontendHandle := ⟨value⟩
private def access : IntegralMemberThisFieldAccess := {
  method := h "method", definition := h "method", owner := h "owner", field := h "field",
  name := "value", receiverType := "Sample *", fieldType := "Error", methodName := "get"}
private def profile : IntegralMemberEnumProfile := {
  field := h "field", enum := h "enum", name := "Error", constantCount := 3,
  explicitValueCount := 3, underlyingType := some "unsigned int"}
private def representation : IntegralMemberEnumRepresentation :=
  (IntegralMemberEnumRepresentation.withOracle profile .unsignedInt).toOption.getD
    {profile, underlying := .unsignedInt}
private def setterMethod : IntegralMemberMethodProfile := {
  method := h "method", resultType := .void,
    parameters := [.enumeration (h "enum")], isConst := false,
    isStatic := false, bodyKind := "CompoundStmt"}
private def setterBody : IntegralMemberMethodBody := {
  canonical := h "method", definition := h "method", bodyKind := "CompoundStmt"}
private def setter : IntegralMemberEnumSetter := {
  method := setterMethod,
  body := setterBody,
  owner := h "owner", field := h "field", parameter := h "parameter",
  fieldName := "value", fieldType := "Error", parameterType := "Error", representation}
private def callSyntax : IntegralMemberCallSyntax := {
  method := h "method", receiver := h "receiver", receiverType := "Sample *",
  resultType := "void", name := "set", canonicalMethod := h "method"}
private def hierarchy : ClassHierarchy := {
  root := h "owner",
  classes := [{declaration := h "owner", isAbstract := false, bases := [], fields := [h "field"], friends := [], name := "Sample"}]}
private def memory (input : Int) : IntegralObjectStore := {
  profile := .lp64,
  objects := {objects := [{duration := .automatic, type := .record (h "owner"), phase := .aliveInitialized}, {duration := .automatic, type := .builtin .unsignedInt, phase := .aliveInitialized}]},
  values := [none, some ⟨.unsigned 32, input⟩]}
private def projection (input : Int) : ClassReceiverProjection := {
  hierarchy, objects := [0], receiverPath := [],
  snapshot := {memory := memory input, object := 0, member := 1, field := h "field"}}
def cases : List (Int × Int) := [''' + pairs + ''']
#guard cases.all (fun (input, expected) =>
  let before := projection 7
  let argument : IntegralMemberEnumValue :=
    {representation := setter.representation, value := ⟨.unsigned 32, input⟩}
  match IntegralMemberEnumSetterCall.bind callSyntax setter access (h "receiver")
      argument before with
  | .ok call =>
      match call.invoke with
      | .ok store =>
          let after := {before with snapshot := {before.snapshot with memory := store}}
          match IntegralMemberEnumValue.read access representation after with
          | .ok (_, value) => value.value.value == expected
          | .error _ => false
      | .error _ => false
  | .error _ => false)
''')
        print("enum mutation: 4 native assignment/readback rows, -O0/-O2 UBSan; explicit unsigned underlying type")


if __name__ == "__main__":
    unittest.main()
