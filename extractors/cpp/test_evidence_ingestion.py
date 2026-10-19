#!/usr/bin/env python3
"""Bounded loading, inspection and source-local function declaration forms.

Callable checks evaluate only admitted integral statement bodies; no
whole-program execution or entity/linkage admission is established here.

LEANCPP_TEST_LEAN=1 enables the built Lean loader checks. The compiler check
additionally requires an explicit matching LEANCPP_CLANG and
LEANCPP_PROBE_LIBRARY. No CI registration or probe build occurs here.
"""

import copy
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest


REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
SOURCE = """int later(int);
int later(int value) { return value; }
[[deprecated]] int attributed() { return 2; }
struct Box { int method() { return 3; } };
"""


def function_row():
    result = {
        "id": "0x2", "kind": "FunctionDecl", "name": "sample",
        "canonical": "0x2", "previous": None,
        "semantic_context": "0x1", "lexical_context": "0x1",
        "implicit": False, "dependent_context": False, "owning_module": None,
        "definition": False,
        "definition_api": "FunctionDecl.isThisDeclarationADefinition",
        "body_present": False, "defaulted": False, "deleted_as_written": False,
        "function_has_skipped_body": False, "function_will_have_body": False,
        "function_has_defining_attr": False, "function_late_template_parsed": False,
        "function_explicitly_defaulted": False, "function_attribute_count": 0,
        "function_attribute_count_api": "Decl.hasAttrs/Decl.getAttrs.size",
        "own_body_kind": None, "own_body_owner": None,
        "own_body_api": "FunctionDecl.getBody",
    }
    result.update({
        "function_has_skipped_body_api": "FunctionDecl.hasSkippedBody",
        "function_will_have_body_api": "FunctionDecl.willHaveBody",
        "function_has_defining_attr_api": "FunctionDecl.hasDefiningAttr",
        "function_late_template_parsed_api": "FunctionDecl.isLateTemplateParsed",
        "function_explicitly_defaulted_api": "FunctionDecl.isExplicitlyDefaulted",
    })
    return result


def document(rows=None):
    return {
        "metadata": {
            "schema_version": "cpp-canonical-probe-0.3",
            "compiled_frontend": "21.1.8",
            "runtime_frontend": "clang version 21.1.8",
            "llvm_headers": "21.1.8",
            "declarations": rows if rows is not None else [function_row()],
        },
        "ast": {"id": "0x1", "kind": "TranslationUnitDecl", "inner": []},
    }


class EvidenceIngestionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if os.environ.get("LEANCPP_TEST_LEAN") != "1":
            raise unittest.SkipTest("set LEANCPP_TEST_LEAN=1 for built Lean loader checks")
        cls.lake = shutil.which("lake")
        if cls.lake is None:
            raise RuntimeError("Lean loader checks require lake on PATH")

    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-evidence-ingestion-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)

    def run_loader(self, contents, guards="", options="", timeout=60):
        probe_path = self.root / "probe.json"
        if isinstance(contents, bytes):
            probe_path.write_bytes(contents)
        else:
            probe_path.write_text(contents, encoding="utf-8")
        lean_path = self.root / "Check.lean"
        lean_path.write_text(
            "import LeanModels.Cpp\n"
            "open LeanModels.Cpp\n"
            "namespace CppProbeIngestionFixture\n"
            + (options + "\n" if options else "")
            + "load_cpp_probe evidence from " + json.dumps(str(probe_path)) + "\n"
            + guards + "\nend CppProbeIngestionFixture\n",
            encoding="utf-8",
        )
        return subprocess.run(
            [self.lake, "env", "lean", "-j", "1", str(lean_path)], cwd=REPO_ROOT,
            capture_output=True, text=True, timeout=timeout,
        )

    def assert_accepts(self, contents, guards="", options="", timeout=60):
        result = self.run_loader(contents, guards, options, timeout)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def assert_refuses(self, contents):
        result = self.run_loader(contents)
        self.assertNotEqual(result.returncode, 0, "invalid probe evidence was admitted")
        self.assertIn("load_cpp_probe:", result.stdout + result.stderr)

    def test_literals_preserve_integer_lexemes(self):
        contents = json.dumps(document()).replace(
            '"inner": []', '"inner": [], "integer": 9007199254740993, "negative_zero": -0',
        )
        self.assert_accepts(contents, """#guard evidence.functions.length == 1
#guard evidence.ast.field "integer" == some (.number "9007199254740993")
#guard evidence.ast.field "negative_zero" == some (.number "-0")
#guard (evidence.functions.head?.bind (·.functionShape)).map (·.attributeCount) == some 0
""")

    def test_repeated_conflicting_rows_remain_ordered_literal_evidence(self):
        first = function_row()
        second = copy.deepcopy(first)
        second["definition"] = True
        self.assert_accepts(json.dumps(document([first, second])), """
#guard evidence.declarations.length == 2
#guard evidence.functions.length == 2
#guard evidence.declarations.map (·.ordinal) == [0, 1]
#guard evidence.functions.map (fun row => row.functionShape.map (·.definition)) == [some false, some true]
""")

    def test_unsupported_rows_keep_raw_fields(self):
        row = function_row()
        row.update(kind="CXXMethodDecl", future={"nested": [None, True, "retained"]})
        row["function_attribute_count"] = "untyped method payload"
        self.assert_accepts(json.dumps(document([row])), """
#guard evidence.declarations.length == 1
#guard evidence.functions.isEmpty
#guard (evidence.declarations.head?.map (·.raw)).bind (fun raw => raw.field "future") ==
  some (.object [("nested", .array [.null, .bool true, .string "retained"])])
""")

    def test_unsupported_shapes_are_not_semantic_admission(self):
        row = function_row()
        row.update(function_has_skipped_body=True, function_has_defining_attr=True,
                   function_attribute_count=3, own_body_kind="FutureStmt",
                   own_body_owner="0xdead")
        self.assert_accepts(json.dumps(document([row])), """
#guard evidence.functions.length == 1
#guard (evidence.functions.head?.bind (·.functionShape)).map (·.ownBodyKind) == some (some "FutureStmt")
""")

    def test_runtime_build_suffix_is_not_a_version_prefix_guess(self):
        fixture = document()
        fixture["metadata"]["runtime_frontend"] = "clang version 21.1.8 (distribution build)"
        self.assert_accepts(json.dumps(fixture))
        fixture["metadata"]["runtime_frontend"] = "clang version 21.1.80"
        self.assert_refuses(json.dumps(fixture))

    def test_missing_and_null_are_distinct(self):
        row = function_row()
        self.assert_accepts(json.dumps(document([row])))
        del row["own_body_owner"]
        self.assert_refuses(json.dumps(document([row])))

    def test_wrong_api_and_flag_types_refuse(self):
        for field, value in (
            ("own_body_api", "some-body-getter"),
            ("function_has_skipped_body", 0),
            ("function_attribute_count", False),
            ("implicit", 0),
        ):
            with self.subTest(field=field):
                row = function_row()
                row[field] = value
                self.assert_refuses(json.dumps(document([row])))

    def test_strict_numeric_count_tokens_refuse(self):
        serialized = json.dumps(document())
        for token in ("-1", "1.0", "1e0", "01"):
            with self.subTest(token=token):
                contents = serialized.replace('"function_attribute_count": 0',
                                              '"function_attribute_count": ' + token)
                self.assert_refuses(contents)

    def test_noninteger_opaque_ast_tokens_refuse(self):
        serialized = json.dumps(document())
        for token in ("0.125", "5e+03"):
            with self.subTest(token=token):
                contents = serialized.replace('"inner": []', '"inner": [], "opaque": ' + token)
                self.assert_refuses(contents)

    def test_duplicate_keys_refuse_before_any_first_or_last_row_wins(self):
        serialized = json.dumps(document())
        for duplicate in ('"id": "0x3", "id": "0x2"',
                          '"\\u0069d": "0x3", "id": "0x2"'):
            with self.subTest(duplicate=duplicate):
                self.assert_refuses(serialized.replace('"id": "0x2"', duplicate))

    def test_invalid_unicode_refuses(self):
        contents = json.dumps(document()).replace('"sample"', '"\\ud800"')
        self.assert_refuses(contents)

    def test_invalid_utf8_refuses_without_replacement(self):
        contents = json.dumps(document()).encode("utf-8").replace(b'"sample"', b'"\xff"')
        result = self.run_loader(contents)
        self.assertNotEqual(result.returncode, 0, "invalid UTF-8 was decoded as evidence")
        self.assertIn("UTF-8", result.stdout + result.stderr)

    def test_duplicate_literal_declaration_name_refuses(self):
        result = self.run_loader(json.dumps(document()),
                                 "load_cpp_probe evidence from " +
                                 json.dumps(str(self.root / "probe.json")))
        self.assertNotEqual(result.returncode, 0, "existing Lean declaration was overwritten")
        self.assertIn("already declared", result.stdout + result.stderr)

    def test_old_schema_refuses_without_shape_defaults(self):
        fixture = document()
        fixture["metadata"]["schema_version"] = "cpp-canonical-probe-0.2"
        self.assert_refuses(json.dumps(fixture))

    def test_actual_pinned_compiler_probe_loads_as_literal(self):
        requested = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            self.skipTest("set matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY")
        clang = shutil.which(requested)
        probe_library = pathlib.Path(library).resolve()
        self.assertIsNotNone(clang, "selected compiler must exist")
        self.assertTrue(probe_library.is_file(), "selected probe library must exist")
        source = self.root / "input.cpp"
        source.write_text(SOURCE, encoding="utf-8")
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        result = subprocess.run([
            clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", "-x", "c++", str(source),
            "-Xclang", "-load", "-Xclang", str(probe_library),
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
        ], cwd=self.root, env=environment, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        probe = json.loads(result.stdout)
        function_count = sum(row["kind"] == "FunctionDecl"
                             for row in probe["metadata"]["declarations"])
        self.assertEqual(function_count, 3)
        self.assert_accepts(result.stdout, """#guard evidence.functions.length == 3
#guard evidence.declarations.length == """ + str(len(probe["metadata"]["declarations"])) + """
#guard evidence.functions.map (fun row => row.functionShape.map (·.bodyPresent)) == [some false, some true, some true]
#guard evidence.functions.map (fun row => row.functionShape.map (·.attributeCount)) == [some 0, some 0, some 1]
#guard match parseValidatedTypeEvidence evidence with
  | .ok rows => !rows.isEmpty
  | .error _ => false
#guard match parseValidatedBinaryExpressionEvidence evidence with
  | .ok rows => rows.isEmpty
  | .error _ => false
""")

    def test_actual_pinned_compiler_expression_evidence_loads(self):
        requested = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            self.skipTest("set matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY")
        clang = shutil.which(requested)
        self.assertIsNotNone(clang, "selected compiler must exist")
        source = self.root / "expression.cpp"
        source.write_text("short arithmetic(short left, short right) { return left + right; }\n",
                          encoding="utf-8")
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        result = subprocess.run([
            clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", "-x", "c++", str(source),
            "-Xclang", "-load", "-Xclang", str(pathlib.Path(library).resolve()),
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
        ], cwd=self.root, env=environment, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        probe = json.loads(result.stdout)
        self.assertEqual([row["operator"] for row in probe["metadata"]["expression_evidence"]], ["+"])
        self.assert_accepts(result.stdout, """#guard match parseValidatedBinaryExpressionEvidence evidence with
  | .ok [row] => match validateBinaryIntegralTyping TargetProfile.lp64 row with
    | .ok _ => row.operands.all (fun operand => operand.sourceType == .builtin .short &&
        operand.type == .builtin .int)
    | .error _ => false
  | .ok _ => false
  | .error _ => false
""")

    def run_inspector(self, fixture, *paths):
        probe_path = self.root / "inspection.json"
        probe_path.write_text(json.dumps(fixture), encoding="utf-8")
        return subprocess.run(
            [self.lake, "env", "lean", "-j", "1", "--run", str(REPO_ROOT / "extractors/cpp/inspect_probe.lean"),
             str(probe_path), *paths], cwd=REPO_ROOT, capture_output=True, text=True, timeout=60,
        )

    def test_runtime_inspector_preserves_refusals(self):
        result = self.run_inspector(document(), "root")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("no artifact provenance, literal compilation or execution admission", result.stdout)
        self.assertIn("metadata=1 occurrences=1 functions=1", result.stdout)
        self.assertIn("canonical-target: REFUSE canonical evidence missing", result.stdout)
        self.assertIn("linkage: REFUSE linkage evidence is not applicable", result.stdout)

    def test_runtime_inspector_keeps_repeated_occurrence_candidates(self):
        row = function_row()
        row.update(linkage_internal="External", linkage_formal="External", language_linkage="C++")
        root = copy.deepcopy(row)
        root.update(id="0x1", kind="TranslationUnitDecl", canonical="0x1",
                    semantic_context=None, lexical_context=None)
        fixture = document([root, row])
        fixture["ast"]["inner"] = [{"id": "0x2", "kind": "FunctionDecl"}] * 2
        result = self.run_inspector(fixture, "0")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        for expected in (
            "metadata=2 occurrences=3 functions=1", "canonical-target: OK 2",
            "canonical-root: OK present", "canonical-chain: OK 1",
            "semantic-chain: OK 1", "lexical-chain: OK 1",
            "function-definition: OK false", "linkage: OK External/External/(some C++)",
        ):
            self.assertIn(expected, result.stdout)

    def test_actual_compiler_local_function_source_admission(self):
        requested = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            self.skipTest("set matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY")
        clang = shutil.which(requested)
        self.assertIsNotNone(clang, "selected compiler must exist")
        self.assertTrue(pathlib.Path(library).is_file(), "selected probe library must exist")
        source = self.root / "local.cpp"
        source.write_text("""int prototype(int);
int prototype(int value) { return value; }
int try_body(int value) try { return value; } catch (...) { return -1; }
int deleted(int) = delete;
namespace scope { int qualified(int); }
int scope::qualified(int value) { return value; }
namespace scope { int reopened() { return 3; } }
namespace { int anonymous() { return 4; } }
inline namespace version { int inlined() { return 5; } }
extern "C" { int linked() { return 6; } }
[[deprecated]] int attributed() { return 7; }
template<class Type> Type templated(Type value) { return value; }
struct Box { int method() { return 8; } };
""", encoding="utf-8")
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        result = subprocess.run([
            clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", "-x", "c++", str(source),
            "-Xclang", "-load", "-Xclang", str(pathlib.Path(library).resolve()),
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
        ], cwd=self.root, env=environment, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        probe = json.loads(result.stdout)
        expected = {
            "prototype": [False, True], "try_body": [True], "deleted": [True],
            "qualified": [False, True], "reopened": [True],
            "anonymous": [None], "inlined": [None], "linked": [None],
            "attributed": [None], "templated": [None], "method": [None],
        }
        guards = []
        counts = dict.fromkeys(expected, 0)
        pending = [(probe["ast"], [])]
        while pending:
            node, path = pending.pop()
            name = node.get("name")
            if node.get("kind") in ("FunctionDecl", "CXXMethodDecl") and name in expected:
                verdict = expected[name][counts[name]]
                counts[name] += 1
                call = "admitLocalFunctionDeclaration evidence " + str(path)
                if verdict is None:
                    guards.append("#guard (" + call + ") matches .error _")
                else:
                    guards.append("#guard (" + call + ").map (·.form.definesEntity) matches .ok "
                                  + str(verdict).lower())
            children = node.get("inner", [])
            pending.extend((child, path + [index])
                           for index, child in reversed(list(enumerate(children))))
        self.assertEqual(counts, {name: len(values) for name, values in expected.items()})
        self.assert_accepts(result.stdout, "\n".join(guards))

    def test_actual_compiler_typed_callable_body_admission(self):
        requested = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            self.skipTest("set matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY")
        clang = shutil.which(requested)
        self.assertIsNotNone(clang, "selected compiler must exist")
        self.assertTrue(pathlib.Path(library).is_file(), "selected probe library must exist")
        source = self.root / "callable.cpp"
        source.write_text("""int identity(int value) { return value; }
int add(int left, int right) { return left + right; }
int branch(int value) { if (value) return value; return 0; }
int loop(int value) { while (value) return value; return 0; }
int unary(int value) { return -value; }
int compare(int value) { if (value > 0) return 1; return 0; }
bool logical(int value) { return !value; }
int block_identity(int value) { { { return value; } } }
int empty_blocks(int value) { {} { {} } return value; }
int direct_for(int value) { for (value = 0; value < 3; ++value) { continue; } return value; }
""", encoding="utf-8")
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        result = subprocess.run([
            clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", "-x", "c++", str(source),
            "-Xclang", "-load", "-Xclang", str(pathlib.Path(library).resolve()),
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
        ], cwd=self.root, env=environment, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        probe = json.loads(result.stdout)
        paths = {}
        pending = [(probe["ast"], [])]
        while pending:
            node, path = pending.pop()
            if node.get("kind") == "FunctionDecl" and node.get("name") in {
                "identity", "add", "branch", "loop", "unary", "compare", "logical",
                "block_identity", "empty_blocks", "direct_for",
            }:
                paths[node["name"]] = path
            children = node.get("inner", [])
            pending.extend((child, path + [index])
                           for index, child in reversed(list(enumerate(children))))
        self.assertEqual(set(paths), {
            "identity", "add", "branch", "loop", "unary", "compare", "logical",
            "block_identity", "empty_blocks", "direct_for"})
        guards = []
        for name in ("identity", "add"):
            guards.append(
                "#guard (admitCallableFunctionFromProbe evidence TargetProfile.lp64 "
                + str(paths[name]) + ").isOk"
            )
        guards.append(
            "#guard (admitCallableFunctionFromProbe evidence TargetProfile.lp64 "
            + str(paths["branch"]) + ").isOk"
        )
        guards.append(
            "#guard (admitCallableFunctionFromProbe evidence TargetProfile.lp64 "
            + str(paths["loop"]) + ").isOk"
        )
        guards.append(
            "#guard (admitCallableFunctionFromProbe evidence TargetProfile.lp64 "
            + str(paths["unary"]) + ").isOk"
        )
        guards.append(
            "#guard (admitCallableFunctionFromProbe evidence TargetProfile.lp64 "
            + str(paths["compare"]) + ").isOk"
        )
        for name, pattern in {
            "block_identity": ".block (.block (.block (.return_ _)))",
            "empty_blocks": ".block (.sequence (.sequence (.block .skip) (.block (.block .skip))) (.return_ _))",
            "direct_for": ".block (.sequence (.forLoop (.assign _ _) _ (.expression _) (.block .continue_)) (.return_ _))",
        }.items():
            admission = ("admitCallableFunctionFromProbe evidence TargetProfile.lp64 "
                         + str(paths[name]))
            guards.append(f"""#guard match {admission} with
  | .ok function => match function.body with
    | {pattern} => true
    | _ => false
  | .error _ => false""")
        self.assert_accepts(json.dumps(probe), "\n".join(guards))

    def test_actual_compiler_local_declarations_remain_loud(self):
        requested = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            self.skipTest("set matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY")
        clang = shutil.which(requested)
        self.assertIsNotNone(clang, "selected compiler must exist")
        self.assertTrue(pathlib.Path(library).is_file(), "selected probe library must exist")
        source = self.root / "declarations.cpp"
        functions = {
            "local_copy": "int local = value; return local;",
            "local_direct": "int local(value); return local;",
            "local_list": "int local{value}; return local;",
            "local_copy_list": "int local = {value}; return local;",
            "local_zero": "int local{}; return local;",
            "local_default": "int local; local = value; return local;",
            "local_const": "const int local = value; return local;",
            "local_auto": "auto local = value; return local;",
            "local_chain": "int first = value, second = first; return second;",
            "local_shadow": "int local = value; { int local = 3; ++local; } return local;",
            "local_self": "int result = value; { int local = local; } return result;",
            "local_for": "for (int local = 0; local < value; ++local) { break; } return value;",
            "local_static": "static int local = value; return local;",
            "local_thread": "thread_local int local = value; return local;",
            "local_volatile": "volatile int local = value; return local;",
            "local_reference": "int &local = value; return local;",
            "local_array": "int local[1] = {value}; return local[0];",
            "local_alias": "using Number = int; Number local = value; return local;",
        }
        source.write_text("\n".join(
            "int " + name + "(int value) { " + body + " }"
            for name, body in functions.items()), encoding="utf-8")
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        result = subprocess.run([
            clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", "-x", "c++", str(source),
            "-Xclang", "-load", "-Xclang", str(pathlib.Path(library).resolve()),
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
        ], cwd=self.root, env=environment, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        probe = json.loads(result.stdout)
        paths = {}
        function_nodes = {}
        variables = []
        pending = [(probe["ast"], [])]
        while pending:
            node, path = pending.pop()
            if node.get("kind") == "FunctionDecl" and node.get("name") in functions:
                paths[node["name"]] = path
                function_nodes[node["name"]] = node
            if node.get("kind") == "VarDecl":
                variables.append(node)
            pending.extend((child, path + [index])
                           for index, child in enumerate(node.get("inner", [])))
        self.assertEqual(set(paths), set(functions))
        type_rows = {row["occurrence"]: row for row in probe["metadata"]["type_evidence"]}
        ordinary = [node for node in variables if node.get("type", {}).get("qualType") == "int"]
        self.assertTrue(ordinary)
        for node in ordinary:
            self.assertEqual(type_rows[node["id"]]["type"], {"kind": "builtin", "name": "int"})

        def references(root):
            result = []
            pending = [root]
            while pending:
                node = pending.pop()
                if node.get("kind") == "DeclRefExpr":
                    result.append(node["referencedDecl"]["id"])
                pending.extend(node.get("inner", []))
            return result

        bodies = {name: next(child for child in function["inner"]
                             if child.get("kind") == "CompoundStmt")
                  for name, function in function_nodes.items()}
        shadow = bodies["local_shadow"]["inner"]
        outer = shadow[0]["inner"][0]
        inner = shadow[1]["inner"][0]["inner"][0]
        self.assertNotEqual(outer["id"], inner["id"])
        self.assertEqual(references(shadow[1]), [inner["id"]])
        self.assertEqual(references(shadow[2]), [outer["id"]])
        self_scope = bodies["local_self"]["inner"][1]
        self_variable = self_scope["inner"][0]["inner"][0]
        self.assertEqual(references(self_scope), [self_variable["id"]])
        first, second = bodies["local_chain"]["inner"][0]["inner"]
        self.assertEqual(references(second), [first["id"]])
        guards = []
        for name in sorted(functions):
            guards.append(
                "#guard match admitCallableFunctionFromProbe evidence TargetProfile.lp64 "
                + str(paths[name]) + " with\n"
                '| .error reason => reason == "callable: unsupported statement DeclStmt"\n'
                "| .ok _ => false")
        self.assert_accepts(json.dumps(probe), "\n".join(guards),
                            options="set_option maxRecDepth 100000 in")

    def test_actual_compiler_switch_continue_admitted(self):
        requested = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            self.skipTest("set matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY")
        clang = shutil.which(requested)
        self.assertIsNotNone(clang, "selected compiler must exist")
        self.assertTrue(pathlib.Path(library).is_file(), "selected probe library must exist")
        source = self.root / "switch.cpp"
        source.write_text("""int switch_while(int value) {
    while (value) { switch (value) { case 1: --value; continue; default: return value; } }
    return value;
}
int switch_for(int value) {
    for (value = 0; value < 3; ++value) { switch (value) { default: continue; } }
    return value;
}
int switch_do(int value) {
    do { switch (value) { default: --value; continue; } } while (value);
    return value;
}
int switch_nested(int value) {
    switch (value) { default: while (value) { --value; continue; } }
    return value;
}
int switch_break(int value) {
    switch (value) { case 0: break; case 1: return 4; default: return 5; }
    return value;
}
""", encoding="utf-8")
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        result = subprocess.run([
            clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", "-x", "c++", str(source),
            "-Xclang", "-load", "-Xclang", str(pathlib.Path(library).resolve()),
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
        ], cwd=self.root, env=environment, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        probe = json.loads(result.stdout)
        expected = {"switch_while", "switch_for", "switch_do", "switch_nested", "switch_break"}
        paths = {}
        pending = [(probe["ast"], [])]
        while pending:
            node, path = pending.pop()
            if node.get("kind") == "FunctionDecl" and node.get("name") in expected:
                paths[node["name"]] = path
            children = node.get("inner", [])
            pending.extend((child, path + [index])
                           for index, child in reversed(list(enumerate(children))))
        self.assertEqual(set(paths), expected)
        guards = []
        for name in sorted(expected):
            admission = ("admitCallableFunctionFromProbe evidence TargetProfile.lp64 "
                         + str(paths[name]))
            guards.append("#guard (" + admission + ").isOk")
        self.assert_accepts(json.dumps(probe), "\n".join(guards))

    def test_callable_argument_conversions_match_compiled_clang(self):
        requested = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            self.skipTest("set matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY")
        clang = shutil.which(requested)
        self.assertIsNotNone(clang, "selected compiler must exist")
        probe_library = pathlib.Path(library).resolve()
        self.assertTrue(probe_library.is_file(), "selected probe library must exist")
        destinations = (
            ("int", "signed_identity", ".signed 32"),
            ("unsigned int", "unsigned_identity", ".unsigned 32"),
            ("short", "short_identity", ".signed 16"),
            ("unsigned short", "ushort_identity", ".unsigned 16"),
            ("bool", "bool_identity", ".boolean"),
        )
        return_casts = (
            ("bool", "to_bool", "int"),
            ("int", "to_int", "bool"),
            ("short", "to_short", "int"),
        )
        compound_cases = (
            ("-=", "compound_subtract", ((-7, 3), (0, 7), (7, 3))),
            ("*=", "compound_multiply", ((-7, 3), (0, 7), (7, 3))),
            ("/=", "compound_divide", ((-7, 3), (7, 3), (7, 2))),
            ("%=", "compound_remainder", ((-7, 3), (7, 3), (7, 2))),
            ("&=", "compound_bit_and", ((5, 3), (7, 2), (8, 1))),
            ("|=", "compound_bit_or", ((5, 3), (7, 2), (8, 1))),
            ("^=", "compound_bit_xor", ((5, 3), (7, 2), (8, 1))),
            ("<<=", "compound_shift_left", ((3, 1), (5, 2), (8, 1))),
            (">>=", "compound_shift_right", ((3, 1), (5, 2), (8, 1))),
        )
        subject = self.root / "callable.cpp"
        subject.write_text("".join(
            f"{type_name} {name}({type_name} value) {{ return value; }}\n"
            for type_name, name, _ in destinations
        ) + "".join(
            f"{result} {name}({parameter} value) {{ return value; }}\n"
            for result, name, parameter in return_casts
        ) + "".join(
            f"int {name}(int value, int amount) {{ value {operator} amount; return value; }}\n"
            for operator, name, _ in compound_cases
        ) + "int literal() { return 7; }\n"
          "int null_then_literal() { ; return 7; }\n"
          "int first(int left, int right) { return left; }\n"
          "int branch(int value) { if (value) return value; return 0; }\n"
          "int branch_else(int value) { if (value) return value; else return 7; }\n"
          "int expression_stmt(int value) { value + 1; return value; }\n"
          "int assign(int value) { value = value + 1; return value; }\n"
          "int compound_add(int value) { value += 1; return value; }\n"
          "unsigned int compound_unsigned(unsigned int value, unsigned int amount) { value += amount; return value; }\n"
          "int compound_self(int value) { value += value; return value; }\n"
          "int compound_while(int value) { while (value < 3) value += 1; return value; }\n"
          "int compound_do(int value) { do { value += 1; } while (value < 3); return value; }\n"
          "int prefix_increment(int value) { return ++value; }\n"
          "int postfix_increment(int value) { return value++; }\n"
          "int prefix_decrement(int value) { return --value; }\n"
          "int postfix_decrement(int value) { return value--; }\n"
          "int discarded_increment(int value) { value++; return value; }\n"
          "unsigned int increment_unsigned(unsigned int value) { return ++value; }\n"
          "int conditional(int value) { return value ? 7 : 3; }\n"
          "int conditional_param(int condition, int value) { return condition ? value : 3; }\n"
          "int conditional_increment(int value) { return value ? ++value : value; }\n"
          "int comma(int value) { return value++, value; }\n"
          "int for_loop(int value) { for (value = 0; value < 3; ++value) { value += 1; } return value; }\n"
          "int for_init_once(int value, int total) { for (++total; value < 3; ++value) { ++total; } return total; }\n"
          "int for_false(int value, int total) { for (++total; 0; ++total) { ++total; } return total; }\n"
          "int for_return(int value) { for (value = 0; value < 3; ++value) { { return value; } } return 9; }\n"
          "int nested_blocks(int value) { { { ++value; } } return value; }\n"
          "int empty_blocks(int value) { {} { {} } return value; }\n"
          "int break_loop(int value) { while (value < 3) { ++value; break; } return value; }\n"
          "int continue_loop(int value) { while (value < 3) { ++value; continue; } return value; }\n"
          "int for_break_loop(int value) { for (value = 0; value < 3; ++value) { ++value; break; } return value; }\n"
          "int for_continue_loop(int value) { for (value = 0; value < 3; ++value) { continue; } return value; }\n"
          "int switch_select(int value) { switch (value) { case 0: return 4; case 1: return 5; default: return 6; } return 7; }\n"
          "int switch_while(int value) { while (value) { switch (value) { case 1: --value; continue; default: return value; } } return value; }\n"
          "int switch_for(int value) { for (value = value; value < 3; ++value) { switch (value) { default: continue; } value += 10; } return value; }\n"
          "int switch_do(int value) { do { switch (value) { default: ++value; continue; } value += 10; } while (value < 3); return value; }\n"
          "int switch_nested(int value) { switch (value) { default: while (value < 3) { ++value; continue; } } return value; }\n"
          "int switch_break(int value) { switch (value) { case 0: break; case 1: return 4; default: return 5; } return value; }\n"
          "int switch_inner_while(int value, int total) { for (value = 0; value < 3; ++value) { switch (value) { default: while (total < 2) { ++total; continue; } } ++total; } return total; }\n"
          "int switch_inner_do(int value, int total) { for (value = 0; value < 3; ++value) { switch (value) { default: do { ++total; continue; } while (total < 2); } ++total; } return total; }\n"
          "int switch_inner_for(int value, int inner, int total) { for (value = 0; value < 3; ++value) { switch (value) { default: for (inner = 0; inner < 2; ++inner) { continue; } } ++total; } return total; }\n"
          "int switch_nested_continue(int value, int total) { for (value = 0; value < 3; ++value) { switch (value) { default: switch (total) { default: ++total; continue; } } total += 10; } return total; }\n"
          "int switch_fallthrough_continue(int value, int total) { for (value = 0; value < 3; ++value) { switch (value) { case 0: ++total; case 1: ++total; continue; default: break; } total += 10; } return total; }\n"
          "int switch_for_break(int value, int total) { for (value = 0; value < 3; ++value) { switch (value) { default: break; } ++total; } return total; }\n"
          "int switch_conditional_continue(int value) { for (value = value; value < 3; ++value) { switch (value) { default: if (value < 2) continue; break; } value += 2; } return value; }\n"
          "int do_break_loop(int value) { do { ++value; break; } while (value < 3); return value; }\n"
          "int do_continue_loop(int value) { do { ++value; continue; } while (value < 3); return value; }\n"
          "short compound_narrow(short value) { value += 1; return value; }\n"
          "int compound_mixed(int value, unsigned int amount) { value += amount; return value; }\n"
          "int loop(int value) { while (value) return value; return 0; }\n"
          "int do_loop(int value) { do { if (value) return value; } while (0); return 7; }\n"
          "int unary(int value) { return -value; }\n"
          "int positive(int value) { return +value; }\n"
          "int complement(int value) { return ~value; }\n"
          "int compare(int value) { if (value > 0) return 1; return 0; }\n"
          "bool equal_values(int left, int right) { return left == right; }\n"
          "bool not_equal_values(int left, int right) { return left != right; }\n"
          "bool less_values(int left, int right) { return left < right; }\n"
          "bool less_equal_values(int left, int right) { return left <= right; }\n"
          "bool greater_equal_values(int left, int right) { return left >= right; }\n"
          "bool logical(int value) { return !value; }\n"
          "int add(int left, int right) { return left + right; }\n"
          "int subtract(int left, int right) { return left - right; }\n"
          "int multiply(int left, int right) { return left * right; }\n"
          "int divide(int left, int right) { return left / right; }\n"
          "int remainder(int left, int right) { return left % right; }\n"
          "int bit_and(int left, int right) { return left & right; }\n"
          "int bit_or(int left, int right) { return left | right; }\n"
          "int bit_xor(int left, int right) { return left ^ right; }\n"
          "int shift_left(int left, int right) { return left << right; }\n"
          "int shift_right(int left, int right) { return left >> right; }\n"
          "bool both(int left, int right) { return left && right; }\n"
          "bool either(int left, int right) { return left || right; }\n"
          "bool both_increment(int value) { return value && ++value; }\n"
          "bool either_increment(int value) { return value || ++value; }\n",
          encoding="utf-8")
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        result = subprocess.run([
            clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", "-x", "c++", str(subject),
            "-Xclang", "-load", "-Xclang", str(probe_library),
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
        ], cwd=self.root, env=environment, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        probe = json.loads(result.stdout)
        names = ({name for _, name, _ in destinations}
                 | {name for _, name, _ in return_casts}
                 | {name for _, name, _ in compound_cases}) | {
            "literal",
            "null_then_literal",
            "first", "branch", "branch_else", "expression_stmt", "assign", "compound_add",
            "loop", "do_loop", "unary", "compare", "equal_values",
            "not_equal_values", "less_values", "less_equal_values",
            "greater_equal_values", "logical", "add",
            "subtract", "multiply", "divide", "remainder", "bit_and", "bit_or",
            "bit_xor", "shift_left", "shift_right", "both", "either", "both_increment",
            "either_increment", "positive",
            "complement", "compound_unsigned", "compound_self", "compound_while", "compound_do",
            "prefix_increment", "postfix_increment", "prefix_decrement",
            "postfix_decrement", "discarded_increment", "increment_unsigned",
            "conditional", "conditional_param", "conditional_increment", "comma", "for_loop",
            "for_init_once", "for_false", "for_return", "nested_blocks", "empty_blocks",
            "break_loop", "continue_loop", "for_break_loop", "for_continue_loop",
            "switch_select", "do_break_loop", "do_continue_loop",
            "switch_while", "switch_for", "switch_do", "switch_nested", "switch_break",
            "switch_inner_while", "switch_inner_do", "switch_inner_for", "switch_nested_continue",
            "switch_fallthrough_continue", "switch_for_break",
            "switch_conditional_continue"}
        refusals = {"compound_narrow", "compound_mixed"}
        paths = {}
        pending = [(probe["ast"], [])]
        while pending:
            node, path = pending.pop()
            if node.get("kind") == "FunctionDecl" and node.get("name") in (names | refusals):
                self.assertNotIn(node["name"], paths)
                paths[node["name"]] = path
            pending.extend((child, path + [index])
                           for index, child in enumerate(node.get("inner", [])))
        self.assertEqual(set(paths), names | refusals)
        sources = (
            ("short", ".signed 16", -32768),
            ("short", ".signed 16", 32767),
            ("int", ".signed 32", -1),
            ("int", ".signed 32", 0),
            ("int", ".signed 32", 65536),
            ("unsigned int", ".unsigned 32", 4294967295),
            ("long long", ".signed 64", -9223372036854775808),
            ("unsigned long long", ".unsigned 64", 18446744073709551615),
            ("bool", ".boolean", 1),
        )
        rows = []
        expressions = []
        for _, name, destination in destinations:
            for type_name, source_format, value in sources:
                literal = ("(-9223372036854775807LL - 1)" if value == -(1 << 63)
                           else f"{value}LL" if value < 0 else f"{value}ULL")
                expressions.append(f"{name}(static_cast<{type_name}>({literal}))")
                rows.append((name, destination, [(source_format, value)]))
        for value in (-1, 0, 7):
            expressions.append(f"to_bool({value})")
            rows.append(("to_bool", ".boolean", [(".signed 32", value)]))
        for value, literal in ((0, "false"), (1, "true")):
            expressions.append(f"to_int({literal})")
            rows.append(("to_int", ".signed 32", [(".boolean", value)]))
        for value in (-32769, 0, 32768):
            expressions.append(f"to_short({value})")
            rows.append(("to_short", ".signed 16", [(".signed 32", value)]))
        expressions.append("literal()")
        rows.append(("literal", ".signed 32", []))
        expressions.append("null_then_literal()")
        rows.append(("null_then_literal", ".signed 32", []))
        expressions.append("first(static_cast<short>(-17), 4294967295U)")
        rows.append(("first", ".signed 32", [(".signed 16", -17),
                                            (".unsigned 32", 4294967295)]))
        for value in (-1, 0, 65536):
            expressions.append(f"branch({value})")
            rows.append(("branch", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 65536):
            expressions.append(f"branch_else({value})")
            rows.append(("branch_else", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"expression_stmt({value})")
            rows.append(("expression_stmt", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"assign({value})")
            rows.append(("assign", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"compound_add({value})")
            rows.append(("compound_add", ".signed 32", [(".signed 32", value)]))
        for _, name, cases in compound_cases:
            for value, amount in cases:
                expressions.append(f"{name}({value}, {amount})")
                rows.append((name, ".signed 32", [
                    (".signed 32", value), (".signed 32", amount)]))
        for value, amount in ((0, 7), (4294967295, 1), (4294967295, 4294967295)):
            expressions.append(f"compound_unsigned({value}U, {amount}U)")
            rows.append(("compound_unsigned", ".unsigned 32", [
                (".unsigned 32", value), (".unsigned 32", amount)]))
        for value in (-7, 0, 7):
            expressions.append(f"compound_self({value})")
            rows.append(("compound_self", ".signed 32", [(".signed 32", value)]))
        for name in ("compound_while", "compound_do"):
            for value in (-1, 0, 3, 5):
                expressions.append(f"{name}({value})")
                rows.append((name, ".signed 32", [(".signed 32", value)]))
        for name in (
            "prefix_increment", "postfix_increment", "prefix_decrement",
            "postfix_decrement", "discarded_increment",
        ):
            for value in (-1, 0, 7):
                expressions.append(f"{name}({value})")
                rows.append((name, ".signed 32", [(".signed 32", value)]))
        for value in (0, 7, 4294967295):
            expressions.append(f"increment_unsigned({value}U)")
            rows.append(("increment_unsigned", ".unsigned 32", [(".unsigned 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"conditional({value})")
            rows.append(("conditional", ".signed 32", [(".signed 32", value)]))
        for condition in (-1, 0, 7):
            expressions.append(f"conditional_param({condition}, 5)")
            rows.append(("conditional_param", ".signed 32", [
                (".signed 32", condition), (".signed 32", 5)]))
        for value in (-1, 0, 7):
            expressions.append(f"conditional_increment({value})")
            rows.append(("conditional_increment", ".signed 32", [(
                ".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"comma({value})")
            rows.append(("comma", ".signed 32", [(".signed 32", value)]))
        for name, cases in {
            "for_init_once": [(-1, 0), (0, 4), (3, 7)],
            "for_false": [(-1, 0), (0, 4), (3, 7)],
            "for_return": [(-1,), (0,), (7,)],
            "nested_blocks": [(-1,), (0,), (7,)],
            "empty_blocks": [(-1,), (0,), (7,)],
        }.items():
            for arguments in cases:
                expressions.append(f"{name}({', '.join(map(str, arguments))})")
                rows.append((name, ".signed 32", [(".signed 32", value) for value in arguments]))
        for value in (-1, 0, 7):
            expressions.append(f"for_loop({value})")
            rows.append(("for_loop", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"break_loop({value})")
            rows.append(("break_loop", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"continue_loop({value})")
            rows.append(("continue_loop", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"for_break_loop({value})")
            rows.append(("for_break_loop", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"for_continue_loop({value})")
            rows.append(("for_continue_loop", ".signed 32", [(".signed 32", value)]))
        for value in (0, 1, 7):
            expressions.append(f"switch_select({value})")
            rows.append(("switch_select", ".signed 32", [(".signed 32", value)]))
        switch_calls = {
            name: [(value,) for value in (-1, 0, 1, 2, 3, 7)]
            for name in ("switch_while", "switch_for", "switch_do", "switch_nested", "switch_break",
                         "switch_conditional_continue")
        }
        switch_calls["switch_inner_while"] = [(0, total) for total in (0, 1, 2, 5)]
        switch_calls["switch_inner_do"] = [(0, total) for total in (0, 1, 2, 5)]
        switch_calls["switch_inner_for"] = [(0, 0, total) for total in (-1, 0, 2)]
        switch_calls["switch_nested_continue"] = [(0, total) for total in (-1, 0, 1, 3)]
        switch_calls["switch_fallthrough_continue"] = [(0, total) for total in (-1, 0, 1, 3)]
        switch_calls["switch_for_break"] = [(0, total) for total in (-1, 0, 1, 3)]
        for name, arguments_list in switch_calls.items():
            for arguments in arguments_list:
                expressions.append(f"{name}({', '.join(map(str, arguments))})")
                rows.append((name, ".signed 32", [(".signed 32", value) for value in arguments]))
        for value in (-1, 0, 7):
            expressions.append(f"do_break_loop({value})")
            rows.append(("do_break_loop", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"do_continue_loop({value})")
            rows.append(("do_continue_loop", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"loop({value})")
            rows.append(("loop", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"do_loop({value})")
            rows.append(("do_loop", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"unary({value})")
            rows.append(("unary", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"positive({value})")
            rows.append(("positive", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"complement({value})")
            rows.append(("complement", ".signed 32", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"compare({value})")
            rows.append(("compare", ".signed 32", [(".signed 32", value)]))
        for left, right in ((-7, -7), (-7, 3), (7, 3)):
            expressions.append(f"equal_values({left}, {right})")
            rows.append(("equal_values", ".boolean", [(".signed 32", left),
                                                         (".signed 32", right)]))
        for left, right in ((-7, -7), (-7, 3), (7, 3)):
            expressions.append(f"not_equal_values({left}, {right})")
            rows.append(("not_equal_values", ".boolean", [(".signed 32", left),
                                                            (".signed 32", right)]))
        for left, right in ((-7, 3), (7, 3), (3, 3)):
            expressions.append(f"less_values({left}, {right})")
            rows.append(("less_values", ".boolean", [(".signed 32", left),
                                                       (".signed 32", right)]))
        for left, right in ((-7, 3), (3, 3), (7, 3)):
            expressions.append(f"less_equal_values({left}, {right})")
            rows.append(("less_equal_values", ".boolean", [(".signed 32", left),
                                                             (".signed 32", right)]))
        for left, right in ((-7, 3), (3, 3), (7, 3)):
            expressions.append(f"greater_equal_values({left}, {right})")
            rows.append(("greater_equal_values", ".boolean", [(".signed 32", left),
                                                                (".signed 32", right)]))
        for value in (-1, 0, 7):
            expressions.append(f"logical({value})")
            rows.append(("logical", ".boolean", [(".signed 32", value)]))
        for left, right in ((-7, 3), (0, 7), (7, 3)):
            expressions.append(f"add({left}, {right})")
            rows.append(("add", ".signed 32", [(".signed 32", left),
                                                (".signed 32", right)]))
        for left, right in ((-7, 3), (0, 7), (7, 3)):
            expressions.append(f"subtract({left}, {right})")
            rows.append(("subtract", ".signed 32", [(".signed 32", left),
                                                     (".signed 32", right)]))
        for left, right in ((-7, 3), (0, 7), (7, 3)):
            expressions.append(f"multiply({left}, {right})")
            rows.append(("multiply", ".signed 32", [(".signed 32", left),
                                                     (".signed 32", right)]))
        for left, right in ((-7, 3), (7, 3), (7, 2)):
            expressions.append(f"divide({left}, {right})")
            rows.append(("divide", ".signed 32", [(".signed 32", left),
                                                   (".signed 32", right)]))
        for left, right in ((-7, 3), (7, 3), (7, 2)):
            expressions.append(f"remainder({left}, {right})")
            rows.append(("remainder", ".signed 32", [(".signed 32", left),
                                                      (".signed 32", right)]))
        for left, right in ((5, 3), (7, 2), (8, 1)):
            expressions.append(f"bit_and({left}, {right})")
            rows.append(("bit_and", ".signed 32", [(".signed 32", left),
                                                    (".signed 32", right)]))
        for left, right in ((5, 3), (7, 2), (8, 1)):
            expressions.append(f"bit_or({left}, {right})")
            rows.append(("bit_or", ".signed 32", [(".signed 32", left),
                                                   (".signed 32", right)]))
        for left, right in ((5, 3), (7, 2), (8, 1)):
            expressions.append(f"bit_xor({left}, {right})")
            rows.append(("bit_xor", ".signed 32", [(".signed 32", left),
                                                    (".signed 32", right)]))
        for left, right in ((3, 1), (5, 2), (8, 1)):
            expressions.append(f"shift_left({left}, {right})")
            rows.append(("shift_left", ".signed 32", [(".signed 32", left),
                                                       (".signed 32", right)]))
        for left, right in ((3, 1), (5, 2), (8, 1)):
            expressions.append(f"shift_right({left}, {right})")
            rows.append(("shift_right", ".signed 32", [(".signed 32", left),
                                                        (".signed 32", right)]))
        for left, right in ((0, 7), (7, 0), (7, 3)):
            expressions.append(f"both({left}, {right})")
            rows.append(("both", ".boolean", [(".signed 32", left),
                                                (".signed 32", right)]))
        for left, right in ((0, 0), (0, 7), (7, 0)):
            expressions.append(f"either({left}, {right})")
            rows.append(("either", ".boolean", [(".signed 32", left),
                                                   (".signed 32", right)]))
        for value in (-1, 0, 7):
            expressions.append(f"both_increment({value})")
            rows.append(("both_increment", ".boolean", [(".signed 32", value)]))
        for value in (-1, 0, 7):
            expressions.append(f"either_increment({value})")
            rows.append(("either_increment", ".boolean", [(".signed 32", value)]))
        oracle = self.root / "oracle.cpp"
        oracle.write_text(
            '#include <climits>\n#include <iostream>\n#include "callable.cpp"\n'
            'static_assert(CHAR_BIT == 8 && sizeof(short) == 2 && sizeof(int) == 4\n'
            '              && sizeof(long) == 8 && sizeof(long long) == 8);\n'
            'int main() {\n' + "".join(
                f"  std::cout << static_cast<long long>({expression}) << '\\n';\n"
                for expression in expressions
            ) + "}\n", encoding="utf-8")
        outputs = []
        for optimization in ("-O0", "-O2"):
            binary = self.root / optimization[1:]
            compiled = subprocess.run([
                clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
                optimization, "-fsanitize=undefined", "-fno-sanitize-recover=all",
                "-static-libstdc++", "-static-libgcc", str(oracle), "-o", str(binary),
            ], cwd=self.root, env=environment, capture_output=True, text=True, timeout=60)
            self.assertEqual(compiled.returncode, 0, compiled.stderr)
            executed = subprocess.run([str(binary)], cwd=self.root, env=environment,
                                      capture_output=True, text=True, timeout=30)
            self.assertEqual(executed.returncode, 0, executed.stderr)
            outputs.append(executed.stdout.splitlines())
        self.assertEqual(outputs[0], outputs[1])
        self.assertEqual(len(outputs[0]), len(rows))
        guards = [
            "def callableTypeRows := parseValidatedTypeEvidence evidence",
            "def callableExpressionRows := parseValidatedBinaryExpressionEvidence evidence",
            "#guard callableTypeRows.isOk",
            "#guard callableExpressionRows.isOk",
        ]
        for name in sorted(names):
            guards.append(f"""def {name} : Except String CallableFunction := do
  let types ← callableTypeRows
  let expressions ← callableExpressionRows
  admitCallableFunction evidence types expressions TargetProfile.lp64 {paths[name]}""")
            guards.append(f"#guard {name}.isOk")
        for name in sorted(refusals):
            guards.append(f"#guard (admitCallableFunctionFromProbe evidence "
                          f"TargetProfile.lp64 {paths[name]}) matches .error _")
        for (name, destination, arguments), expected in zip(rows, outputs[0]):
            values = ", ".join(f"⟨{format_name}, {value}⟩"
                               for format_name, value in arguments)
            fuel = (256 if name in switch_calls
                    else 64 if name in ("for_break_loop", "for_continue_loop", "switch_select")
                    else 32 if name in ("break_loop", "continue_loop", "do_break_loop",
                                        "do_continue_loop")
                    else 64 if name in ("for_loop", "for_init_once", "for_false", "for_return")
                    else 32 if name in ("compound_while", "compound_do")
                    else 16)
            guards.append(f"""#guard match {name} with
  | .ok function => match evaluateCallable {fuel} .lp64 function [{values}] with
    | .ok (.ok value) => value == ⟨{destination}, {int(expected)}⟩
    | _ => false
  | .error _ => false""")
        self.assert_accepts(json.dumps(probe), "\n".join(guards),
                            options="set_option maxRecDepth 100000 in", timeout=360)
        print(f"callable argument differential: {len(rows)} rows at -O0/-O2")

    def test_runtime_inspector_schema_and_paths_fail_loudly(self):
        fixture = document()
        fixture["metadata"]["schema_version"] = "cpp-canonical-probe-0.2"
        result = self.run_inspector(fixture)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("expected 'cpp-canonical-probe-0.3'", result.stdout + result.stderr)
        result = self.run_inspector(document(), "invalid")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("invalid occurrence path", result.stdout + result.stderr)
        result = self.run_inspector(document(), "0")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing declaration occurrence", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
