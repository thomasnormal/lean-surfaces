#!/usr/bin/env python3
"""Bounded literal loading and runtime inspection, not C++ semantic admission.

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

    def run_loader(self, contents, guards=""):
        probe_path = self.root / "probe.json"
        if isinstance(contents, bytes):
            probe_path.write_bytes(contents)
        else:
            probe_path.write_text(contents, encoding="utf-8")
        lean_path = self.root / "Check.lean"
        lean_path.write_text(
            "import LeanModels.Cpp.Load\n"
            "open LeanModels.Cpp\n"
            "namespace CppProbeIngestionFixture\n"
            "load_cpp_probe evidence from " + json.dumps(str(probe_path)) + "\n"
            + guards + "\nend CppProbeIngestionFixture\n",
            encoding="utf-8",
        )
        return subprocess.run(
            [self.lake, "env", "lean", str(lean_path)], cwd=REPO_ROOT,
            capture_output=True, text=True, timeout=60,
        )

    def assert_accepts(self, contents, guards=""):
        result = self.run_loader(contents, guards)
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
""")

    def run_inspector(self, fixture, *paths):
        probe_path = self.root / "inspection.json"
        probe_path.write_text(json.dumps(fixture), encoding="utf-8")
        return subprocess.run(
            [self.lake, "env", "lean", "--run", str(REPO_ROOT / "extractors/cpp/inspect_probe.lean"),
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
