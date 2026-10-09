#!/usr/bin/env python3
"""Focused tooling tests, not C++ semantic admission or execution tests.

Run explicitly with LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY set to the
matching frontend and built probe library. No build or CI registration occurs.
Temporary translation fixtures establish tooling behavior only.
"""

import json
import os
import pathlib
import re
import shutil
import subprocess
import tempfile
import unittest


SOURCE = """namespace model {
struct Box;
struct Box {
    Box() = default;
    Box(const Box&) = delete;
    int read() const;
};
int Box::read() const { return 7; }
int pick(int);
int pick(double);
int pick(int value) { return value; }
int pick(double value) { return static_cast<int>(value); }
extern int declaration_only;
int defined = 3;
extern "C" {
    int c_function(int);
    extern int c_variable;
}
}
namespace model {
int c_function(int value) { return value; }
int another() { return 11; }
}
"""

POINTER_ID = re.compile(r"0x[0-9a-fA-F]+\Z")
DECLARATION_KINDS = {
    "NamespaceDecl", "CXXRecordDecl", "CXXMethodDecl", "CXXConstructorDecl",
    "FunctionDecl", "VarDecl",
}


def normalize_pointers(value):
    identifiers = {}

    def normalize(current):
        if isinstance(current, dict):
            return {key: normalize(child) for key, child in current.items()}
        if isinstance(current, list):
            return [normalize(child) for child in current]
        if isinstance(current, str) and POINTER_ID.fullmatch(current):
            if current not in identifiers:
                identifiers[current] = "declaration-{}".format(len(identifiers))
            return identifiers[current]
        return current

    return normalize(value)


def declaration_occurrences(ast):
    occurrences = {}
    pending = [(ast, ())]
    while pending:
        node, path = pending.pop()
        if isinstance(node, dict):
            kind = node.get("kind")
            identifier = node.get("id")
            if isinstance(kind, str) and kind.endswith("Decl") and isinstance(identifier, str):
                occurrences.setdefault(identifier, []).append((path, node))
            for key, child in reversed(list(node.items())):
                pending.append((child, path + (key,)))
        elif isinstance(node, list):
            for index, child in reversed(list(enumerate(node))):
                pending.append((child, path + (index,)))
    return occurrences


def witnessed_relationships(probe):
    occurrences = declaration_occurrences(probe["ast"])

    def witness(identifier):
        if identifier is None:
            return ("no-reference",)
        matches = occurrences.get(identifier, [])
        if not matches:
            return ("unindexed-reference",)
        return tuple(path for path, node in matches)

    result = []
    for record in probe["metadata"]["declarations"]:
        if record.get("kind") not in DECLARATION_KINDS:
            continue
        if record.get("name") not in {
            "model", "Box", "read", "pick", "declaration_only", "defined",
            "c_function", "c_variable", "another",
        }:
            continue
        relationships = tuple(
            (field, witness(record.get(field)))
            for field in (
                "canonical", "previous", "semantic_context", "lexical_context",
                "original_namespace", "represented_class",
            )
        )
        result.append((
            witness(record["id"]), record["kind"], record.get("name"),
            record["implicit"], record.get("injected_class_name"), relationships,
            record["definition"], record.get("variable_definition_kind"),
            record.get("language_linkage"),
        ))
    return result


class CanonicalProbeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        requested = os.environ.get("LEANCPP_CLANG")
        library = os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            raise RuntimeError("set LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY explicitly")
        cls.clang = shutil.which(requested)
        cls.library = pathlib.Path(library).resolve()
        if cls.clang is None or not cls.library.is_file():
            raise RuntimeError("the selected frontend and compiled probe library must exist")

    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-canonical-probe-test-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)
        self.source = self.root / "input.cpp"
        self.source.write_text(SOURCE, encoding="utf-8")

    def run_frontend(self, plugin=True, plugin_arguments=(), library=None):
        arguments = [
            self.clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", "-x", "c++", str(self.source),
        ]
        if plugin:
            arguments.extend([
                "-Xclang", "-load", "-Xclang", str(library or self.library),
                "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe",
            ])
            for argument in plugin_arguments:
                arguments.extend([
                    "-Xclang", "-plugin-arg-leancpp-canonical-probe", "-Xclang", argument,
                ])
        else:
            arguments.extend(["-Xclang", "-ast-dump=json"])
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        environment["SOURCE_DATE_EPOCH"] = "0"
        return subprocess.run(
            arguments, cwd=self.root, env=environment, capture_output=True,
            text=True, timeout=30,
        )

    def probe(self):
        result = self.run_frontend()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout, "a successful probe must publish its evidence")
        return json.loads(result.stdout)

    def records(self, probe, kind, name):
        records = [
            record for record in probe["metadata"]["declarations"]
            if record["kind"] == kind and record.get("name") == name
        ]
        self.assertTrue(records, "no {} records for {}".format(kind, name))
        return records

    def test_schema_and_frontend_versions_are_explicit(self):
        probe = self.probe()
        metadata = probe["metadata"]
        self.assertEqual(metadata["schema_version"], "cpp-canonical-probe-0.1")
        self.assertTrue(metadata["compiled_frontend"])
        self.assertIn(metadata["compiled_frontend"], metadata["runtime_frontend"])
        self.assertTrue(metadata["llvm_headers"])
        self.assertEqual(probe["ast"]["kind"], "TranslationUnitDecl")

    def test_same_process_joins_preserve_nonempty_coverage_and_raw_gaps(self):
        probe = self.probe()
        occurrences = declaration_occurrences(probe["ast"])
        records = probe["metadata"]["declarations"]
        supplemented = {record["id"] for record in records}
        joined = set(occurrences) & supplemented
        unsupplemented = set(occurrences) - supplemented
        supplement_only = supplemented - set(occurrences)
        self.assertGreater(len(joined), 0)
        self.assertEqual(len(occurrences), len(joined) + len(unsupplemented))
        self.assertEqual(len(supplemented), len(joined) + len(supplement_only))
        for record in records:
            if record.get("name") not in {"model", "Box", "read", "pick"}:
                continue
            self.assertIn(record["id"], occurrences)
            for path, node in occurrences[record["id"]]:
                self.assertIsInstance(path, tuple)
                self.assertEqual(node["kind"], record["kind"])
        print(
            "canonical probe coverage: {} joined IDs; {} raw gaps; {} supplement-only".format(
                len(joined), len(unsupplemented), len(supplement_only),
            ),
        )

    def test_raw_ast_matches_independent_stock_dump_up_to_pointer_renaming(self):
        probe = self.probe()
        stock = self.run_frontend(plugin=False)
        self.assertEqual(stock.returncode, 0, stock.stderr)
        self.assertEqual(normalize_pointers(probe["ast"]), normalize_pointers(json.loads(stock.stdout)))

    def test_skeletal_builtin_references_remain_visible_as_raw_gaps(self):
        probe = self.probe()
        occurrences = declaration_occurrences(probe["ast"])
        supplemented = {record["id"] for record in probe["metadata"]["declarations"]}
        gaps = set(occurrences) - supplemented
        skeletal = [
            (path, node) for identifier in gaps for path, node in occurrences[identifier]
            if node["kind"].endswith("RecordDecl") and "decl" in path and "inner" not in node
        ]
        self.assertTrue(skeletal, "nested skeletal builtin records must not disappear from telemetry")
        for path, node in skeletal:
            self.assertNotIn(node["id"], supplemented)
            self.assertNotIn("inner", node)
            self.assertTrue(any(isinstance(component, str) for component in path))
            self.assertTrue(any(isinstance(component, int) for component in path))

    def test_namespace_reopening_reports_one_canonical_namespace(self):
        namespaces = self.records(self.probe(), "NamespaceDecl", "model")
        self.assertEqual(len(namespaces), 2)
        self.assertNotEqual(namespaces[0]["id"], namespaces[1]["id"])
        self.assertEqual(namespaces[0]["canonical"], namespaces[1]["canonical"])
        for record in namespaces:
            self.assertEqual(record["original_namespace"], record["canonical"])
            self.assertFalse(record["anonymous_namespace"])
            self.assertFalse(record["inline_namespace"])

    def test_out_of_class_method_keeps_lexical_and_semantic_contexts_distinct(self):
        methods = self.records(self.probe(), "CXXMethodDecl", "read")
        self.assertEqual(len(methods), 2)
        declaration = next(record for record in methods if not record["definition"])
        definition = next(record for record in methods if record["definition"])
        self.assertEqual(declaration["canonical"], definition["canonical"])
        self.assertEqual(declaration["semantic_context"], definition["semantic_context"])
        self.assertEqual(declaration["semantic_context"], declaration["lexical_context"])
        self.assertNotEqual(definition["semantic_context"], definition["lexical_context"])
        self.assertEqual(definition["previous"], declaration["id"])

    def test_overload_redeclarations_do_not_merge_by_name(self):
        functions = self.records(self.probe(), "FunctionDecl", "pick")
        self.assertEqual(len(functions), 4)
        groups = {}
        for record in functions:
            groups.setdefault(record["canonical"], []).append(record)
        self.assertEqual(len(groups), 2)
        for canonical, records in groups.items():
            self.assertEqual(len(records), 2)
            self.assertEqual(sum(record["definition"] for record in records), 1)
            self.assertIn(canonical, {record["id"] for record in records})

    def test_injected_name_preserves_self_canonical_and_represented_class(self):
        classes = self.records(self.probe(), "CXXRecordDecl", "Box")
        injected = [record for record in classes if record["injected_class_name"]]
        ordinary = [record for record in classes if not record["injected_class_name"]]
        self.assertEqual(len(injected), 1)
        self.assertEqual(len(ordinary), 2)
        self.assertEqual(len({record["canonical"] for record in ordinary}), 1)
        name = injected[0]
        self.assertTrue(name["implicit"])
        self.assertEqual(name["canonical"], name["id"])
        self.assertIsNone(name["previous"])
        self.assertIn(name["represented_class"], {record["id"] for record in ordinary})
        self.assertNotEqual(name["represented_class"], name["canonical"])
        self.assertFalse(name["definition"])
        self.assertEqual(sum(record["definition"] for record in ordinary), 1)

    def test_defaulted_and_deleted_definitions_are_not_body_presence(self):
        constructors = self.records(self.probe(), "CXXConstructorDecl", "Box")
        defaulted = [record for record in constructors if record["defaulted"]]
        deleted = [record for record in constructors if record["deleted_as_written"]]
        self.assertEqual(len(defaulted), 1)
        self.assertEqual(len(deleted), 1)
        for record in defaulted + deleted:
            self.assertTrue(record["definition"])
            self.assertFalse(record["body_present"])
            self.assertEqual(record["definition_api"], "FunctionDecl.isThisDeclarationADefinition")

    def test_variable_definition_kind_is_an_enum_not_a_boolean(self):
        probe = self.probe()
        declaration = self.records(probe, "VarDecl", "declaration_only")[0]
        definition = self.records(probe, "VarDecl", "defined")[0]
        for record in (declaration, definition):
            self.assertIs(type(record["variable_definition_kind"]), int)
            self.assertIn(record["variable_definition_kind"], (0, 1, 2))
            self.assertIsNone(record["definition"])
            self.assertEqual(record["definition_api"], "VarDecl.isThisDeclarationADefinition")
        self.assertEqual(declaration["variable_definition_kind"], 0)
        self.assertEqual(definition["variable_definition_kind"], 2)

    def test_c_language_linkage_survives_redeclaration(self):
        probe = self.probe()
        functions = self.records(probe, "FunctionDecl", "c_function")
        self.assertEqual(len(functions), 2)
        self.assertEqual(len({record["canonical"] for record in functions}), 1)
        for record in functions + self.records(probe, "VarDecl", "c_variable"):
            self.assertEqual(record["language_linkage"], "C")
            self.assertEqual(record["linkage_formal"], "External")
        for record in self.records(probe, "FunctionDecl", "pick"):
            self.assertEqual(record["language_linkage"], "C++")

    def test_syntax_error_does_not_publish_a_json_artifact(self):
        self.source.write_text("int broken( {\n", encoding="utf-8")
        result = self.run_frontend()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("error:", result.stderr)

    def test_nonempty_plugin_arguments_do_not_publish_a_json_artifact(self):
        result = self.run_frontend(plugin_arguments=("unexpected",))
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("canonical probe accepts no plugin arguments", result.stderr)

    def test_header_runtime_version_mismatch_does_not_publish_json(self):
        headers = pathlib.Path(os.environ.get(
            "LEANCPP_PROBE_INCLUDE", str(self.library.parent / "toolchain" / "include"),
        ))
        library_directory = pathlib.Path(self.clang).parent.parent / "lib"
        clang_library = library_directory / "libclang-cpp.so.21.1"
        llvm_library = library_directory / "libLLVM.so.21.1"
        if not (headers / "clang" / "Basic" / "Version.h").is_file():
            self.skipTest("matching probe development headers are unavailable")
        if not clang_library.is_file() or not llvm_library.is_file():
            self.skipTest("matching probe development libraries are unavailable")
        original = pathlib.Path(__file__).with_name("canonical_probe.cpp").read_text(encoding="utf-8")
        marker = "\nnamespace {"
        self.assertEqual(original.count(marker), 1)
        altered = original.replace(
            marker,
            '\n#undef CLANG_VERSION_STRING\n#define CLANG_VERSION_STRING "0.0.unsupported"\n' + marker,
            1,
        )
        source = self.root / "unsupported_version.cpp"
        source.write_text(altered, encoding="utf-8")
        library = self.root / "unsupported_version.so"
        environment = dict(os.environ)
        environment.pop("CCC_OVERRIDE_OPTIONS", None)
        environment.pop("CCC_ADD_ARGS", None)
        built = subprocess.run(
            [
                self.clang, "--no-default-config", "-std=c++17", "-shared", "-fPIC",
                "-I", str(headers), str(source), str(clang_library), str(llvm_library),
                "-Wl,-rpath," + str(library_directory), "-o", str(library),
            ],
            cwd=self.root, env=environment, capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(built.returncode, 0, built.stderr)
        result = self.run_frontend(library=library)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("canonical probe header/runtime version mismatch", result.stderr)

    def test_fresh_runs_agree_by_occurrence_witness_not_pointer_equality(self):
        first = self.probe()
        second = self.probe()
        relationships = witnessed_relationships(first)
        self.assertTrue(relationships)
        self.assertEqual(relationships, witnessed_relationships(second))
        self.assertEqual(normalize_pointers(first["ast"]), normalize_pointers(second["ast"]))


if __name__ == "__main__":
    unittest.main()
