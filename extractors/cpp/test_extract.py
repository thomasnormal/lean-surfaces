#!/usr/bin/env python3
"""Regress the C++ translation envelope, not a C++ execution semantics.

Run from anywhere with Python's standard library and clang++ on PATH.
LEANCPP_CLANG may select the frontend executable. Fixtures are temporary
translation inputs, never proof examples or claims about admitted execution.
LEANCPP_TEST_LEAN=1 additionally checks the built Lean translation ingester.
"""

import hashlib
import importlib.util
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


HERE = pathlib.Path(__file__).resolve().parent
REPO_ROOT = HERE.parent.parent
EXTRACTOR_PATH = HERE / "extract.py"
MODULE_SPEC = importlib.util.spec_from_file_location("cpp_extract_under_test", EXTRACTOR_PATH)
extractor = importlib.util.module_from_spec(MODULE_SPEC)
sys.modules[MODULE_SPEC.name] = extractor
MODULE_SPEC.loader.exec_module(extractor)

DECLARATION_SOURCE = """namespace model {
struct Box {
    int value;
    explicit Box(int initial) : value(initial) {}
    int read() const;
};
int Box::read() const { return value; }
int pick(int value) { return value; }
int pick(double value) { return static_cast<int>(value); }
long widen(int value) { return value; }
template <typename Item> Item identity(Item value) { return value; }
int use(int input) {
    Box box(input);
    int &reference = box.value;
    int &&rvalue = static_cast<int&&>(reference);
    return pick(reference) + pick(2.5) + identity(input) + box.read() + rvalue;
}
}
"""

POINTER_ID = re.compile(r"0x[0-9a-fA-F]+\Z")


def sha256(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def normalized_ast(ast):
    identifiers = {}

    def normalize(value):
        if isinstance(value, dict):
            return {key: normalize(child) for key, child in value.items()}
        if isinstance(value, list):
            return [normalize(child) for child in value]
        if isinstance(value, str) and POINTER_ID.fullmatch(value):
            if value not in identifiers:
                identifiers[value] = "clang-id-{}".format(len(identifiers))
            return identifiers[value]
        return value

    return normalize(ast)


def ast_nodes(ast):
    pending = [ast]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            if "kind" in current:
                yield current
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)


def declaration_occurrence_paths(ast):
    occurrences = []
    pending = [(ast, [])]
    while pending:
        current, path = pending.pop()
        if not isinstance(current, dict):
            continue
        kind = current.get("kind")
        identifier = current.get("id")
        if isinstance(kind, str) and kind.endswith("Decl") and isinstance(identifier, str):
            occurrences.append((identifier, path))
        children = current.get("inner", [])
        if isinstance(children, list):
            pending.extend((children[index], path + [index])
                           for index in range(len(children) - 1, -1, -1))
    return occurrences


class ExtractorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        requested = os.environ.get("LEANCPP_CLANG", "clang++")
        cls.clang = shutil.which(requested)
        if cls.clang is None:
            raise RuntimeError("C++ extractor tests require clang++ or a valid LEANCPP_CLANG")

    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-extract-test-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)
        self.source = self.write("input.cpp", "int value() { return 17; }\n")

    def write(self, relative, contents):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents, encoding="utf-8")
        return path

    def envelope(self, source=None, flags=None):
        return extractor.extract(source or self.source, clang=self.clang, flags=flags)

    def run_command(self, arguments, cwd=None, environment=None):
        return subprocess.run(
            arguments, cwd=cwd, env=environment, capture_output=True, text=True, timeout=30,
        )

    def run_cli(self, source=None, output=None, flags=None):
        arguments = [sys.executable, str(EXTRACTOR_PATH), str(source or self.source)]
        arguments.extend(["--clang", self.clang])
        if output is not None:
            arguments.extend(["--out", str(output)])
        if flags:
            arguments.extend(["--"] + flags)
        return self.run_command(arguments)

    def dependency_map(self, envelope):
        dependencies = {}
        for dependency in envelope["dependencies"]:
            path = pathlib.Path(dependency["path"])
            self.assertTrue(path.is_absolute())
            self.assertTrue(path.is_file())
            self.assertEqual(dependency["sha256"], sha256(path))
            self.assertNotIn(path.resolve(), dependencies)
            dependencies[path.resolve()] = dependency["sha256"]
        return dependencies

    def declaration_envelope(self):
        self.source.write_text(DECLARATION_SOURCE, encoding="utf-8")
        return self.envelope()

    def test_envelope_identifies_the_exact_source_and_edition(self):
        envelope = self.envelope()
        self.assertEqual(envelope["schema_version"], "cpp-0.1")
        self.assertEqual(envelope["language"], "cpp")
        self.assertEqual(envelope["edition"], "c++23")
        self.assertEqual(envelope["profile_id"], "cpp23-clang-json-0.1")
        self.assertEqual(envelope["source_file"], str(self.source.resolve()))
        self.assertEqual(envelope["source_sha256"], sha256(self.source))
        self.assertEqual(envelope["ast"]["kind"], "TranslationUnitDecl")

    def test_frontend_provenance_matches_an_independent_clang_invocation(self):
        envelope = self.declaration_envelope()
        frontend = envelope["frontend"]
        executable = pathlib.Path(frontend["path"])
        self.assertTrue(executable.is_absolute())
        self.assertEqual(executable.resolve(), pathlib.Path(self.clang).resolve())
        self.assertEqual(frontend["sha256"], sha256(executable))
        self.assertTrue(pathlib.Path(frontend["cwd"]).is_absolute())
        version = self.run_command([str(executable), "--version"])
        self.assertEqual(version.returncode, 0, version.stderr)
        self.assertIn(version.stdout.splitlines()[0], frontend["version"])
        target = self.run_command([str(executable), "-dumpmachine"])
        self.assertEqual(target.returncode, 0, target.stderr)
        self.assertEqual(frontend["target"], target.stdout.strip())
        arguments = list(frontend["argv"])
        self.assertIsInstance(arguments, list)
        self.assertEqual(pathlib.Path(arguments[0]).resolve(), executable.resolve())
        self.assertIn(str(self.source.resolve()), arguments)
        self.assertIn("-fsyntax-only", arguments)
        self.assertIn("-ast-dump=json", arguments)
        self.assertTrue("-std=c++23" in arguments or "--std=c++23" in arguments)
        if "-MF" in arguments:
            arguments[arguments.index("-MF") + 1] = str(self.root / "independent.d")
        environment = dict(os.environ)
        environment.update(frontend.get("environment", {}))
        replay = self.run_command(arguments, cwd=frontend["cwd"], environment=environment)
        self.assertEqual(replay.returncode, 0, replay.stderr)
        self.assertEqual(normalized_ast(envelope["ast"]), normalized_ast(json.loads(replay.stdout)))

    def test_default_clang_configuration_is_explicitly_disabled(self):
        envelope = self.envelope()
        self.assertIn("--no-default-config", envelope["frontend"]["argv"])

    def test_hidden_clang_driver_overrides_are_refused(self):
        self.source.write_text("struct Holder { struct { int value; }; };\n", encoding="utf-8")
        cases = (("CCC_OVERRIDE_OPTIONS", "x-pedantic-errors"),
                 ("CCC_OVERRIDE_OPTIONS", "+-std=c++20"),
                 ("CCC_OVERRIDE_OPTIONS", ""),
                 ("CCC_ADD_ARGS", "-Wno-error=gnu-anonymous-struct"),
                 ("CCC_ADD_ARGS", ""))
        for key, value in cases:
            with self.subTest(key=key, value=value):
                with mock.patch.dict(os.environ, {key: value}):
                    with self.assertRaisesRegex(extractor.ExtractionError, key):
                        self.envelope()

    def test_declaration_kinds_outside_the_c_vocabulary_remain_raw(self):
        nodes = list(ast_nodes(self.declaration_envelope()["ast"]))
        kinds = {node["kind"] for node in nodes}
        self.assertTrue({
            "NamespaceDecl", "CXXRecordDecl", "CXXConstructorDecl",
            "CXXConstructExpr", "CXXMemberCallExpr", "FunctionTemplateDecl",
            "CXXStaticCastExpr",
        }.issubset(kinds))
        self.assertNotIn("Unsupported", kinds)

    def test_value_categories_and_implicit_conversions_are_preserved(self):
        nodes = list(ast_nodes(self.declaration_envelope()["ast"]))
        categories = {node["valueCategory"] for node in nodes if "valueCategory" in node}
        self.assertTrue({"lvalue", "prvalue", "xvalue"}.issubset(categories))
        conversions = {node.get("castKind") for node in nodes if node["kind"] == "ImplicitCastExpr"}
        self.assertTrue({"LValueToRValue", "IntegralCast"}.issubset(conversions))

    def test_overloads_and_referenced_declarations_keep_their_identity(self):
        nodes = list(ast_nodes(self.declaration_envelope()["ast"]))
        overloads = [node for node in nodes if node["kind"] == "FunctionDecl"
                     and node.get("name") == "pick" and "mangledName" in node]
        self.assertEqual(len(overloads), 2)
        self.assertEqual(len({node["id"] for node in overloads}), 2)
        self.assertEqual(len({node["mangledName"] for node in overloads}), 2)
        referenced = {node["referencedDecl"]["id"] for node in nodes
                      if node["kind"] == "DeclRefExpr"
                      and node.get("referencedDecl", {}).get("name") == "pick"}
        self.assertEqual(referenced, {node["id"] for node in overloads})

    def test_out_of_line_method_retains_its_parent_context(self):
        nodes = list(ast_nodes(self.declaration_envelope()["ast"]))
        records = [node for node in nodes if node["kind"] == "CXXRecordDecl"
                   and node.get("name") == "Box" and node.get("completeDefinition")]
        methods = [node for node in nodes if node["kind"] == "CXXMethodDecl"
                   and node.get("name") == "read" and "parentDeclContextId" in node]
        self.assertEqual(len(records), 1)
        self.assertEqual(len(methods), 1)
        self.assertEqual(methods[0]["parentDeclContextId"], records[0]["id"])

    def test_user_transitive_and_system_dependencies_are_hashed(self):
        leaf = self.write("include/leaf.hpp", "inline constexpr int leaf_value = 9;\n")
        header = self.write("include/user.hpp", '#include "leaf.hpp"\n')
        self.source.write_text(
            '#include "user.hpp"\n#include <stddef.h>\nsize_t value = leaf_value;\n',
            encoding="utf-8",
        )
        dependencies = self.dependency_map(self.envelope(flags=["-I", str(header.parent)]))
        self.assertIn(header.resolve(), dependencies)
        self.assertIn(leaf.resolve(), dependencies)
        self.assertTrue(any(path.name == "stddef.h" for path in dependencies))
        self.assertTrue(any(self.root not in path.parents for path in dependencies))

    def test_normal_include_macro_and_forced_header_flags_are_admitted(self):
        header = self.write("include/value.hpp", "inline constexpr int header_value = 3;\n")
        forced = self.write("forced.hpp", "inline constexpr int forced_value = 5;\n")
        self.source.write_text(
            '#include "value.hpp"\nint value = ADMITTED_VALUE + forced_value + header_value;\n',
            encoding="utf-8",
        )
        flags = ["-I", str(header.parent), "-DADMITTED_VALUE=17", "-include", str(forced)]
        envelope = self.envelope(flags=flags)
        dependencies = self.dependency_map(envelope)
        self.assertIn(header.resolve(), dependencies)
        self.assertIn(forced.resolve(), dependencies)
        for flag in flags:
            self.assertIn(flag, envelope["frontend"]["argv"])

    def test_adjacent_precompiled_headers_do_not_hide_forced_header_ast(self):
        for suffix in (".pch", ".gch"):
            with self.subTest(suffix=suffix):
                header = self.write("precompiled/" + suffix[1:] + "/value.hpp", (
                    "inline constexpr int forced_value = 23;\n"
                    "inline int forced_read() { return forced_value; }\n"
                ))
                precompiled = header.with_name(header.name + suffix)
                completed = self.run_command([
                    self.clang, "--no-default-config", "-x", "c++-header",
                    "-std=c++23", "-pedantic-errors", str(header), "-o", str(precompiled),
                ])
                self.assertEqual(completed.returncode, 0, completed.stderr)
                self.assertTrue(precompiled.is_file())
                self.source.write_text("int value() { return forced_read(); }\n", encoding="utf-8")
                envelope = self.envelope(flags=["-include", str(header)])
                dependencies = self.dependency_map(envelope)
                self.assertEqual(dependencies[self.source.resolve()], sha256(self.source))
                self.assertEqual(dependencies[header.resolve()], sha256(header))
                self.assertNotIn(precompiled.resolve(), dependencies)
                declarations = [node for node in ast_nodes(envelope["ast"])
                                if node["kind"] == "FunctionDecl"
                                and node.get("name") == "forced_read" and "inner" in node]
                self.assertEqual(len(declarations), 1)
                self.assertTrue(any(child.get("kind") == "CompoundStmt"
                                    for child in declarations[0].get("inner", [])))

    def test_dependency_paths_with_spaces_are_not_split(self):
        header = self.write("include with spaces/header value.hpp", "inline constexpr int value = 3;\n")
        self.source.write_text('#include "header value.hpp"\n', encoding="utf-8")
        dependencies = self.dependency_map(self.envelope(flags=["-I", str(header.parent)]))
        self.assertIn(header.resolve(), dependencies)

    def test_nonbreaking_space_in_dependency_filename_is_not_split(self):
        filename = "nonbreaking\u00a0space.hpp"
        header = self.write(filename, "inline constexpr int value = 3;\n")
        paths = extractor.dependency_paths("cpp-input: " + filename + "\n", self.root)
        self.assertEqual(paths, [str(header.resolve())])
        self.source.write_text('#include "' + filename + '"\n', encoding="utf-8")
        dependencies = self.dependency_map(self.envelope())
        self.assertIn(header.resolve(), dependencies)
        self.assertEqual(dependencies[header.resolve()], sha256(header))

    def test_quoted_dependency_name_does_not_hash_a_shadow_header(self):
        header = self.write("a'b'.hpp", "inline constexpr int value = 3;\n")
        shadow = self.write("ab.hpp", "inline constexpr int shadow_value = 29;\n")
        self.source.write_text('#include "a\'b\'.hpp"\nint result = value;\n', encoding="utf-8")
        dependencies = self.dependency_map(self.envelope())
        self.assertIn(header.resolve(), dependencies)
        self.assertEqual(dependencies[header.resolve()], sha256(header))
        self.assertNotIn(shadow.resolve(), dependencies)
        self.assertNotEqual(sha256(header), sha256(shadow))

    def test_make_dependency_quotes_are_literal_characters(self):
        contents = 'cpp-input: a\'b\'.hpp "double-quote".hpp\n'
        paths = extractor.dependency_paths(contents, self.root)
        expected = [str((self.root / name).resolve())
                    for name in ("a'b'.hpp", '"double-quote".hpp')]
        self.assertEqual(paths, sorted(expected))

    def test_make_dependency_escapes_and_continuations_are_decoded(self):
        contents = (
            "cpp-input: space\\ name.hpp hash\\#name.hpp dollar$$name.hpp \\\n"
            "  back\\\\slash.hpp tab\\\tname.hpp plain.hpp\n"
        )
        paths = extractor.dependency_paths(contents, self.root)
        expected = [str((self.root / name).resolve()) for name in (
            "space name.hpp", "hash#name.hpp", "dollar$name.hpp",
            "back\\\\slash.hpp", "tab\tname.hpp", "plain.hpp",
        )]
        self.assertEqual(paths, sorted(expected))

    def test_make_backslash_runs_preserve_literal_filename_characters(self):
        cases = (
            ("back\\slash.hpp", ["back\\slash.hpp"]),
            ("odd" + "\\" * 3 + " name.hpp", ["odd\\ name.hpp"]),
            ("even" + "\\" * 2 + " plain.hpp", ["even\\", "plain.hpp"]),
            ("hash" + "\\" * 3 + "#name.hpp", ["hash\\#name.hpp"]),
        )
        for contents, names in cases:
            with self.subTest(contents=contents):
                paths = extractor.dependency_paths("cpp-input: " + contents, self.root)
                expected = [str((self.root / name).resolve()) for name in names]
                self.assertEqual(paths, sorted(expected))

    def test_make_continuations_separate_dependency_names(self):
        for continuation in ("\\\n", "\\\r\n"):
            with self.subTest(continuation=continuation):
                contents = "cpp-input: first.hpp" + continuation + "second.hpp\n"
                expected = [str((self.root / name).resolve())
                            for name in ("first.hpp", "second.hpp")]
                self.assertEqual(extractor.dependency_paths(contents, self.root), expected)

    def test_unescaped_make_variables_and_comments_are_refused(self):
        for contents in ("$name.hpp", "$(ROOT)/name.hpp", "hash#name.hpp"):
            with self.subTest(contents=contents):
                with self.assertRaises(extractor.ExtractionError):
                    extractor.dependency_paths("cpp-input: " + contents, self.root)

    def test_special_character_header_paths_keep_their_hashes(self):
        header = self.write("space #$.hpp", "inline constexpr int value = 3;\n")
        self.source.write_text('#include "space #$.hpp"\n', encoding="utf-8")
        dependencies = self.dependency_map(self.envelope())
        self.assertIn(header.resolve(), dependencies)
        self.assertEqual(dependencies[header.resolve()], sha256(header))

    def test_header_changes_update_the_dependency_hash(self):
        header = self.write("value.hpp", "inline constexpr int value = 3;\n")
        self.source.write_text('#include "value.hpp"\n', encoding="utf-8")
        initial = self.envelope()
        initial_hash = self.dependency_map(initial)[header.resolve()]
        header.write_text("inline constexpr int value = 7;\n", encoding="utf-8")
        updated = self.envelope()
        self.assertEqual(initial["source_sha256"], updated["source_sha256"])
        self.assertNotEqual(initial_hash, self.dependency_map(updated)[header.resolve()])
        self.assertNotEqual(normalized_ast(initial["ast"]), normalized_ast(updated["ast"]))

    def test_different_language_editions_are_refused(self):
        for flag in ("--std=c++20", "-std=c++20"):
            with self.subTest(flag=flag):
                with self.assertRaises(extractor.ExtractionError):
                    self.envelope(flags=[flag])

    def test_response_files_are_refused_even_for_harmless_arguments(self):
        response = self.write("frontend.rsp", "-DVALUE=3\n")
        with self.assertRaises(extractor.ExtractionError):
            self.envelope(flags=["@" + str(response)])

    def test_modules_and_precompiled_inputs_are_refused(self):
        precompiled = str(self.root / "input.pch")
        module = str(self.root / "input.pcm")
        cases = [
            ["-fmodules"], ["-fcxx-modules"],
            ["-fmodule-file=" + module], ["-fmodule-file=fixture=" + module],
            ["-fmodule-map-file=" + str(self.root / "module.modulemap")],
            ["-fprebuilt-module-path=" + str(self.root)],
            ["-include-pch", precompiled], ["-include-pch=" + precompiled],
            ["-Xclang", "-include-pch", "-Xclang", precompiled],
        ]
        for flags in cases:
            with self.subTest(flags=flags):
                with self.assertRaises(extractor.ExtractionError):
                    self.envelope(flags=flags)

    def test_nonzero_clang_partial_ast_is_never_an_envelope(self):
        self.source.write_text(
            "int valid() { return 1; }\nint invalid() { return missing_name; }\n",
            encoding="utf-8",
        )
        partial = self.run_command([
            self.clang, "-std=c++23", "-fsyntax-only", "-Xclang", "-ast-dump=json",
            str(self.source),
        ])
        self.assertNotEqual(partial.returncode, 0)
        self.assertEqual(json.loads(partial.stdout)["kind"], "TranslationUnitDecl")
        with self.assertRaises(extractor.ExtractionError):
            self.envelope()

    def test_missing_source_is_a_named_extraction_error(self):
        with self.assertRaises(extractor.ExtractionError):
            self.envelope(source=self.root / "missing.cpp")

    def test_opaque_ast_integer_tokens_remain_exact(self):
        values = (9007199254740993, -9007199254740993, 10**100)
        for value in values:
            with self.subTest(value=value):
                contents = '{"kind":"TranslationUnitDecl","opaque":' + str(value) + '}'
                ast = extractor.parse_ast(contents)
                self.assertEqual(ast["opaque"], value)
                self.assertEqual(json.loads(json.dumps(ast))["opaque"], value)

    def test_fractional_and_exponent_ast_number_tokens_are_refused(self):
        for token in ("1.5", "9007199254740993.0", "0.0", "1e20", "-1E-8"):
            with self.subTest(token=token):
                contents = '{"kind":"TranslationUnitDecl","opaque":' + token + '}'
                with self.assertRaises(extractor.ExtractionError):
                    extractor.parse_ast(contents)

    def test_non_json_numeric_constants_are_refused(self):
        for token in ("NaN", "Infinity", "-Infinity"):
            with self.subTest(token=token):
                contents = '{"kind":"TranslationUnitDecl","opaque":' + token + '}'
                with self.assertRaises(extractor.ExtractionError):
                    extractor.parse_ast(contents)

    def test_cli_stdout_is_a_complete_envelope(self):
        completed = self.run_cli()
        self.assertEqual(completed.returncode, 0, completed.stderr)
        envelope = json.loads(completed.stdout)
        self.assertEqual(envelope["source_sha256"], sha256(self.source))
        self.assertEqual(envelope["ast"]["kind"], "TranslationUnitDecl")

    def test_cli_output_keeps_raw_ast_and_flags(self):
        output = self.root / "output.json"
        flags = ["-DADMITTED_VALUE=17"]
        self.source.write_text("int value = ADMITTED_VALUE;\n", encoding="utf-8")
        completed = self.run_cli(output=output, flags=flags)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        envelope = json.loads(output.read_text(encoding="utf-8"))
        self.assertIn(flags[0], envelope["frontend"]["argv"])
        expected = self.envelope(flags=flags)
        self.assertEqual(normalized_ast(envelope["ast"]), normalized_ast(expected["ast"]))

    def test_cli_failure_never_replaces_existing_output(self):
        output = self.root / "existing.json"
        original = b'{"preserve":"the previous extraction"}\n'
        output.write_bytes(original)
        invalid = self.write("invalid.cpp", "int value = missing_name;\n")
        cases = [(invalid, None), (self.source, ["--std=c++20"])]
        for source, flags in cases:
            with self.subTest(source=source, flags=flags):
                completed = self.run_cli(source=source, output=output, flags=flags)
                self.assertNotEqual(completed.returncode, 0)
                self.assertEqual(output.read_bytes(), original)

    def test_cli_failure_never_creates_a_partial_output(self):
        output = self.root / "absent.json"
        invalid = self.write("invalid.cpp", "int value = missing_name;\n")
        completed = self.run_cli(source=invalid, output=output)
        self.assertNotEqual(completed.returncode, 0)
        self.assertFalse(output.exists())

    def output_alias(self, target, kind):
        if kind == "direct":
            return target
        directory = self.root / "aliases"
        directory.mkdir(exist_ok=True)
        if kind == "normalized":
            return directory / ".." / target.name
        output = directory / (kind + "-" + target.name)
        if kind == "symlink":
            output.symlink_to(target)
        else:
            os.link(target, output)
        return output

    def test_cli_output_never_replaces_source_or_dependency_aliases(self):
        source_contents = b'#include "value.hpp"\nint result = value;\n'
        header_contents = b"inline constexpr int value = 3;\n"
        header = self.write("value.hpp", header_contents.decode("utf-8"))
        for target in (self.source, header):
            for kind in ("direct", "normalized", "symlink", "hardlink"):
                with self.subTest(target=target.name, kind=kind):
                    self.source.write_bytes(source_contents)
                    header.write_bytes(header_contents)
                    original = target.read_bytes()
                    output = self.output_alias(target, kind)
                    completed = self.run_cli(output=output)
                    self.assertEqual(completed.returncode, 2, completed.stderr)
                    self.assertIn("refused", completed.stderr)
                    self.assertEqual(self.source.read_bytes(), source_contents)
                    self.assertEqual(header.read_bytes(), header_contents)
                    self.assertEqual(output.read_bytes(), original)
                    if kind == "symlink":
                        self.assertTrue(output.is_symlink())

    @unittest.skipUnless(os.environ.get("LEANCPP_TEST_LEAN") == "1", "set LEANCPP_TEST_LEAN=1 after building LeanModels.Cpp")
    def test_lean_import_preserves_unknown_fields_and_refuses_execution(self):
        self.assertTrue((REPO_ROOT / ".lake/build/lib/lean/LeanModels/Cpp.olean").is_file())
        lake = shutil.which("lake")
        self.assertIsNotNone(lake, "Lean integration requires the pinned Lake executable")
        envelope = self.declaration_envelope()
        artifact = self.write("artifact.json", json.dumps(envelope))
        expected_paths = "[" + ", ".join(
            "(" + json.dumps(identifier) + ", " + json.dumps(path) + ")"
            for identifier, path in declaration_occurrence_paths(envelope["ast"])
        ) + "]"
        declaration_id = next(
            node["id"] for node in ast_nodes(envelope["ast"])
            if node["kind"] == "FunctionDecl" and node.get("name") == "pick"
        )
        synthetic = json.loads(json.dumps(envelope))
        synthetic["ast"]["opaque_test_child"] = {
            "kind": "OpaqueFutureNode",
            "payload": {"retained": [True, None, "native metadata"]},
        }
        opaque_artifact = self.write("synthetic-import-only.json", json.dumps(synthetic))
        lean_source = "\n".join([
            "import LeanModels.Cpp",
            "open LeanModels.Cpp",
            "load_cpp_artifact probe from " + json.dumps(str(artifact)),
            "#guard probe.sourceSha256 == " + json.dumps(envelope["source_sha256"]),
            '#guard probe.ast.text "kind" == some "TranslationUnitDecl"',
            '#guard probe.declarations.any (fun declaration => declaration.kind == "FunctionDecl" && declaration.name == some "pick")',
            "#guard probe.declarations.map (fun declaration => (declaration.id, declaration.path)) == " + expected_paths,
            "#guard execute probe " + json.dumps(declaration_id) + " matches .error _",
            "load_cpp_artifact syntheticProbe from " + json.dumps(str(opaque_artifact)),
            '#guard ((syntheticProbe.ast.field "opaque_test_child").bind (fun child => child.text "kind")) == some "OpaqueFutureNode"',
            '#guard (((syntheticProbe.ast.field "opaque_test_child").bind (fun child => child.field "payload")).bind (fun payload => payload.field "retained")) == some (.array [.bool true, .null, .string "native metadata"])',
            "",
        ])
        lean_file = self.write("import-regression.lean", lean_source)
        completed = self.run_command([lake, "env", "lean", str(lean_file)], cwd=REPO_ROOT)
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)


if __name__ == "__main__":
    unittest.main()
