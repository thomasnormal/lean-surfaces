#!/usr/bin/env python3
"""Check the bounded Clang-dump token observer, not a general JSON parser."""

import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest


HERE = pathlib.Path(__file__).resolve().parent


class DumpReachabilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        requested = os.environ.get("LEANCPP_CLANG", "c++")
        cls.compiler = shutil.which(requested)
        if cls.compiler is None:
            raise unittest.SkipTest("dump observer checks require a C++17 compiler")
        cls.directory = tempfile.TemporaryDirectory(prefix="cpp-dump-observer-")
        cls.addClassCleanup(cls.directory.cleanup)
        cls.runner = pathlib.Path(cls.directory.name) / "observer"
        arguments = [cls.compiler, "-std=c++17", str(HERE / "dump_reachability_runner.cpp"),
                     "-o", str(cls.runner)]
        if os.environ.get("LEANCPP_CLANG"):
            arguments.insert(1, "--no-default-config")
        result = subprocess.run(arguments, capture_output=True, text=True, timeout=60)
        if result.returncode != 0:
            raise RuntimeError(result.stdout + result.stderr)

    def observe(self, text, chunk, ast=False):
        return subprocess.run([str(self.runner), str(chunk)] + (["ast"] if ast else []), input=text,
                              capture_output=True, text=True, timeout=10)

    def assert_ids(self, document, expected, ast=False):
        text = json.dumps(document, ensure_ascii=True)
        for chunk in (1, 2, 3, 7, 64, 127, len(text) + 1):
            with self.subTest(chunk=chunk):
                result = self.observe(text, chunk, ast)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.splitlines(), sorted(expected))

    def test_nested_objects_field_order_and_compound_operators(self):
        self.assert_ids({"kind": "TranslationUnitDecl", "id": "0x1", "inner": [
            {"kind": "BinaryOperator", "id": "0x2", "inner": [
                {"id": "0x3", "kind": "CompoundAssignOperator"}]},
            {"id": "0x4", "kind": "DeclRefExpr", "referencedDecl": {
                "id": "0x5", "kind": "FunctionDecl"}},
        ]}, {"0x2", "0x3"})

    def test_textual_fake_fields_and_escaped_payloads_do_not_join(self):
        self.assert_ids({"id": "0x1", "kind": "StringLiteral",
                         "value": '"id":"0xdead","kind":"BinaryOperator"\\\"{}[]',
                         "inner": [{"id": "0x2", "kind": "BinaryOperator"}]}, {"0x2"})

    def test_long_payloads_and_missing_node_fields_do_not_join(self):
        self.assert_ids({"inner": [
            {"kind": "BinaryOperator"}, {"id": "0x1"},
            {"id": "0x2", "kind": "BinaryOperator", "value": "x" * 100000},
            {"id": "0x3", "kind": "BinaryOperator" + "x" * 100},
        ]}, {"0x2"})

    def test_arrays_and_repeated_occurrences_preserve_identity(self):
        self.assert_ids({"inner": [
            [{"id": "0x2", "kind": "BinaryOperator"}],
            {"kind": "BinaryOperator", "id": "0x2", "values": [None, True, 17]},
            {"kind": "CompoundAssignOperator", "id": "0x3"},
        ]}, {"0x2", "0x3"})

    def test_ast_mode_only_witnesses_root_and_direct_inner_edges(self):
        self.assert_ids({"kind": "TranslationUnitDecl", "id": "0x1", "inner": [
            {"kind": "VarDecl", "id": "0x2", "inner": [
                {"kind": "IntegerLiteral", "id": "0x3"}],
             "type": {"id": "0x4", "kind": "RecordType", "inner": [
                 {"kind": "VarDecl", "id": "0x5"}]}},
            {"id": "0x6", "kind": "DeclRefExpr", "referencedDecl": {
                "id": "0x7", "kind": "VarDecl"}},
            [{"id": "0x8", "kind": "VarDecl"}],
        ], "payload": {"id": "0x9", "kind": "VarDecl"}},
            {"0x1", "0x2", "0x3", "0x6"}, ast=True)

    def test_ast_mode_rejects_non_array_inner_and_array_root(self):
        self.assert_ids({"id": "0x1", "kind": "VarDecl", "inner": {
            "id": "0x2", "kind": "IntegerLiteral"}}, {"0x1"}, ast=True)
        self.assert_ids([{"id": "0x1", "kind": "VarDecl"}], set(), ast=True)

    def test_unfinished_strings_containers_and_mismatched_delimiters_fail(self):
        for text in ('{"id": "0x1', '{"inner": [}', '{"inner": [', '}', '[}'):
            with self.subTest(text=text):
                result = self.observe(text, 1)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(result.stderr, "")


if __name__ == "__main__":
    unittest.main()
