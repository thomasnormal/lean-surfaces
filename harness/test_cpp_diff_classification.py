#!/usr/bin/env python3
"""Regression checks for the C++ coverage evidence boundary."""

import hashlib
import json
import pathlib
import tempfile
import unittest
from unittest import mock

import cpp_diff_test as driver


class EvidenceClassificationTest(unittest.TestCase):
    def row(self, kind="statement", expect="match"):
        return {"id": "case", "corpus": "fixture", "kind": kind,
                "rung": 4, "expect": expect}

    def classify(self, row, model, native):
        return driver.differential([row], {"case": model}, {"case": native})[0]["verdict"]

    def test_independent_pass_is_only_a_witness(self):
        self.assertEqual(self.classify(self.row(), "ok", ("NATIVE", "ok")), "WITNESS")
        self.assertEqual(self.classify(self.row("callable"), "ok 1", ("NATIVE", "1")), "WITNESS")

    def test_failure_refusal_and_missing_oracle_remain_visible(self):
        self.assertEqual(self.classify(self.row(), "ok", ("DIVERGE", "native assertion failed")), "DIVERGE")
        self.assertEqual(self.classify(self.row(expect="refuse"), "refuse", ("NATIVE", "ok")), "REFUSE")
        self.assertEqual(self.classify(self.row(), "ok", ("ORACLE", "missing compiler")), "ORACLE")

    def test_coverage_table_does_not_count_witness_as_match(self):
        rows = driver.differential([self.row()], {"case": "ok"}, {"case": ("NATIVE", "ok")})
        coverage = driver.render_coverage(rows, [])
        rung = driver.render_rung_page(rows, [])
        self.assertIn("| 1 | 0 | 1 | 0 | 0 | 0 | 0 |", coverage)
        self.assertIn("| differential and independent witnesses | 1 | 0 | 1 | 0 | 0 | 0 | 0 |", rung)

    def test_capture_checks_source_literal_and_both_call_arguments(self):
        row = {"id": "case", "corpus": "TinyXML-2", "args": [-1],
               "lean_module": "Examples.cpp.tinyxml2.proof",
               "lean_namespace": "Examples.cpp.tinyxml2.IsUTF8Continuation",
               "lean_expression": "observed (-1)",
               "cpp_expression": "tinyxml2::XMLUtil::IsUTF8Continuation(static_cast<char>({arg}))"}
        digest = lambda data: hashlib.sha256(data).hexdigest()
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            example = root / "Examples/cpp/tinyxml2"
            corpus = root / "corpus"
            example.mkdir(parents=True)
            corpus.mkdir()
            (corpus / "tinyxml2.h").write_bytes(b"header")
            (corpus / "tinyxml2.cpp").write_bytes(b"implementation")
            literal = example / "IsUTF8Continuation.lean"
            literal.write_bytes(b"captured literal")
            manifest = {"format": "cpp-original-callable-1",
                        "source_revision": "321ea883b7190d4e85cae5512a12e5eaa8f8731f",
                        "frontend": "Clang/LLVM 21.1.8",
                        "source_declaration": "tinyxml2::XMLUtil::IsUTF8Continuation",
                        "source_sha256": {"tinyxml2.h": digest(b"header"),
                                          "tinyxml2.cpp": digest(b"implementation")},
                        "literal_sha256": digest(b"captured literal")}
            (example / "provenance.json").write_text(json.dumps(manifest))
            with mock.patch.object(driver, "ROOT", root):
                self.assertTrue(driver.tinyxml_capture_verified(row, corpus))
                self.assertFalse(driver.tinyxml_capture_verified(dict(row, lean_expression="observed 0"), corpus))
                self.assertFalse(driver.tinyxml_capture_verified(dict(row, cpp_expression="other({arg})"), corpus))
                self.assertFalse(driver.tinyxml_capture_verified(dict(row, args=[256]), corpus))
                literal.write_bytes(b"changed literal")
                self.assertFalse(driver.tinyxml_capture_verified(row, corpus))
                literal.write_bytes(b"captured literal")
                (corpus / "tinyxml2.h").write_bytes(b"changed header")
                self.assertFalse(driver.tinyxml_capture_verified(row, corpus))

    def test_only_verified_native_capture_is_a_match(self):
        self.assertEqual(self.classify(self.row("callable"), "ok 1", ("NATIVE_CAPTURED", "1")), "MATCH")
        self.assertEqual(self.classify(self.row("callable"), "ok 0", ("NATIVE_CAPTURED", "1")), "DIVERGE")

    def test_clang_version_must_match_a_whole_release(self):
        result = mock.Mock(returncode=0, stdout="clang version 21.1.80\n", stderr="")
        with mock.patch.dict(driver.os.environ, {"LEANCPP_CLANG": "/test/clang++"}), \
             mock.patch.object(driver.os.path, "exists", return_value=True), \
             mock.patch.object(driver, "run", return_value=result):
            compiler, _ = driver.clang_info()
        self.assertIsNone(compiler)

    def test_model_launch_does_not_set_an_address_space_limit(self):
        row = dict(self.row(), lean_module="LeanModels.Cpp", lean_expression="true")
        result = mock.Mock(returncode=0, stdout="CPPCASE|case|ok\n", stderr="")
        with mock.patch.object(driver, "run", return_value=result) as run:
            self.assertEqual(driver.model_rows([row]), {"case": "ok"})
        command = run.call_args.args[0]
        self.assertEqual(command[:4], ["lake", "env", "lean", "-j"])
        self.assertNotIn("prlimit", command)

    def test_captured_callable_is_built_before_observation(self):
        row = dict(self.row("callable"), lean_module="Examples.cpp.tinyxml2.proof",
                   lean_expression="observed 0")
        build = mock.Mock(returncode=0, stdout="", stderr="")
        observation = mock.Mock(returncode=0, stdout="CPPCASE|case|ok 0\n", stderr="")
        with mock.patch.object(driver, "run", side_effect=[build, observation]) as run:
            self.assertEqual(driver.model_rows([row]), {"case": "ok 0"})
        self.assertEqual(run.call_args_list[0].args[0], ["lake", "build", "Examples.cpp.tinyxml2.proof"])
        self.assertEqual(run.call_args_list[1].args[0][:3], ["lake", "env", "lean"])
        failed = mock.Mock(returncode=1, stdout="", stderr="build failed")
        with mock.patch.object(driver, "run", return_value=failed) as run:
            with self.assertRaisesRegex(RuntimeError, "captured callable build failed"):
                driver.model_rows([row])
        self.assertEqual(run.call_count, 1)


if __name__ == "__main__":
    unittest.main()
