#!/usr/bin/env python3
"""Unit checks for C++ oracle-status accounting."""

import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "cpp_diff_test_under_test", ROOT / "harness" / "cpp_diff_test.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class CheckExecutionTests(unittest.TestCase):
    def test_assertion_failure_is_divergence(self):
        self.assertEqual(
            MODULE.classify_check_execution(3, "", ""),
            ("DIVERGE", "native assertion failed (exit 3)"))

    def test_success_is_native(self):
        self.assertEqual(
            MODULE.classify_check_execution(0, "ok\n", ""), ("NATIVE", "ok"))

    def test_protocol_failure_is_oracle(self):
        self.assertEqual(
            MODULE.classify_check_execution(0, "unexpected\n", ""),
            ("ORACLE", "check witness protocol failed: expected 'ok'"))

    def test_runtime_failure_is_oracle(self):
        self.assertEqual(
            MODULE.classify_check_execution(1, "", "runtime failed\n"),
            ("ORACLE", "check witness exited 1: runtime failed"))

    def test_differential_preserves_native_divergence(self):
        row = {"id": "check", "corpus": "test", "kind": "scalar", "rung": 2}
        result = MODULE.differential(
            [row], {"check": "ok true"},
            {"check": ("DIVERGE", "native assertion failed (exit 3)")})
        self.assertEqual(result[0]["verdict"], "DIVERGE")
        self.assertEqual(result[0]["detail"], "native assertion failed (exit 3)")


if __name__ == "__main__":
    unittest.main()
