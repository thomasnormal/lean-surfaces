#!/usr/bin/env python3
"""Focused checks for the module frontend-boundary probe."""

import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "cpp_module_probe_under_test", ROOT / "harness" / "cpp_module_probe.py")
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ModuleProbeTests(unittest.TestCase):
    def test_witness_is_a_module_unit(self):
        self.assertIn("export module", MODULE.SOURCE)

    def test_json_kind_walk_is_structured(self):
        self.assertEqual(
            sorted(set(MODULE.kinds({"kind": "TranslationUnitDecl",
                                      "inner": [{"kind": "ModuleDecl"}]}))),
            ["ModuleDecl", "TranslationUnitDecl"])


if __name__ == "__main__":
    unittest.main()
