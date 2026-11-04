#!/usr/bin/env python3
"""End-to-end controls for runtime callable census, not corpus execution."""

import copy
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
DRIVER = ROOT / "extractors/cpp/census_callable.lean"


@unittest.skipUnless(os.environ.get("LEANCPP_TEST_LEAN") == "1", "set LEANCPP_TEST_LEAN=1")
class CallableCensusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lake = shutil.which("lake")
        cls.clang = shutil.which(os.environ.get("LEANCPP_CLANG", ""))
        cls.plugin = pathlib.Path(os.environ.get("LEANCPP_PROBE_LIBRARY", ""))
        if cls.lake is None or cls.clang is None or not cls.plugin.is_file():
            raise RuntimeError("select Lake and the matching Clang/probe library")
        cls.directory = tempfile.TemporaryDirectory(prefix="cpp-callable-census-")
        cls.addClassCleanup(cls.directory.cleanup)
        cls.root = pathlib.Path(cls.directory.name)
        cls.header = cls.root / "dependency.h"
        cls.header.write_text('''inline int dependency() { return 1; }
#define MAKE_FUNCTION int macro_function() { return 2; }
''', encoding="utf-8")
        cls.source = cls.root / "input.cpp"
        cls.source.write_text('''#include "dependency.h"
MAKE_FUNCTION
#line 400 "unrelated.cpp"
int accepted(int x) { return x + 1; }
int call() { return accepted(2); }
struct Box { int method() { return 3; } };
template<class T> T generic(T x) { return x; }
int instantiate() { return generic(2); }
''', encoding="utf-8")
        result = subprocess.run([
            cls.clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", str(cls.source), "-Xclang", "-load", "-Xclang",
            str(cls.plugin.resolve()), "-Xclang", "-plugin", "-Xclang",
            "leancpp-canonical-probe",
        ], cwd=ROOT, capture_output=True, text=True, timeout=30)
        if result.returncode:
            raise RuntimeError(result.stderr)
        cls.probe = json.loads(result.stdout)

    def run_census(self, probe=None, sources=None, path=None):
        if path is None:
            path = self.root / "probe.json"
            path.write_text(json.dumps(self.probe if probe is None else probe), encoding="utf-8")
        result = subprocess.run([
            self.lake, "env", "lean", "-j", "1", "--run", str(DRIVER), str(path),
            "--sources", *(str(source) for source in (sources or [self.source])),
        ], cwd=ROOT, capture_output=True, text=True, timeout=90)
        self.assertIn(result.returncode, (0, 2), result.stdout + result.stderr)
        return result, json.loads(result.stdout)

    def test_real_probe_counts_admission_refusals_and_source_origins(self):
        result, report = self.run_census()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(report["status"], "COMPLETE")
        self.assertEqual(report["execution"], "not-attempted")
        bodies = report["bodies"]
        self.assertEqual(report["body_occurrences"], len(bodies))
        self.assertEqual(len({tuple(row["path"]) for row in bodies}), len(bodies))
        named = {name: [row for row in bodies if row["name"] == name]
                 for name in ("accepted", "call", "method", "generic", "dependency", "macro_function")}
        accepted, = named["accepted"]
        self.assertTrue(accepted["admitted"])
        self.assertEqual(accepted["ownership"], "target-source")
        self.assertIsNone(accepted["first_refusal"])
        call, = named["call"]
        self.assertFalse(call["admitted"])
        self.assertIn("CallExpr", call["first_refusal"])
        self.assertIn("CallExpr", call["body_kinds"])
        method, = named["method"]
        self.assertEqual(method["first_refusal"], "local function: requires FunctionDecl")
        self.assertEqual(len(named["generic"]), 2, "retain template pattern and instantiation")
        self.assertTrue(all(not row["admitted"] for row in named["generic"]))
        self.assertEqual(named["dependency"][0]["ownership"], "dependency")
        self.assertEqual(named["macro_function"][0]["ownership"], "mixed-macro")
        self.assertEqual(report["target_explicit_bodies"], 6)
        self.assertEqual(report["target_explicit_admitted"], 1)
        self.assertEqual(report["target_explicit_refused"], 5)
        self.assertEqual(sum(report["target_first_refusals"].values()), 5)

        # Selecting the header explicitly makes the macro's two physical origins
        # source-owned. A symlink spelling selects the same physical main source.
        alias = self.root / "source-alias.cpp"
        alias.symlink_to(self.source)
        result, report = self.run_census(sources=[alias, self.header])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(report["ownership_counts"], {"target-source": 8})
        self.assertEqual(report["target_explicit_admitted"], 3)

    def test_missing_origin_does_not_guess_from_elided_ast_locations(self):
        probe = copy.deepcopy(self.probe)
        row, = [row for row in probe["metadata"]["declarations"] if row.get("name") == "accepted"]
        del row["source_origin_api"]
        result, report = self.run_census(probe)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(report["stage"], "source-origin")

    def test_unavailable_origin_stays_unknown_and_conflicting_rows_refuse(self):
        probe = copy.deepcopy(self.probe)
        row, = [row for row in probe["metadata"]["declarations"] if row.get("name") == "accepted"]
        row["source_origin"]["expansion"] = None
        result, report = self.run_census(probe)
        self.assertEqual(result.returncode, 0, result.stderr)
        accepted, = [row for row in report["bodies"] if row["name"] == "accepted"]
        self.assertEqual(accepted["ownership"], "unknown-origin")
        self.assertTrue(accepted["admitted"])
        self.assertEqual(report["target_explicit_admitted"], 0)
        self.assertEqual(report["target_explicit_bodies"], 5)
        conflict = copy.deepcopy(row)
        conflict["source_origin"]["expansion"] = {"file": str(self.source), "offset": 0}
        probe["metadata"]["declarations"].append(conflict)
        result, report = self.run_census(probe)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(report["stage"], "source-origin")
        self.assertEqual(report["reason"], "source origin: conflicting declaration metadata")

    def test_whole_probe_binary_validation_precedes_body_selection(self):
        probe = copy.deepcopy(self.probe)
        probe["metadata"]["expression_evidence"][0]["occurrence"] = "0xdeadbeef"
        result, report = self.run_census(probe)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(report["stage"], "binary-evidence")
        self.assertEqual(report["reason"], "expression evidence occurrence is absent from AST")

    def test_input_bound_is_a_resource_rejection_before_json_parsing(self):
        path = self.root / "oversized.json"
        with path.open("wb") as output:
            output.truncate(128 * 1024 * 1024 + 1)
        result, report = self.run_census(path=path)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(report["stage"], "input-byte-bound")


if __name__ == "__main__":
    unittest.main()
