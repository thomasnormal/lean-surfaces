#!/usr/bin/env python3
"""Check refusal inventories and their fail-closed census contracts."""

from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import unittest
from unittest.mock import mock_open, patch

import refusal_census


REPO_ROOT = Path(__file__).resolve().parent.parent


class RefusalCensusTests(unittest.TestCase):
    def test_whitelist_inventory_is_classified(self):
        cases = json.loads((REPO_ROOT / "harness/cases.json").read_text())
        keys = {
            Path(case["file"]).stem + "::" + case["function"]
            for case in cases if case.get("expect") == "unsupported"
        }
        self.assertTrue(keys)
        self.assertEqual(keys - refusal_census.WHITELIST_CLASS.keys(), set())

    def test_script_inventory_is_classified(self):
        scripts = json.loads((REPO_ROOT / "harness/scripts.json").read_text())
        keys = {
            Path(script["file"]).stem
            for script in scripts if script.get("expect") == "unsupported"
        }
        self.assertTrue(keys)
        self.assertEqual(keys - refusal_census.SCRIPT_CLASS.keys(), set())

    def test_missing_whitelist_class_fails(self):
        case = {"file": "fixture.py", "function": "missing", "args": [[]],
                "expect": "unsupported"}
        with patch("builtins.open", mock_open(read_data=json.dumps([case]))), \
                patch.object(refusal_census, "run_batch", return_value=[]), \
                redirect_stdout(io.StringIO()) as output:
            self.assertEqual(refusal_census.whitelist_census(["stub"]), 1)
        self.assertIn("no class in WHITELIST_CLASS", output.getvalue())

    def test_missing_script_class_fails(self):
        script = {"file": "missing.py", "expect": "unsupported"}
        with patch("builtins.open", mock_open(read_data=json.dumps([script]))), \
                patch.object(refusal_census, "run_batch", return_value=[]), \
                redirect_stdout(io.StringIO()) as output:
            self.assertEqual(refusal_census.scripts_census(["stub"]), 1)
        self.assertIn("no class in SCRIPT_CLASS", output.getvalue())

    def test_decided_whitelisted_row_fails(self):
        case = {"file": "fixture.py", "function": "loud", "args": [[]],
                "expect": "unsupported"}
        with patch("builtins.open", mock_open(read_data=json.dumps([case]))), \
                patch.dict(refusal_census.WHITELIST_CLASS, {"fixture::loud": "test"}), \
                patch.object(refusal_census, "run_batch", return_value=[{"status": "ok"}]), \
                redirect_stdout(io.StringIO()) as output:
            self.assertEqual(refusal_census.whitelist_census(["stub"]), 1)
        self.assertIn("model answered", output.getvalue())

    def test_runner_error_whitelisted_row_fails(self):
        case = {"file": "fixture.py", "function": "loud", "args": [[]],
                "expect": "unsupported"}
        with patch("builtins.open", mock_open(read_data=json.dumps([case]))), \
                patch.dict(refusal_census.WHITELIST_CLASS, {"fixture::loud": "test"}), \
                patch.object(refusal_census, "run_batch", return_value=[{"status": "runner-error"}]), \
                redirect_stdout(io.StringIO()) as output:
            self.assertEqual(refusal_census.whitelist_census(["stub"]), 1)
        self.assertIn("model answered runner-error", output.getvalue())

    def test_float_whitelist_jobs_use_exact_transport(self):
        case = {"file": "fixture.py", "function": "loud", "fuel": 32,
                "args": [[1.5, -0.0, True,
                          {"t": "tuple", "v": [-0.0, {"t": "float", "bits": "1"}]}]],
                "expect": "unsupported"}
        with patch("builtins.open", mock_open(read_data=json.dumps([case]))), \
                patch.dict(refusal_census.WHITELIST_CLASS, {"fixture::loud": "test"}), \
                patch.object(refusal_census, "run_batch", return_value=[{"status": "unsupported"}]) as batch, \
                redirect_stdout(io.StringIO()):
            self.assertEqual(refusal_census.whitelist_census(["stub"]), 0)
        jobs = batch.call_args.args[1]
        self.assertEqual(len(jobs), 1)
        self.assertEqual(json.loads(jobs[0]), {
            "path": "fixture.json", "function": "loud", "fuel": 32,
            "args": [{"t": "float", "bits": "4609434218613702656"},
                     {"t": "float", "bits": "9223372036854775808"},
                     {"t": "bool", "v": True},
                     {"t": "tuple", "v": [
                         {"t": "float", "bits": "9223372036854775808"},
                         {"t": "float", "bits": "1"}]}]})

    def test_decided_loud_script_fails(self):
        script = {"file": "fixture.py", "expect": "unsupported"}
        with patch("builtins.open", mock_open(read_data=json.dumps([script]))), \
                patch.dict(refusal_census.SCRIPT_CLASS, {"fixture": "test"}), \
                patch.object(refusal_census.leanpy, "envelope_for", return_value="fixture.json"), \
                patch.object(refusal_census, "run_batch", return_value=[{"status": "ok"}]), \
                redirect_stdout(io.StringIO()) as output:
            self.assertEqual(refusal_census.scripts_census(["stub"]), 1)
        self.assertIn("model answered", output.getvalue())

    def test_ci_runs_both_censuses_without_building(self):
        lines = (REPO_ROOT / "tools/ci.sh").read_text().splitlines()
        self.assertEqual(lines.count(
            'step  "py-refusal-census-tests" python3 harness/test_refusal_census.py'), 1)
        self.assertEqual(lines.count(
            'step  "py-refusal-census" python3 harness/refusal_census.py '
            '--whitelist --scripts --no-build --runner .lake/build/bin/leanmodels-run'), 1)


if __name__ == "__main__":
    unittest.main()
