#!/usr/bin/env python3
"""Exercise the scoped check plan and CLI without launching Lean or notebooks."""

from contextlib import redirect_stderr, redirect_stdout
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import check_python


class PythonCheckPlanTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="python-check-tests-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name) / "checkout with spaces"
        self.root.mkdir()
        for relative in (
            "LeanModels/Python.lean", "LeanModels/Python/Tests.lean",
            "Examples/python/example/spec.lean", "Examples/python/example/proof.lean",
            "LeanModels/Other/Tests.lean", "Examples/other/example/spec.lean",
        ):
            source = self.root / relative
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("", encoding="utf-8")
        runner = self.root / ".lake/build/bin/leanmodels-run"
        runner.parent.mkdir(parents=True)
        runner.write_text("", encoding="utf-8")
        runner.chmod(0o755)

    def invoke(self, arguments=(), environment=None, statuses=None):
        observed = []

        def execute(command, cwd):
            self.assertEqual(cwd, self.root)
            observed.append(command)
            return subprocess.CompletedProcess(command, (statuses or {}).get(len(observed), 0))

        output = io.StringIO()
        errors = io.StringIO()
        with patch.object(check_python, "ROOT", self.root), \
                patch.object(check_python.subprocess, "run", side_effect=execute), \
                patch.dict(os.environ, environment or {}, clear=True), \
                redirect_stdout(output), redirect_stderr(errors):
            result = check_python.main(arguments)
        return result, observed, output.getvalue(), errors.getvalue()

    def test_build_targets_discover_only_python_sources_and_runner(self):
        self.assertEqual(check_python.build_targets(self.root), [
            "LeanModels/Python.lean", "LeanModels/Python/Tests.lean",
            "Examples/python/example/proof.lean", "Examples/python/example/spec.lean",
            "leanmodels-run",
        ])

    def test_missing_python_source_tree_fails_instead_of_narrowing_the_build(self):
        shutil.rmtree(self.root / "Examples/python")
        result, observed, output, errors = self.invoke(environment={"GITHUB_ACTIONS": "true"})
        self.assertEqual(result, 1)
        self.assertEqual(observed, [])
        self.assertIn("no Lean sources", errors)

    def test_plan_keeps_both_interpreters_scripts_refusals_and_coverage(self):
        plan = dict(check_python.acceptance_gates(self.root))
        self.assertIn("--proof-interpreter", plan["py-proof-interpreter"])
        self.assertNotIn("--proof-interpreter", plan["py-harness"])
        for name in ("py-harness", "py-proof-interpreter", "py-script-corpus", "py-refusal-census"):
            with self.subTest(name=name):
                self.assertIn("--no-build", plan[name])
                self.assertIn("--runner", plan[name])
        self.assertIn("--check", plan["py-coverage-fresh"])
        self.assertIn("--whitelist", plan["py-refusal-census"])
        self.assertIn("--scripts", plan["py-refusal-census"])

    def test_plan_has_no_foreign_tier_harness_or_notebook(self):
        for name, command in check_python.acceptance_gates(self.root):
            with self.subTest(name=name):
                for argument in command:
                    if argument.startswith("harness/"):
                        self.assertNotIn("/", argument.removeprefix("harness/"))
                    if argument.startswith("extractors/"):
                        self.assertTrue(argument.startswith("extractors/python/"))
                    if argument.endswith(".ipynb"):
                        self.assertIn(argument, (
                            "notebooks/01-pipeline.ipynb", "notebooks/02-loops-interactive.ipynb",
                        ))
        self.assertIn("--no-save", dict(check_python.acceptance_gates(self.root))["python-notebooks"])

    def test_axiom_inventory_matches_full_ci(self):
        source = (check_python.ROOT / "tools/ci.sh").read_text(encoding="utf-8")
        inventory = re.search(r"for e in (.+); do\n    mods\+=", source)
        self.assertIsNotNone(inventory)
        self.assertEqual(tuple(inventory.group(1).split()), check_python.CURATED_EXAMPLES)

    def test_python_gate_inventory_tracks_full_ci(self):
        source = (check_python.ROOT / "tools/ci.sh").read_text(encoding="utf-8")
        full_gates = set(re.findall(
            r'^(?:step|maybe)\s+"((?:py-|leanpy-)[^"\n]+|extractor-tests|notebook-cache-tests|notebook-dependency-tests)"',
            source, re.MULTILINE,
        ))
        self.assertTrue(full_gates)
        scoped_gates = set(dict(check_python.acceptance_gates(self.root)))
        self.assertEqual(full_gates - scoped_gates, set())

    def test_ci_build_is_scoped_and_precedes_acceptance(self):
        result, observed, output, errors = self.invoke(
            ("--require-build",), environment={"GITHUB_ACTIONS": "true"},
        )
        self.assertEqual(result, 0, errors)
        self.assertEqual(observed[0], ["lake", "build", *check_python.build_targets(self.root)])
        self.assertEqual(len(observed), 1 + len(check_python.acceptance_gates(self.root)))
        self.assertIn("not full repository CI", output)

    def test_build_failure_does_not_validate_stale_artifacts(self):
        result, observed, output, errors = self.invoke(
            environment={"GITHUB_ACTIONS": "true"}, statuses={1: 1},
        )
        self.assertEqual(result, 1)
        self.assertEqual(len(observed), 1)
        self.assertIn("stale artifacts", errors)

    def test_gate_failure_remains_failure_and_other_gates_still_run(self):
        result, observed, output, errors = self.invoke(("--no-build",), statuses={2: 7})
        self.assertEqual(result, 1)
        self.assertEqual(len(observed), len(check_python.acceptance_gates(self.root)))
        self.assertIn("FAIL: python-check-tests", output)

    def test_no_build_reuses_existing_artifacts_even_in_ci(self):
        result, observed, output, errors = self.invoke(
            ("--no-build",), environment={"GITHUB_ACTIONS": "true"},
        )
        self.assertEqual(result, 0, errors)
        self.assertFalse(any(command[0] == "lake" for command in observed))
        self.assertIn("SKIP: python-build", output)

    def test_required_build_cannot_skip_on_local_host(self):
        result, observed, output, errors = self.invoke(("--require-build",))
        self.assertEqual(result, 1)
        self.assertEqual(observed, [])
        self.assertIn("does not permit a skipped build", errors)

    def test_missing_runner_fails_before_acceptance_gates(self):
        (self.root / ".lake/build/bin/leanmodels-run").unlink()
        result, observed, output, errors = self.invoke(("--no-build",))
        self.assertEqual(result, 1)
        self.assertEqual(observed, [])
        self.assertIn("required Python runner", errors)

    def test_directory_cannot_masquerade_as_runner(self):
        runner = self.root / ".lake/build/bin/leanmodels-run"
        runner.unlink()
        runner.mkdir()
        result, observed, output, errors = self.invoke(("--no-build",))
        self.assertEqual(result, 1)
        self.assertEqual(observed, [])
        self.assertIn("required Python runner", errors)

    def test_nonexecutable_runner_fails_before_acceptance_gates(self):
        (self.root / ".lake/build/bin/leanmodels-run").chmod(0o644)
        result, observed, output, errors = self.invoke(("--no-build",))
        self.assertEqual(result, 1)
        self.assertEqual(observed, [])
        self.assertIn("required Python runner", errors)

    def test_cli_refusals_do_not_launch_commands(self):
        for arguments, environment in (
            (("--unknown",), {}),
            (("--require-build", "--no-build"), {}),
            ((), {"LS_CI_SELF_TEST": "already checking"}),
        ):
            with self.subTest(arguments=arguments, environment=environment), \
                    patch.object(check_python.subprocess, "run") as execute, \
                    patch.dict(os.environ, environment, clear=True), \
                    redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as error:
                    check_python.main(arguments)
                self.assertEqual(error.exception.code, 2)
                execute.assert_not_called()


class PythonCheckRoutingTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="python-check-routing-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name) / "checkout with spaces"
        tools = self.root / "tools"
        tools.mkdir(parents=True)
        for relative in ("check.sh", "tools/ci.sh"):
            shutil.copy2(check_python.ROOT / relative, self.root / relative)
        (tools / "check_python.py").write_text(
            "import json, os, sys\n"
            "print(json.dumps({'arguments': sys.argv[1:], 'directory': os.getcwd()}))\n"
            "raise SystemExit(int(os.environ.get('CHECK_TEST_EXIT', '0')))\n",
            encoding="utf-8",
        )

    def invoke(self, arguments, environment=None):
        child_environment = os.environ.copy()
        child_environment.pop("LS_CI_SELF_TEST", None)
        child_environment.update(environment or {})
        return subprocess.run(
            [str(self.root / "check.sh"), *arguments], cwd=self.root.parent,
            env=child_environment, capture_output=True, text=True, timeout=10,
        )

    def test_entrypoint_routes_scope_and_forwards_only_scoped_options(self):
        for arguments, expected in (
            (("--python-only",), []),
            (("--require-build", "--python-only"), ["--require-build"]),
            (("--python-only", "--no-build"), ["--no-build"]),
        ):
            with self.subTest(arguments=arguments):
                result = self.invoke(arguments)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(json.loads(result.stdout), {
                    "arguments": expected, "directory": str(self.root),
                })

    def test_scope_preserves_driver_failure_status(self):
        result = self.invoke(("--python-only",), {"CHECK_TEST_EXIT": "7"})
        self.assertEqual(result.returncode, 7, result.stderr)

    def test_invalid_scope_combinations_and_recursive_ci_refuse_early(self):
        for arguments, environment in (
            (("--no-build",), {}),
            (("--python-only", "--verify-guards"), {}),
            (("--python-only",), {"LS_CI_SELF_TEST": "already checking"}),
            (("--python-only", "--unknown"), {}),
        ):
            with self.subTest(arguments=arguments):
                result = self.invoke(arguments, environment)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
