#!/usr/bin/env python3
"""Focused simulator-selection and phase-2 verification accounting tests."""

import contextlib
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import diff_test2


class SimulatorSelectionTests(unittest.TestCase):
    def select(self, requested, available):
        with mock.patch.object(diff_test2.shutil, "which",
                               side_effect=available.get):
            return diff_test2.requested_simulators(requested)

    def test_auto_and_both_select_available_backends(self):
        inventories = [
            ({}, []),
            ({"xrun": "/bin/xrun"}, ["xrun"]),
            ({"iverilog": "/bin/iverilog", "vvp": "/bin/vvp"},
             ["iverilog"]),
            ({"verilator": "/bin/verilator"}, []),
            ({"xrun": "/bin/xrun", "iverilog": "/bin/iverilog",
              "vvp": "/bin/vvp"}, ["xrun", "iverilog"]),
        ]
        for requested in ("auto", "both"):
            for available, expected in inventories:
                with self.subTest(requested=requested, available=available):
                    self.assertEqual(self.select(requested, available), expected)

    def test_explicit_selection_never_falls_back(self):
        self.assertEqual(self.select("xrun", {"iverilog": "/bin/iverilog",
                                              "vvp": "/bin/vvp"}), [])
        self.assertEqual(self.select("iverilog", {"xrun": "/bin/xrun"}), [])
        self.assertEqual(self.select("verilator", {"iverilog": "/bin/iverilog",
                                                    "vvp": "/bin/vvp"}), [])
        available = {"xrun": "/bin/xrun", "iverilog": "/bin/iverilog",
                     "vvp": "/bin/vvp", "verilator": "/bin/verilator"}
        self.assertEqual(self.select("xrun", available), ["xrun"])
        self.assertEqual(self.select("iverilog", available), ["iverilog"])
        self.assertEqual(self.select("verilator", available), ["verilator"])

    def test_icarus_requires_compiler_and_runtime(self):
        for available in ({"iverilog": "/bin/iverilog"},
                          {"vvp": "/bin/vvp"}):
            with self.subTest(available=available):
                self.assertEqual(self.select("iverilog", available), [])
                self.assertEqual(self.select("auto", available), [])


class VerilatorRunnerTests(unittest.TestCase):
    def test_verilator_build_and_runtime_commands_are_parsed(self):
        calls = []

        def fake_run(cmd, cwd, timeout):
            calls.append((cmd, cwd, timeout))
            if len(calls) == 1:
                obj = Path(cmd[cmd.index("--Mdir") + 1])
                obj.mkdir(parents=True, exist_ok=True)
                (obj / "Vtb").write_text("")
                return type("Result", (), {"returncode": 0, "stdout": "build", "stderr": ""})()
            return type("Result", (), {"returncode": 0,
                                       "stdout": "CYCLE 0 hit=0\nCYCLE 1 hit=1\n",
                                       "stderr": ""})()

        with mock.patch.object(diff_test2, "run_cmd", side_effect=fake_run):
            with tempfile.TemporaryDirectory(prefix="sv-verilator-test-") as directory:
                trace = diff_test2.run_verilator("dut.sv", "module tb; endmodule\n", directory)

        self.assertEqual(trace, ["CYCLE 0 hit=0", "CYCLE 1 hit=1"])
        self.assertEqual(calls[0][0][0], "verilator")
        self.assertIn("--binary", calls[0][0])
        self.assertIn("--timing", calls[0][0])
        self.assertEqual(Path(calls[1][0][0]).name, "Vtb")


class VerificationAccountingTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="sv-admission-test-")
        self.addCleanup(directory.cleanup)
        self.directory = directory.name
        self.cases_path = os.path.join(self.directory, "cases.json")
        # main scans the source directory for memory sidecars, even when the
        # simulator is mocked. Keep that fixture inside the temporary repo.
        fixture = Path(self.directory) / "Examples" / "system-verilog" / "admission_fixture"
        fixture.mkdir(parents=True)
        (fixture / "dut.sv").write_text("module dut; endmodule\n")
        self.fixture = fixture
        self.patch_runner("REPO", new=self.directory)
        self.trace = ["CYCLE 0 out=0", "CYCLE 1 out=1"]
        self.ports = [("out", "out", 1)]
        self.patch_runner("CASES_JSON", new=self.cases_path)
        self.ensure_oleans = self.patch_runner("ensure_oleans")
        self.requested_simulators = self.patch_runner(
            "requested_simulators", return_value=["iverilog"])
        self.run_lean = self.patch_runner(
            "run_lean", return_value=(self.ports, self.trace))
        self.run_iverilog = self.patch_runner(
            "run_iverilog", return_value=self.trace)
        self.run_xcelium = self.patch_runner(
            "run_xcelium", return_value=self.trace)
        self.run_verilator = self.patch_runner(
            "run_verilator", return_value=self.trace)
        self.patch_runner("run_cmd", side_effect=AssertionError(
            "accounting tests must not launch external commands"))
        generator = mock.patch.object(diff_test2.gen_tb2, "generate_tb2",
                                      return_value="module tb; endmodule\n")
        self.addCleanup(generator.stop)
        self.generate_tb = generator.start()

    def patch_runner(self, name, **kwargs):
        patcher = mock.patch.object(diff_test2, name, **kwargs)
        self.addCleanup(patcher.stop)
        return patcher.start()

    def case(self, name, xrun_only=False, verilator_only=False):
        return {"name": name, "example": "admission_fixture", "top": "dut",
                "xrun_only": xrun_only, "verilator_only": verilator_only}

    def run_main(self, cases, arguments=()):
        with open(self.cases_path, "w") as handle:
            json.dump({"cases": cases}, handle)
        output = io.StringIO()
        argv = ["diff_test2.py", "--workdir", self.directory] + list(arguments)
        with mock.patch.object(sys, "argv", argv), contextlib.redirect_stdout(output):
            status = diff_test2.main()
        return status, output.getvalue()

    def test_nonempty_icarus_cases_are_verified(self):
        status, output = self.run_main([self.case("first"), self.case("second")])
        self.assertEqual(status, 0)
        self.assertIn("2 case(s) verified, 0 skipped", output)
        self.assertEqual(self.run_lean.call_count, 2)
        self.assertEqual(self.run_iverilog.call_count, 2)
        self.run_xcelium.assert_not_called()
        self.run_verilator.assert_not_called()

    def test_memory_sidecars_are_copied_to_simulator_workdir(self):
        (self.fixture / "init.hex").write_text("ab\n")
        (self.fixture / "other.MEM").write_text("cd\n")
        (self.fixture / "ignored.txt").write_text("no\n")
        status, _ = self.run_main([self.case("sidecars")])
        self.assertEqual(status, 0)
        workdir = Path(self.directory) / "sidecars" / "iverilog"
        self.assertEqual((workdir / "init.hex").read_text(), "ab\n")
        self.assertEqual((workdir / "other.MEM").read_text(), "cd\n")
        self.assertFalse((workdir / "ignored.txt").exists())

    def test_xrun_only_cases_are_counted_as_skipped(self):
        status, output = self.run_main([self.case("portable"),
                                        self.case("xrun_first", True),
                                        self.case("xrun_second", True)])
        self.assertEqual(status, 0)
        self.assertIn("1 case(s) verified, 2 skipped", output)
        self.assertEqual(output.count("SKIP (required simulator not selected"), 2)
        self.run_lean.assert_called_once()
        self.run_iverilog.assert_called_once()
        self.run_xcelium.assert_not_called()
        self.run_verilator.assert_not_called()

    def test_all_xrun_only_cases_do_not_fake_a_pass(self):
        status, output = self.run_main([self.case("xrun_first", True),
                                        self.case("xrun_second", True)])
        self.assertEqual(status, 1)
        self.assertIn("0 case(s) verified, 2 skipped", output)
        self.assertNotIn("PASS", output)
        self.run_lean.assert_not_called()
        self.run_iverilog.assert_not_called()
        self.run_xcelium.assert_not_called()
        self.run_verilator.assert_not_called()

    def test_verilator_only_case_runs_explicit_backend(self):
        self.requested_simulators.return_value = ["verilator"]
        status, output = self.run_main([self.case("inside", verilator_only=True)],
                                       ["--sim", "verilator"])
        self.assertEqual(status, 0)
        self.assertIn("1 case(s) verified, 0 skipped", output)
        self.run_verilator.assert_called_once()
        self.run_iverilog.assert_not_called()
        self.run_xcelium.assert_not_called()

    def test_verilator_only_case_is_skipped_without_explicit_backend(self):
        self.requested_simulators.return_value = ["iverilog"]
        status, output = self.run_main([self.case("inside", verilator_only=True)])
        self.assertEqual(status, 1)
        self.assertIn("0 case(s) verified, 1 skipped", output)
        self.assertIn("required simulator not selected", output)
        self.run_verilator.assert_not_called()
        self.run_iverilog.assert_not_called()
        self.run_xcelium.assert_not_called()

    def test_empty_table_is_checked_before_no_simulator_skip(self):
        self.requested_simulators.return_value = []
        status, output = self.run_main([])
        self.assertEqual(status, 1)
        self.assertIn("COULD NOT VERIFY", output)
        self.requested_simulators.assert_not_called()
        self.ensure_oleans.assert_not_called()

    def test_unknown_case_is_checked_before_no_simulator_skip(self):
        self.requested_simulators.return_value = []
        status, output = self.run_main([self.case("present")],
                                       ["--case", "missing"])
        self.assertEqual(status, 2)
        self.assertIn("no case named 'missing'", output)
        self.requested_simulators.assert_not_called()
        self.ensure_oleans.assert_not_called()

    def test_known_case_filter_counts_only_selected_case(self):
        status, output = self.run_main([self.case("first"), self.case("second")],
                                       ["--case", "second", "--sim", "iverilog"])
        self.assertEqual(status, 0)
        self.assertIn("1 case(s) verified, 0 skipped", output)
        self.requested_simulators.assert_called_once_with("iverilog")
        self.run_lean.assert_called_once()
        self.assertEqual(self.run_lean.call_args.args[1], "second")

    def test_nonempty_table_without_simulators_is_explicit_skip(self):
        self.requested_simulators.return_value = []
        status, output = self.run_main([self.case("portable")])
        self.assertEqual(status, 0)
        self.assertIn("SKIP: no requested simulator", output)
        self.assertIn("not exercised", output)
        self.assertNotIn("verified", output)
        self.ensure_oleans.assert_not_called()
        self.run_lean.assert_not_called()

    def test_two_backends_count_one_verified_case(self):
        self.requested_simulators.return_value = ["xrun", "iverilog"]
        status, output = self.run_main([self.case("portable")])
        self.assertEqual(status, 0)
        self.assertIn("1 case(s) verified, 0 skipped", output)
        self.assertIn("xrun:ok(src)", output)
        self.assertIn("iverilog:ok(src)", output)
        self.run_lean.assert_called_once()
        self.run_iverilog.assert_called_once()
        self.run_xcelium.assert_called_once()

    def test_xrun_only_case_runs_selected_xrun(self):
        self.requested_simulators.return_value = ["xrun", "iverilog"]
        status, output = self.run_main([self.case("inside", True)])
        self.assertEqual(status, 0)
        self.assertIn("1 case(s) verified, 0 skipped", output)
        self.run_xcelium.assert_called_once()
        self.run_iverilog.assert_not_called()

    def test_mismatch_remains_hard_when_other_backend_matches(self):
        self.requested_simulators.return_value = ["xrun", "iverilog"]
        self.run_iverilog.return_value = ["CYCLE 0 out=1"]
        status, output = self.run_main([self.case("mismatch")])
        self.assertEqual(status, 1)
        self.assertIn("FAIL vs iverilog", output)
        self.assertIn("1 case(s) failed", output)
        self.assertNotIn("PASS", output)
        self.run_xcelium.assert_called_once()

    def test_lean_error_remains_hard(self):
        self.run_lean.side_effect = diff_test2.HarnessError("runner2 failed")
        status, output = self.run_main([self.case("broken_lean")])
        self.assertEqual(status, 1)
        self.assertIn("ERROR: runner2 failed", output)
        self.assertIn("1 case(s) failed", output)
        self.run_iverilog.assert_not_called()

    def test_simulator_error_remains_hard(self):
        self.run_iverilog.side_effect = diff_test2.HarnessError("compile failed")
        status, output = self.run_main([self.case("broken_sim")])
        self.assertEqual(status, 1)
        self.assertIn("ERROR: compile failed", output)
        self.assertIn("1 case(s) failed", output)

    def test_selected_xrun_failure_is_not_reclassified_as_skip(self):
        self.requested_simulators.return_value = ["xrun"]
        self.run_xcelium.side_effect = diff_test2.HarnessError("xrun NOLICN")
        status, output = self.run_main([self.case("broken_xrun")])
        self.assertEqual(status, 1)
        self.assertIn("ERROR: xrun NOLICN", output)
        self.assertIn("1 case(s) failed", output)
        self.assertNotIn("SKIP", output)

    def test_testbench_error_remains_hard(self):
        self.generate_tb.side_effect = diff_test2.gen_tb2.TbError("bad stimulus")
        status, output = self.run_main([self.case("broken_tb")])
        self.assertEqual(status, 1)
        self.assertIn("ERROR: bad stimulus", output)
        self.assertIn("1 case(s) failed", output)
        self.run_iverilog.assert_not_called()


if __name__ == "__main__":
    unittest.main()
