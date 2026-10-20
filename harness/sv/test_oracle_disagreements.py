#!/usr/bin/env python3
"""Keep the Icarus unary-plus exception exact, observable, and retireable."""

import contextlib
import copy
import io
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import diff_test
import diff_test2


class OracleDisagreementTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(diff_test.REPO)
        cases = json.loads(Path(diff_test.CASES_JSON).read_text())["cases"]
        declared = [c for c in cases if "oracle_disagreement" in c]
        self.assertEqual([c["name"] for c in declared], ["unary_plus_directed"])
        self.case = copy.deepcopy(declared[0])
        fixture = self.root / "Examples/system-verilog/unary_plus/unary_plus.sv"
        self.source = fixture.read_bytes()
        self.envelope = fixture.with_suffix(".sv.json").read_bytes()
        self.tb = diff_test.gen_tb.generate_tb(json.loads(self.envelope), self.case)
        self.row = self.case["oracle_disagreement"]
        self.sim_trace = list(self.row["sim_trace"])
        self.lean_trace = list(self.row["lean_trace"])

    def check(self, **overrides):
        inputs = dict(case=self.case, sim="iverilog", source=self.source,
                      envelope=self.envelope, tb_text=self.tb,
                      sim_trace=self.sim_trace, lean_by_sigma={"src": self.lean_trace})
        inputs.update(overrides)
        return diff_test.oracle_disagreement(**inputs)

    def test_exact_observed_disagreement_is_recognized(self):
        self.assertEqual(self.check(), "iverilog-unary-plus-xz")

    def test_every_changed_input_invalidates_the_binding(self):
        for field in ("source", "envelope", "tb_text"):
            value = {"source": self.source, "envelope": self.envelope,
                     "tb_text": self.tb}[field]
            with self.subTest(field=field), self.assertRaisesRegex(
                    diff_test.HarnessError, "changed"):
                self.check(**{field: value + (" " if isinstance(value, str) else b" ")})
        for field, value in (("name", "different_case"), ("example", "different_source"),
                             ("signals", ["b"]), ("stimulus", [{"a": "0000"}]),
                             ("accept_sigmas", ["src", "rev"])):
            case = copy.deepcopy(self.case)
            case[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(
                    diff_test.HarnessError, "changed case"):
                self.check(case=case)

    def test_every_changed_trace_bit_is_rejected(self):
        for side, original in (("sim", self.sim_trace), ("lean", self.lean_trace)):
            for line_index, line in enumerate(original):
                for column, digit in enumerate(line):
                    if digit not in "01xz" or column < len("CYCLE 0 "):
                        continue
                    changed = list(original)
                    changed[line_index] = line[:column] + ("1" if digit == "0" else "0") + line[column + 1:]
                    inputs = ({"sim_trace": changed} if side == "sim" else
                              {"lean_by_sigma": {"src": changed}})
                    with self.subTest(side=side, line=line_index, column=column), \
                            self.assertRaises(diff_test.HarnessError):
                        self.check(**inputs)

    def test_missing_extra_and_reordered_cycles_are_rejected(self):
        for trace in (self.sim_trace[:-1], self.sim_trace + self.sim_trace[-1:],
                      list(reversed(self.sim_trace))):
            with self.subTest(trace=trace), self.assertRaisesRegex(
                    diff_test.HarnessError, "unexpected trace"):
                self.check(sim_trace=trace)
        with self.assertRaisesRegex(diff_test.HarnessError, "changed schedule"):
            self.check(lean_by_sigma={"rev": self.lean_trace})
        with self.assertRaisesRegex(diff_test.HarnessError, "changed schedule"):
            self.check(lean_by_sigma={"src": self.lean_trace, "rev": self.lean_trace})

    def test_resolved_disagreement_requires_retirement(self):
        for trace in (self.sim_trace, self.lean_trace):
            with self.subTest(trace=trace), self.assertRaisesRegex(
                    diff_test.HarnessError, "resolved; retire"):
                self.check(sim_trace=trace, lean_by_sigma={"src": trace})

    def test_xcelium_and_ordinary_cases_have_no_exception(self):
        self.assertIsNone(self.check(sim="xrun"))
        case = copy.deepcopy(self.case)
        del case["oracle_disagreement"]
        self.assertIsNone(self.check(case=case))

    def run_main(self, sim="iverilog", sim_trace=None, lean_trace=None, case=None):
        with tempfile.TemporaryDirectory(prefix="sv-disagreement-test-") as directory:
            cases_path = Path(directory) / "cases.json"
            cases_path.write_text(json.dumps({"cases": [case or self.case]}))
            sim_trace = self.sim_trace if sim_trace is None else sim_trace
            lean_trace = self.lean_trace if lean_trace is None else lean_trace
            output = io.StringIO()
            with mock.patch.object(diff_test, "CASES_JSON", str(cases_path)), \
                    mock.patch.object(diff_test, "ensure_oleans"), \
                    mock.patch.object(diff_test, "resolve_sim", return_value=sim), \
                    mock.patch.object(diff_test, "SIMULATORS", {
                        sim: (mock.Mock(return_value=sim_trace), ())}), \
                    mock.patch.object(diff_test, "run_lean", return_value=lean_trace), \
                    mock.patch.object(diff_test, "run_cmd", side_effect=AssertionError(
                        "unit tests must not launch external commands")), \
                    mock.patch.object(sys, "argv", ["diff_test.py", "--workdir", directory]), \
                    contextlib.redirect_stdout(output):
                status = diff_test.main()
            return status, output.getvalue()

    def test_report_counts_disagreement_separately_and_shows_both_traces(self):
        status, output = self.run_main()
        self.assertEqual(status, 0, output)
        self.assertIn("DECLARED DISAGREEMENT (iverilog-unary-plus-xz)", output)
        self.assertIn("0 matched, 1 declared simulator disagreement(s), 0 failed", output)
        self.assertNotIn("PASS", output)
        self.assertIn(self.sim_trace[2], output)
        self.assertIn(self.lean_trace[2], output)

    def test_resolved_changed_and_undeclared_disagreements_fail_the_driver(self):
        ordinary = copy.deepcopy(self.case)
        del ordinary["oracle_disagreement"]
        bad_trace = list(self.sim_trace)
        bad_trace[0] = "CYCLE 0 a=0000 b=1111 c=0101"
        for inputs in ({"sim_trace": self.lean_trace}, {"sim_trace": bad_trace},
                       {"lean_trace": self.sim_trace}, {"case": ordinary},
                       {"sim": "xrun"}):
            with self.subTest(inputs=inputs):
                status, output = self.run_main(**inputs)
                self.assertEqual(status, 1, output)
                self.assertIn("0 matched, 0 declared simulator disagreement(s), 1 failed", output)

    def test_ordinary_agreement_and_xcelium_agreement_still_pass(self):
        ordinary = copy.deepcopy(self.case)
        del ordinary["oracle_disagreement"]
        for inputs in ({"case": ordinary}, {"sim": "xrun"}):
            with self.subTest(inputs=inputs):
                status, output = self.run_main(sim_trace=self.lean_trace, **inputs)
                self.assertEqual(status, 0, output)
                self.assertIn("1 matched, 0 declared simulator disagreement(s), 0 failed", output)


class Phase2DisagreementTests(unittest.TestCase):
    cases = ("bit_select_assign", "noncanonical_bit_assign", "packed_member_subrange",
             "packed_member_bit", "packed_union_subrange", "packed_union_bit", "nested_member_bit", "nested_member_concat", "typedef_nested_concat",
             "fixed_array_noncanonical_slice")

    def run_main(self, name, sims=("iverilog",), resolved=False, changed=False):
        case = next(c for c in json.loads(Path(diff_test2.CASES_JSON).read_text())["cases"]
                    if c["name"] == name)
        row = case["oracle_disagreement"]
        fixture = Path(diff_test2.REPO) / "Examples/system-verilog" / case["example"] / (case["top"] + ".sv.json")
        module = json.loads(fixture.read_text())["design"]["modules"][0]
        ports = [(p["name"], p["dir"], p["width"]["resolved"]) for p in module["ports"]]
        sim_trace = list(row["lean_trace"] if resolved else row["sim_trace"])
        if changed:
            sim_trace[0] += " extra=0"
        with tempfile.TemporaryDirectory(prefix="sv2-disagreement-test-") as directory:
            path = Path(directory) / "cases.json"
            path.write_text(json.dumps({"cases": [case]}))
            output = io.StringIO()
            with mock.patch.object(diff_test2, "CASES_JSON", str(path)), \
                    mock.patch.object(diff_test2, "ensure_oleans"), \
                    mock.patch.object(diff_test2, "requested_simulators", return_value=list(sims)), \
                    mock.patch.object(diff_test2, "run_lean", return_value=(ports, row["lean_trace"])), \
                    mock.patch.object(diff_test2, "run_iverilog", return_value=sim_trace), \
                    mock.patch.object(diff_test2, "run_xcelium", return_value=row["lean_trace"]), \
                    mock.patch.object(diff_test2, "run_cmd", side_effect=AssertionError(
                        "unit tests must not launch external commands")), \
                    mock.patch.object(sys, "argv", ["diff_test2.py", "--workdir", directory]), \
                    contextlib.redirect_stdout(output):
                status = diff_test2.main()
            return status, output.getvalue()

    def test_each_exact_disagreement_is_reported_separately(self):
        for name in self.cases:
            with self.subTest(name=name):
                status, output = self.run_main(name)
                self.assertEqual(status, 0, output)
                self.assertIn("0 case(s) verified, 0 skipped, 1 declared simulator disagreement(s)", output)
                self.assertIn("DECLARED DISAGREEMENT", output)
                self.assertNotIn("PASS", output)

    def test_resolution_and_changed_trace_are_hard_failures(self):
        for name in self.cases:
            for inputs in ({"resolved": True}, {"changed": True}):
                with self.subTest(name=name, inputs=inputs):
                    status, output = self.run_main(name, **inputs)
                    self.assertEqual(status, 1, output)
                    self.assertIn("1 case(s) failed", output)
                    self.assertNotIn("PASS", output)

    def test_dual_run_preserves_separate_disagreement_count(self):
        status, output = self.run_main("bit_select_assign", sims=("xrun", "iverilog"))
        self.assertEqual(status, 0, output)
        self.assertIn("xrun:ok(src)", output)
        self.assertIn("0 case(s) verified, 0 skipped, 1 declared simulator disagreement(s)", output)

    def test_xcelium_agreement_is_verified_normally(self):
        status, output = self.run_main("bit_select_assign", sims=("xrun",))
        self.assertEqual(status, 0, output)
        self.assertIn("1 case(s) verified, 0 skipped, 0 declared simulator disagreement(s)", output)
        self.assertIn("PASS", output)


class UnavailableOracleTests(unittest.TestCase):
    def setUp(self):
        self.cases = [c for c in json.loads(Path(diff_test2.CASES_JSON).read_text())["cases"]
                      if "icarus_unavailable" in c]
        self.assertEqual(len(self.cases), 23)

    def run_main(self, case, record=None, sims=("iverilog",), succeeds=False):
        source = Path(diff_test2.REPO) / "Examples/system-verilog" / case["example"] / (case["top"] + ".sv")
        module = json.loads(source.with_suffix(".sv.json").read_text())["design"]["modules"][0]
        ports = [(p["name"], p["dir"], p["width"]["resolved"]) for p in module["ports"]]
        trace = ["CYCLE 0 out=0"]
        failure = None
        if not succeeds:
            record = record or case["icarus_unavailable"]["failures"][0]
            result = SimpleNamespace(returncode=record["returncode"],
                                     stdout=record["stdout"].replace("<source>", str(source)),
                                     stderr=record["stderr"].replace("<source>", str(source)))
            failure = diff_test2.SimulatorError("observed tool failure", record["stage"], result)
        with tempfile.TemporaryDirectory(prefix="sv-unavailable-test-") as directory:
            path = Path(directory) / "cases.json"
            path.write_text(json.dumps({"cases": [case]}))
            output = io.StringIO()
            with mock.patch.object(diff_test2, "CASES_JSON", str(path)), \
                    mock.patch.object(diff_test2, "ensure_oleans"), \
                    mock.patch.object(diff_test2, "requested_simulators", return_value=list(sims)), \
                    mock.patch.object(diff_test2, "run_lean", return_value=(ports, trace)), \
                    mock.patch.object(diff_test2, "run_iverilog", side_effect=failure, return_value=trace), \
                    mock.patch.object(diff_test2, "run_xcelium", return_value=trace), \
                    mock.patch.object(diff_test2, "run_cmd", side_effect=AssertionError(
                        "unit tests must not launch external commands")), \
                    mock.patch.object(sys, "argv", ["diff_test2.py", "--workdir", directory]), \
                    contextlib.redirect_stdout(output):
                status = diff_test2.main()
            return status, output.getvalue()

    def test_every_recorded_failure_reports_unavailable_without_faking_verification(self):
        for case in self.cases:
            for record in case["icarus_unavailable"]["failures"]:
                with self.subTest(name=case["name"], record=record):
                    status, output = self.run_main(case, record)
                    self.assertEqual(status, 1, output)  # No simulator verified anything.
                    self.assertIn("UNAVAILABLE ORACLE", output)
                    self.assertIn("0 case(s) verified, 1 skipped, 0 declared simulator disagreement(s), 1 unavailable backend(s)", output)
                    self.assertNotIn("PASS", output)

    def test_compiler_diagnostics_are_independent_of_checkout_path(self):
        case = next(c for c in self.cases if c["name"] == "packed_aggregate_array_member")
        relative = Path("Examples/system-verilog") / case["example"] / (case["top"] + ".sv")
        original = Path(diff_test2.REPO) / relative
        with tempfile.TemporaryDirectory(prefix="different-checkout-") as directory:
            relocated = Path(directory) / relative
            relocated.parent.mkdir(parents=True)
            relocated.write_bytes(original.read_bytes())
            relocated.with_suffix(".sv.json").write_bytes(original.with_suffix(".sv.json").read_bytes())
            with mock.patch.object(diff_test2, "REPO", directory):
                status, output = self.run_main(case)
        self.assertEqual(status, 1, output)  # Unavailable coverage is never verification.
        self.assertIn("UNAVAILABLE ORACLE", output)
        self.assertNotIn("unexpected simulator failure", output)

    def test_unexpected_diagnostic_exit_stage_or_output_remains_failure(self):
        for case in self.cases:
            record = case["icarus_unavailable"]["failures"][0]
            for field, value in (("returncode", 99), ("stage", "unrecognized"),
                                 ("stdout", "unexpected output"), ("stderr", "different error")):
                changed = dict(record, **{field: value})
                with self.subTest(name=case["name"], field=field):
                    status, output = self.run_main(case, changed)
                    self.assertEqual(status, 1, output)
                    self.assertIn("unexpected simulator failure", output)
                    self.assertNotIn("UNAVAILABLE ORACLE", output)

    def test_rejected_failure_retains_all_observed_diagnostics(self):
        record = dict(stage="compile", returncode=99,
                      stdout="compiler stdout retained\n",
                      stderr="new compiler diagnostic retained\n")
        status, output = self.run_main(self.cases[0], record)
        self.assertEqual(status, 1, output)
        self.assertIn("unexpected simulator failure", output)
        for value in ("compile", "99", "compiler stdout retained",
                      "new compiler diagnostic retained"):
            with self.subTest(value=value):
                self.assertIn(value, output)

    def test_rejected_failure_publishes_escaped_github_annotation(self):
        record = dict(stage="compile", returncode=99,
                      stdout="unfamiliar 50% compiler stdout\n",
                      stderr="unfamiliar compiler stderr\r\n")
        with mock.patch.dict("os.environ", {"GITHUB_ACTIONS": "true"}):
            status, output = self.run_main(self.cases[0], record)
        self.assertEqual(status, 1, output)
        annotations = [line for line in output.splitlines() if line.startswith("::error")]
        self.assertEqual(len(annotations), 1, output)
        annotation = annotations[0]
        self.assertTrue(annotation.startswith("::error title=SV differential failure::"))
        for detail in ("unexpected simulator failure", "compile", "99",
                       "50%25 compiler stdout", "compiler stderr", "%0A"):
            with self.subTest(detail=detail):
                self.assertIn(detail, annotation)

    def test_changed_bindings_are_rejected(self):
        for field in ("source", "envelope", "case", "testbench"):
            case = copy.deepcopy(self.cases[0])
            case["icarus_unavailable"][field + "_sha256"] = "0" * 64
            with self.subTest(field=field):
                status, output = self.run_main(case)
                self.assertEqual(status, 1, output)
                self.assertIn("changed " + field, output)
                self.assertNotIn("UNAVAILABLE ORACLE", output)

    def test_success_requires_retiring_a_stale_unavailability_declaration(self):
        status, output = self.run_main(self.cases[0], succeeds=True)
        self.assertEqual(status, 1, output)
        self.assertIn("restriction resolved; retire", output)
        self.assertNotIn("PASS", output)

    def test_dual_run_verifies_xcelium_and_names_the_unavailable_backend(self):
        status, output = self.run_main(self.cases[0], sims=("xrun", "iverilog"))
        self.assertEqual(status, 0, output)
        self.assertIn("xrun:ok(src)", output)
        self.assertIn("1 case(s) verified, 0 skipped, 0 declared simulator disagreement(s), 1 unavailable backend(s)", output)

    def test_unexpected_icarus_failure_is_hard_even_when_xcelium_matches(self):
        record = dict(self.cases[0]["icarus_unavailable"]["failures"][0], returncode=99)
        status, output = self.run_main(self.cases[0], record, sims=("xrun", "iverilog"))
        self.assertEqual(status, 1, output)
        self.assertIn("1 case(s) failed", output)

    def test_xcelium_only_runs_are_verified_normally(self):
        status, output = self.run_main(self.cases[0], sims=("xrun",))
        self.assertEqual(status, 0, output)
        self.assertIn("1 case(s) verified, 0 skipped", output)


if __name__ == "__main__":
    unittest.main()
