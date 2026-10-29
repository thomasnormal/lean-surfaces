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
import declare_disagreement
import diff_test
import diff_test2
import oracle_disagreements
import xcelium_golden


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
             "fixed_array_noncanonical_slice", "concat_undriven")

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


class XceliumDeclarationTests(unittest.TestCase):
    """A declaration that names Xcelium (`"sim": "xcelium"`, round 6): the
    reference simulator departs from IEEE 1800-2023 and the departure cannot be
    refused statically. It is checked live (`xrun`) and against the pin
    (`--golden`) with the same alarms an Icarus declaration has. The fixture is
    an existing Icarus-declared row re-labelled: its recorded sim_trace plays
    the Xcelium trace (the declaration's bindings do not cover `sim`)."""

    NAME = "bit_select_assign"

    def setUp(self):
        self.root = Path(diff_test2.REPO)
        cases = json.loads(Path(diff_test2.CASES_JSON).read_text())["cases"]
        self.case = copy.deepcopy(next(c for c in cases if c["name"] == self.NAME))
        self.case["oracle_disagreement"]["sim"] = "xcelium"
        self.row = self.case["oracle_disagreement"]
        self.sim_trace = list(self.row["sim_trace"])
        self.lean_trace = list(self.row["lean_trace"])
        self.dut = self.root / "Examples/system-verilog" / self.case["example"] / (self.case["top"] + ".sv")
        self.source = self.dut.read_bytes()
        self.envelope = self.dut.with_suffix(".sv.json").read_bytes()
        module = json.loads(self.envelope)["design"]["modules"][0]
        self.ports = [(p["name"], p["dir"], p["width"]["resolved"]) for p in module["ports"]]
        self.tb = diff_test2.gen_tb2.generate_tb2(self.case["top"], self.ports, self.case)

    def check(self, sim="xrun", **overrides):
        inputs = dict(case=self.case, sim=sim, source=self.source, envelope=self.envelope,
                      tb_text=self.tb, sim_trace=self.sim_trace,
                      lean_by_sigma={"src": self.lean_trace})
        inputs.update(overrides)
        return diff_test2.oracle_disagreement(**inputs)

    def golden(self, **overrides):
        inputs = dict(case=self.case, source=self.source, envelope=self.envelope,
                      tb_text=self.tb, pinned_trace=self.sim_trace,
                      lean_by_sigma={"src": self.lean_trace})
        inputs.update(overrides)
        return diff_test2.golden_disagreement(**inputs)

    # --- the live check: `xrun` and `xcelium` are one simulator ---
    def test_live_xrun_run_is_checked_and_icarus_is_left_alone(self):
        ident = self.row["id"]
        self.assertEqual(self.check("xrun"), ident)
        self.assertEqual(self.check("xcelium"), ident)
        self.assertIsNone(self.check("iverilog"))

    def test_an_icarus_declaration_is_not_about_xcelium(self):
        case = copy.deepcopy(self.case)
        case["oracle_disagreement"]["sim"] = "iverilog"
        self.assertIsNone(diff_test2.oracle_disagreement(
            case, "xrun", self.source, self.envelope, self.tb, self.sim_trace,
            {"src": self.lean_trace}))
        self.assertEqual(diff_test2.oracle_disagreement(
            case, "iverilog", self.source, self.envelope, self.tb, self.sim_trace,
            {"src": self.lean_trace}), case["oracle_disagreement"]["id"])

    def test_unknown_simulator_names_are_invalid(self):
        for name in ("xrun", "verilator", "", None):
            case = copy.deepcopy(self.case)
            case["oracle_disagreement"]["sim"] = name
            with self.subTest(name=name), self.assertRaisesRegex(
                    diff_test2.HarnessError, "invalid oracle_disagreement"):
                diff_test2.oracle_disagreement(case, "xrun", self.source, self.envelope,
                                               self.tb, self.sim_trace, {"src": self.lean_trace})

    def test_resolved_changed_and_rebound_departures_fail_live(self):
        with self.assertRaisesRegex(diff_test2.HarnessError, "resolved; retire"):
            self.check(sim_trace=self.lean_trace)
        with self.assertRaisesRegex(diff_test2.HarnessError, "unexpected trace"):
            self.check(sim_trace=[self.sim_trace[0] + " extra=0"] + self.sim_trace[1:])
        with self.assertRaisesRegex(diff_test2.HarnessError, "unexpected trace"):
            self.check(lean_by_sigma={"src": self.sim_trace[:-1] + [self.sim_trace[-1] + "0"]})
        for field in ("source", "envelope", "tb_text"):
            value = {"source": self.source, "envelope": self.envelope, "tb_text": self.tb}[field]
            with self.subTest(field=field), self.assertRaisesRegex(diff_test2.HarnessError, "changed"):
                self.check(**{field: value + (" " if isinstance(value, str) else b" ")})

    # --- the pinned check: the pin plays the simulator ---
    def test_the_pin_is_checked_like_a_simulator(self):
        self.assertEqual(self.golden(), self.row["id"])
        with self.assertRaisesRegex(diff_test2.HarnessError, "resolved; retire"):
            self.golden(pinned_trace=self.lean_trace)
        bad = list(self.sim_trace)
        bad[0] = bad[0].replace("z", "0", 1)
        with self.assertRaisesRegex(diff_test2.HarnessError, "unexpected trace"):
            self.golden(pinned_trace=bad)
        with self.assertRaisesRegex(diff_test2.HarnessError, "unexpected trace"):
            self.golden(lean_by_sigma={"src": bad})
        with self.assertRaisesRegex(diff_test2.HarnessError, "changed source"):
            self.golden(source=self.source + b" ")

    def test_an_icarus_declaration_or_none_is_not_the_pins_business(self):
        case = copy.deepcopy(self.case)
        case["oracle_disagreement"]["sim"] = "iverilog"
        self.assertIsNone(self.golden(case=case))
        del case["oracle_disagreement"]
        self.assertIsNone(self.golden(case=case))

    def test_bindings_alone_can_be_checked_when_no_pin_is_usable(self):
        args = (self.case, self.source, self.envelope, self.tb)
        self.assertEqual(diff_test2.check_declaration_bindings(*args), self.row["id"])
        with self.assertRaisesRegex(diff_test2.HarnessError, "changed testbench"):
            diff_test2.check_declaration_bindings(self.case, self.source, self.envelope, self.tb + "\n")
        case = copy.deepcopy(self.case)
        del case["oracle_disagreement"]
        self.assertIsNone(diff_test2.check_declaration_bindings(case, self.source, self.envelope, self.tb))

    # --- `diff_test2.py --golden`, end to end with mocked tools ---
    def run_main(self, pin, sims=(), pin_params=None, case=None, pin_status="ok", extra=()):
        """Run the harness with `--golden` over this one row. `pin`: the pinned
        trace (None: no entry); the entry is keyed by the hash of the DUT, the
        generated testbench and the row's parameters, as `xcelium_batch` does."""
        case = case or self.case
        golden = xcelium_golden.empty_golden()
        golden["simulator"] = {"name": "Xcelium", "version": "test 24.03"}
        if pin is not None:
            tb = diff_test2.gen_tb2.generate_tb2(case["top"], self.ports, case)
            golden["rows"][case["name"]] = {
                "hash": xcelium_golden.row_hash(case["name"], xcelium_golden.read_text(str(self.dut)),
                                                tb, pin_params if pin_params is not None else case.get("params")),
                "status": pin_status, "cycles": list(pin),
                **({"message": "xmvlog: *E,TEST (m.sv,1|1): pinned failure"} if pin_status != "ok" else {})}
        with tempfile.TemporaryDirectory(prefix="sv2-xcelium-declaration-test-") as directory:
            cases_path = Path(directory) / "cases.json"
            cases_path.write_text(json.dumps({"cases": [case]}))
            golden_path = Path(directory) / "golden.json"
            xcelium_golden.save(golden, str(golden_path))
            output = io.StringIO()
            with mock.patch.object(diff_test2, "CASES_JSON", str(cases_path)), \
                    mock.patch.object(diff_test2, "ensure_oleans"), \
                    mock.patch.object(diff_test2, "requested_simulators", return_value=list(sims)), \
                    mock.patch.object(diff_test2, "run_lean", return_value=(self.ports, self.lean_trace)), \
                    mock.patch.object(diff_test2, "run_iverilog", return_value=self.lean_trace), \
                    mock.patch.object(diff_test2, "run_xcelium", return_value=self.sim_trace), \
                    mock.patch.object(diff_test2, "run_cmd", side_effect=AssertionError(
                        "unit tests must not launch external commands")), \
                    mock.patch.object(sys, "argv", ["diff_test2.py", "--workdir", directory,
                                                    "--golden", str(golden_path), *extra]), \
                    contextlib.redirect_stdout(output):
                status = diff_test2.main()
            return status, output.getvalue()

    def test_golden_reports_a_declared_departure_apart_from_match_and_diff(self):
        status, output = self.run_main(self.sim_trace)
        self.assertEqual(status, 0, output)
        self.assertIn("XREF-DECLARED", output)
        self.assertIn("1 XREF-DECLARED, 0 XREF-DIFF", output)
        self.assertIn("0 XREF-MATCH", output)
        self.assertNotIn("XREF-MATCH\n", output)
        self.assertNotIn("PASS", output)

    def test_golden_strict_fails_on_a_diff_but_not_on_a_declared_departure(self):
        status, output = self.run_main(self.sim_trace, extra=("--golden-strict",))
        self.assertEqual(status, 0, output)
        self.assertNotIn("--golden-strict:", output)
        icarus = copy.deepcopy(self.case)
        icarus["oracle_disagreement"]["sim"] = "iverilog"
        status, output = self.run_main(self.sim_trace, case=icarus, extra=("--golden-strict",))
        self.assertEqual(status, 1, output)
        self.assertIn("--golden-strict: 1 XREF-DIFF", output)

    def test_golden_resolved_changed_or_rebound_departure_is_a_hard_failure(self):
        status, output = self.run_main(self.lean_trace)           # pin == model: resolved
        self.assertEqual(status, 1, output)
        self.assertIn("resolved; retire", output)
        self.assertNotIn("XREF-MATCH\n", output)
        changed = list(self.sim_trace)
        changed[0] = changed[0].replace("z", "1", 1)              # pin moved to a third value
        status, output = self.run_main(changed)
        self.assertEqual(status, 1, output)
        self.assertIn("unexpected trace", output)
        self.assertNotIn("XREF-DIFF\n", output)

    def test_golden_without_a_usable_pin_still_checks_the_bindings(self):
        for pin, kwargs in ((None, {}), (self.sim_trace, {"pin_params": {"N": 99}}),
                            (self.sim_trace, {"pin_status": "xrun-compile-error"})):
            with self.subTest(kwargs=kwargs, pinned=pin is not None):
                # Icarus verifies the row (it agrees with the model) so that the
                # run has something to count; the pin contributes no verdict.
                status, output = self.run_main(pin, sims=("iverilog",), **kwargs)
                self.assertEqual(status, 0, output)
                self.assertIn("NOT re-checked against the pin", output)
                self.assertNotIn("XREF-DECLARED\n", output)
        # ... and a changed input fails even there.
        case = copy.deepcopy(self.case)
        case["signals"] = case["signals"][:-1]
        status, output = self.run_main(None, sims=("iverilog",), case=case)
        self.assertEqual(status, 1, output)
        self.assertIn("changed case", output)

    def test_golden_leaves_an_icarus_declaration_and_an_ordinary_row_alone(self):
        icarus = copy.deepcopy(self.case)
        icarus["oracle_disagreement"]["sim"] = "iverilog"
        # Icarus is the outlier on its own declared rows: the pin equals the model.
        status, output = self.run_main(self.lean_trace, case=icarus)
        self.assertEqual(status, 0, output)
        self.assertIn("XREF-MATCH", output)
        self.assertIn("1 XREF-MATCH, 0 XREF-DECLARED, 0 XREF-DIFF", output)
        # ... and a pin that differs from the model is an ordinary XREF-DIFF.
        status, output = self.run_main(self.sim_trace, case=icarus)
        self.assertEqual(status, 0, output)
        self.assertIn("0 XREF-MATCH, 0 XREF-DECLARED, 1 XREF-DIFF", output)

    def test_an_icarus_only_run_names_the_declared_xcelium_departure(self):
        status, output = self.run_main(self.sim_trace, sims=("iverilog",))
        self.assertEqual(status, 0, output)
        self.assertIn("iverilog:ok(src)", output)
        self.assertIn("xcelium:DECLARED DEPARTURE (%s; checked by --golden, not here)" % self.row["id"],
                      output)
        self.assertIn("1 case(s) verified", output)

    def test_live_xrun_and_golden_agree_on_the_same_row(self):
        status, output = self.run_main(self.sim_trace, sims=("xrun", "iverilog"))
        self.assertEqual(status, 0, output)
        self.assertIn("xrun:DECLARED DISAGREEMENT", output)
        self.assertIn("iverilog:ok(src)", output)
        self.assertIn("XREF-DECLARED", output)
        self.assertIn("0 case(s) verified, 0 skipped, 1 declared simulator disagreement(s)", output)


class DeclareDisagreementTests(unittest.TestCase):
    """`declare_disagreement.build_declaration` is the recipe of the committed
    declarations: it reproduces them bit for bit from their own inputs."""

    NAMES = ("bit_select_assign", "array_oob_inner", "hier_fill_ctx")

    def inputs(self, name):
        root = Path(diff_test2.REPO)
        cases = json.loads(Path(diff_test2.CASES_JSON).read_text())["cases"]
        case = copy.deepcopy(next(c for c in cases if c["name"] == name))
        dut = root / "Examples/system-verilog" / case["example"] / (case["top"] + ".sv")
        envelope = dut.with_suffix(".sv.json").read_bytes()
        module = json.loads(envelope)["design"]["modules"][0]
        ports = [(p["name"], p["dir"], p["width"]["resolved"]) for p in module["ports"]]
        tb = diff_test2.gen_tb2.generate_tb2(case["top"], ports, case)
        return case, dut.read_bytes(), envelope, tb

    def test_the_recipe_reproduces_the_committed_declarations(self):
        for name in self.NAMES:
            with self.subTest(name=name):
                case, source, envelope, tb = self.inputs(name)
                row = case["oracle_disagreement"]
                text = {k: row[k] for k in declare_disagreement.TEXT_FIELDS}
                built = declare_disagreement.build_declaration(
                    case, row["sim"], text, source, envelope, tb,
                    row["sim_trace"], row["lean_trace"], row["sigma"])
                self.assertEqual(built, row)
                self.assertEqual(list(built), list(row))  # key order too

    def test_digests_are_the_checkers(self):
        case, source, envelope, tb = self.inputs("bit_select_assign")
        digests = oracle_disagreements.binding_digests(case, source, envelope, tb)
        self.assertEqual(sorted(digests), ["case_sha256", "envelope_sha256", "source_sha256",
                                           "testbench_sha256"])
        for key, value in digests.items():
            self.assertEqual(value, case["oracle_disagreement"][key])

    def test_nothing_to_declare_and_bad_input_are_refused(self):
        case, source, envelope, tb = self.inputs("bit_select_assign")
        row = case["oracle_disagreement"]
        text = {k: row[k] for k in declare_disagreement.TEXT_FIELDS}
        build = declare_disagreement.build_declaration
        with self.assertRaisesRegex(diff_test2.HarnessError, "nothing to declare"):
            build(case, "xcelium", text, source, envelope, tb, row["lean_trace"], row["lean_trace"])
        with self.assertRaisesRegex(diff_test2.HarnessError, "--sim must be"):
            build(case, "xrun", text, source, envelope, tb, row["sim_trace"], row["lean_trace"])
        with self.assertRaisesRegex(diff_test2.HarnessError, "missing observed"):
            build(case, "xcelium", dict(text, observed=" "), source, envelope, tb,
                  row["sim_trace"], row["lean_trace"])

    def test_a_pin_is_used_only_when_it_describes_these_sources(self):
        case, source, envelope, tb = self.inputs("bit_select_assign")
        dut = Path(diff_test2.REPO) / "Examples/system-verilog" / case["example"] / (case["top"] + ".sv")
        good = xcelium_golden.row_hash(case["name"], xcelium_golden.read_text(str(dut)), tb,
                                       case.get("params"))
        with tempfile.TemporaryDirectory(prefix="sv-declare-test-") as directory:
            def pin(entry):
                golden = xcelium_golden.empty_golden()
                golden["simulator"] = {"version": "test"}
                golden["rows"] = {case["name"]: entry} if entry else {}
                path = str(Path(directory) / "g.json")
                xcelium_golden.save(golden, path)
                return path
            trace = ["CYCLE 0 y=1"]
            args = (case["name"], str(dut), tb, case.get("params"))
            self.assertEqual(declare_disagreement.pinned_trace(
                pin({"hash": good, "status": "ok", "cycles": trace}), *args), trace)
            for entry, message in ((None, "not pinned"),
                                   ({"hash": "0" * 64, "status": "ok", "cycles": trace}, "stale"),
                                   ({"hash": good, "status": "runtime-error", "cycles": [],
                                     "message": "x"}, "not ok")):
                with self.subTest(message=message), self.assertRaisesRegex(
                        diff_test2.HarnessError, message):
                    declare_disagreement.pinned_trace(pin(entry), *args)


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


# Measured 2026-10-28 with Homebrew Icarus 12.0 on macOS (full diff_test2
# suite): the same failures as the recorded Ubuntu signatures, framed by
# macOS libc and macOS /bin/sh (oracle_disagreements.py, "HOST FRAMING").
DARWIN_IVL_ABORT = (
    "sh: line 1: 31863 Done                    /opt/homebrew/Cellar/icarus-verilog/12.0/lib/ivl/ivlpp"
    " -L -F\"/var/folders/qz/yy2p38hj2m9c7bfp30yq99340000gn/T//ivrlg21feae553\""
    " -f\"/var/folders/qz/yy2p38hj2m9c7bfp30yq99340000gn/T//ivrlg1feae553\""
    " -p\"/var/folders/qz/yy2p38hj2m9c7bfp30yq99340000gn/T//ivrli1feae553\"\n"
    "     31864 Abort trap: 6           | /opt/homebrew/Cellar/icarus-verilog/12.0/lib/ivl/ivl"
    " -C\"/var/folders/qz/yy2p38hj2m9c7bfp30yq99340000gn/T//ivrlh1feae553\""
    " -C\"/opt/homebrew/Cellar/icarus-verilog/12.0/lib/ivl/vvp.conf\" -- -\n")
DARWIN_VVP_ASSERT = ("Assertion failed: (adr+that.size_ <= size_), function set_vec, "
                     "file vvp_net.cc, line 1180.\n")


def darwin_form(record, pid=40000):
    """A recorded (Ubuntu) failure as macOS frames it: libc's assertion format
    and the bash job report, with fresh process ids and temporary names."""
    def darwin_assert(match):
        return "Assertion failed: (%s), function %s, file %s, line %s." % (
            match.group("expr"), oracle_disagreements._short_function(match.group("func")),
            match.group("file"), match.group("line"))
    stderr = oracle_disagreements._GLIBC_ASSERT.sub(darwin_assert, record["stderr"])
    report = DARWIN_IVL_ABORT.replace("31863", str(pid)).replace("31864", str(pid + 1)) \
        .replace("1feae553", "%x" % (pid * 7919))
    stderr = stderr.replace("Aborted (core dumped)\n", report)
    return dict(record, stderr=stderr)


class HostFramingTests(unittest.TestCase):
    """One Icarus failure, two hosts: accepted in both framings, and nothing
    else is accepted because of the rewriting."""

    setUp = UnavailableOracleTests.setUp
    run_main = UnavailableOracleTests.run_main

    def framed(self):
        out = []
        for case in self.cases:
            for record in case["icarus_unavailable"]["failures"]:
                darwin = darwin_form(record)
                if darwin != record:
                    out.append((case, record, darwin))
        return out

    def test_every_recorded_crash_in_macos_framing_is_the_same_failure(self):
        framed = self.framed()
        # Non-vacuity: the sixteen cases that ERRORed on macOS all carry one.
        self.assertGreaterEqual(len({c["name"] for c, _, _ in framed}), 16)
        for case, _record, darwin in framed:
            for pid in (40000, 7):
                with self.subTest(name=case["name"], pid=pid):
                    status, output = self.run_main(case, darwin_form(_record, pid))
                    self.assertEqual(status, 1, output)  # unavailable is never verified
                    self.assertIn("UNAVAILABLE ORACLE", output)
                    self.assertNotIn("unexpected simulator failure", output)

    def test_measured_macos_signatures_are_recognized(self):
        by_name = {c["name"]: c for c in self.cases}
        compile_case = by_name["packed_member_indexed"]
        runtime_case = by_name["noncanonical_member_bit"]
        compile_record = dict(stage="compile", returncode=134, stdout="", stderr=(
            "<source>:12: assert: elab_net.cc:668: failed assertion tail_sel.sel == "
            "index_component_t::SEL_PART || tail_sel.sel == index_component_t::SEL_BIT\n"
            + DARWIN_IVL_ABORT))
        runtime_record = dict(stage="runtime", returncode=-6, stdout="",
                              stderr=DARWIN_VVP_ASSERT)
        for case, record in ((compile_case, compile_record), (runtime_case, runtime_record)):
            with self.subTest(name=case["name"]):
                status, output = self.run_main(case, record)
                self.assertEqual(status, 1, output)
                self.assertIn("UNAVAILABLE ORACLE", output)
                self.assertNotIn("unexpected simulator failure", output)

    def test_host_framing_does_not_admit_a_different_failure(self):
        compile_case, _, darwin = next(t for t in self.framed() if t[1]["stage"] == "compile")
        runtime_case, _, rdarwin = next(t for t in self.framed() if t[1]["stage"] == "runtime")
        variants = [
            (compile_case, dict(darwin, stderr=darwin["stderr"].replace(
                "Abort trap: 6", "Segmentation fault: 11"))),
            (compile_case, dict(darwin, stderr=darwin["stderr"].replace(
                "Abort trap: 6           | /opt/homebrew/Cellar/icarus-verilog/12.0/lib/ivl/ivl ",
                "Abort trap: 6           | /opt/homebrew/Cellar/icarus-verilog/12.0/lib/ivl/ivlpp "))),
            (compile_case, dict(darwin, stderr=darwin["stderr"].split("sh: line")[0] + "Aborted\n")),
            (compile_case, dict(darwin, stderr=darwin["stderr"].split("sh: line")[0])),
            (compile_case, dict(darwin, returncode=139)),
            (compile_case, dict(darwin, stderr=darwin["stderr"].replace("elab_net.cc:668", "elab_net.cc:669"))),
            (runtime_case, dict(rdarwin, stderr=rdarwin["stderr"].replace("line 1180", "line 1181"))),
            (runtime_case, dict(rdarwin, stderr=rdarwin["stderr"].replace("function set_vec", "function set_bit"))),
            (runtime_case, dict(rdarwin, stderr=rdarwin["stderr"].replace("<= size_)", "< size_)"))),
            (runtime_case, dict(rdarwin, stderr=rdarwin["stderr"].replace("vvp_net.cc", "vvp_net2.cc"))),
            (runtime_case, dict(rdarwin, stage="compile")),
            (runtime_case, dict(rdarwin, stderr=rdarwin["stderr"] + "trailing diagnostic\n")),
        ]
        for case, record in variants:
            with self.subTest(name=case["name"], stderr=record["stderr"][-80:],
                              returncode=record["returncode"], stage=record["stage"]):
                status, output = self.run_main(case, record)
                self.assertEqual(status, 1, output)
                self.assertIn("unexpected simulator failure", output)
                self.assertNotIn("UNAVAILABLE ORACLE", output)


if __name__ == "__main__":
    unittest.main()
