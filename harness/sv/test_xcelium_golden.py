#!/usr/bin/env python3
"""Unit tests for the pinned Xcelium reference (xcelium_golden.py, the
classifier of xcelium_batch.py, and the integrity of the committed
xcelium_golden.json). No simulator, no ssh, no Lean."""

import json
import os
import re
import sys
import tempfile
import unittest

HARNESS_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HARNESS_DIR)

import diff_test2  # noqa: E402
import xcelium_batch as B  # noqa: E402
import xcelium_golden as G  # noqa: E402


class RowHashTests(unittest.TestCase):
    def test_every_input_matters(self):
        base = G.row_hash("r", "module m; endmodule\n", "module tb; endmodule\n", {"A": 1})
        for changed in (G.row_hash("r2", "module m; endmodule\n", "module tb; endmodule\n", {"A": 1}),
                        G.row_hash("r", "module m;  endmodule\n", "module tb; endmodule\n", {"A": 1}),
                        G.row_hash("r", "module m; endmodule\n", "module tb;  endmodule\n", {"A": 1}),
                        G.row_hash("r", "module m; endmodule\n", "module tb; endmodule\n", {"A": 2}),
                        G.row_hash("r", "module m; endmodule\n", "module tb; endmodule\n", {"B": 1})):
            self.assertNotEqual(base, changed)

    def test_stable_and_order_free(self):
        a = G.row_hash("r", "d", "t", {"A": 1, "B": 2})
        self.assertEqual(a, G.row_hash("r", "d", "t", {"B": 2, "A": 1}))
        self.assertEqual(G.row_hash("r", "d", "t", None), G.row_hash("r", "d", "t", {}))
        self.assertRegex(a, r"^[0-9a-f]{64}$")

    def test_flags_are_hashed(self):
        before = G.row_hash("r", "d", "t", {})
        saved = list(G.XRUN_FLAGS)
        try:
            G.XRUN_FLAGS.append("-extra")
            self.assertNotEqual(before, G.row_hash("r", "d", "t", {}))
        finally:
            G.XRUN_FLAGS[:] = saved


class XrefTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dut = os.path.join(self.tmp.name, "m.sv")
        with open(self.dut, "w") as f:
            f.write("module m; endmodule\n")
        self.tb = "module tb; endmodule\n"
        h = G.row_hash("good", "module m; endmodule\n", self.tb, {"P": 3})
        golden = G.empty_golden()
        golden["simulator"] = {"version": "test 1.0"}
        golden["rows"] = {
            "good": {"hash": h, "status": "ok", "cycles": ["CYCLE 0 y=1"]},
            "stale": {"hash": "0" * 64, "status": "ok", "cycles": ["CYCLE 0 y=1"]},
            "failed": {"hash": G.row_hash("failed", "module m; endmodule\n", self.tb, {"P": 3}),
                       "status": "xrun-compile-error", "cycles": [],
                       "message": "xmvlog: *E,ILLPRI (m.sv,2|16): illegal expression primary"},
        }
        self.path = os.path.join(self.tmp.name, "g.json")
        G.save(golden, self.path)
        self.xref = G.Xref(self.path)

    def tearDown(self):
        self.tmp.cleanup()

    def check(self, name, model):
        return self.xref.check(name, self.dut, self.tb, {"P": 3}, model, diff_test2.diff_traces)

    def test_statuses(self):
        self.assertEqual(self.check("good", [["CYCLE 0 y=1"]])[0], "XREF-MATCH")
        status, detail = self.check("good", [["CYCLE 0 y=0"]])
        self.assertEqual(status, "XREF-DIFF")
        self.assertTrue(any("sim : CYCLE 0 y=1" in ln for ln in detail), detail)
        self.assertEqual(self.check("stale", [["CYCLE 0 y=1"]])[0], "XREF-STALE")
        self.assertEqual(self.check("missing", [["CYCLE 0 y=1"]])[0], "XREF-NONE")
        status, detail = self.check("failed", [["CYCLE 0 y=1"]])
        self.assertEqual(status, "XREF-NONE")
        self.assertIn("xrun-compile-error", detail[0])
        self.assertEqual(self.xref.counts, {"match": 1, "diff": 1, "stale": 1, "none": 2})

    def test_any_accepted_schedule_matches(self):
        self.assertEqual(self.check("good", [["CYCLE 0 y=0"], ["CYCLE 0 y=1"]])[0], "XREF-MATCH")

    def test_changed_dut_goes_stale(self):
        with open(self.dut, "w") as f:
            f.write("module m; wire w; endmodule\n")
        self.assertEqual(self.check("good", [["CYCLE 0 y=1"]])[0], "XREF-STALE")

    def test_missing_file_is_an_error(self):
        with self.assertRaises(FileNotFoundError):
            G.Xref(os.path.join(self.tmp.name, "nope.json"))

    def test_serialization_is_deterministic(self):
        g = G.load(self.path)
        g["rows"] = dict(reversed(list(g["rows"].items())))
        self.assertEqual(G.dumps(g), G.dumps(G.load(self.path)))


class ClassifyTests(unittest.TestCase):
    def test_ok(self):
        out = ("xcelium> run\nCYCLE 0 a=1\nCYCLE 1 a=0\n"
               "Simulation complete via $finish(1) at time 9 NS + 0\nxcelium> exit\n")
        self.assertEqual(B.classify(0, out, "", "/w"),
                         ("ok", ["CYCLE 0 a=1", "CYCLE 1 a=0"], None, []))

    def test_warnings_are_codes_only(self):
        out = ("xmelab: *W,BNDWRN (./m.sv,3|4): out of bounds.\nxmelab: *W,BNDWRN (./m.sv,5|4): again.\n"
               "xcelium> run\nCYCLE 0 a=1\nSimulation complete via $finish(1) at time 9 NS + 0\n")
        status, _, msg, warns = B.classify(0, out, "", "/w")
        self.assertEqual((status, msg, warns), ("ok", None, ["xmelab:BNDWRN"]))

    def test_compile_error(self):
        out = ("xmvlog: *E,ILLPRI (bad.sv,2|16): illegal expression primary [4.2(IEEE)].\n"
               "xrun: *E,VLGERR: An error occurred during parsing.\n")
        status, cycles, msg, _ = B.classify(1, out, "", "/w")
        self.assertEqual((status, cycles), ("xrun-compile-error", []))
        self.assertIn("ILLPRI", msg)

    def test_runtime_error_keeps_the_partial_trace(self):
        out = "xcelium> run\nCYCLE 0 x=1\nxmsim: *F,FATSEV (./rt.sv,4): (time 0 FS).\n"
        status, cycles, msg, _ = B.classify(2, out, "", "/w")
        self.assertEqual((status, cycles), ("runtime-error", ["CYCLE 0 x=1"]))
        self.assertIn("FATSEV", msg)

    def test_no_finish_and_timeout(self):
        out = "xcelium> run\nCYCLE 0 a=1\n"
        self.assertEqual(B.classify(0, out, "", "/w")[0], "runtime-error")
        self.assertEqual(B.classify(124, out, "", "/w")[0], "timeout")
        self.assertEqual(B.classify(137, "", "", "/w")[0], "timeout")


class CommittedGoldenTests(unittest.TestCase):
    """The checked-in pin is well formed and covers exactly the simulated rows."""

    @classmethod
    def setUpClass(cls):
        cls.golden = G.load()
        with open(diff_test2.CASES_JSON) as f:
            cls.cases = {c["name"]: c for c in json.load(f)["cases"]}

    def test_present_and_versioned(self):
        self.assertIsNotNone(self.golden, "harness/sv/xcelium_golden.json is missing")
        self.assertRegex(self.golden["simulator"]["version"], r"\d+\.\d+")
        self.assertEqual(self.golden["simulator"]["name"], "Xcelium")

    def test_rows_are_the_simulated_rows(self):
        simulated = {n for n, c in self.cases.items() if "refusal" not in c}
        pinned = set(self.golden["rows"])
        # Rows added to cases2.json after the pin are reported as XREF-NONE,
        # not failures; rows the pin has but the corpus no longer does are stale data.
        self.assertEqual(pinned - simulated, set(), "pinned rows no longer in the corpus")

    def test_entries_are_well_formed(self):
        names = list(self.golden["rows"])
        self.assertEqual(names, sorted(names))
        for name, e in self.golden["rows"].items():
            with self.subTest(row=name):
                self.assertIn(e["status"], (G.STATUS_OK,) + G.FAILURE_STATUSES)
                if e["status"] == "no-testbench":
                    self.assertIsNone(e["hash"])
                else:
                    self.assertRegex(e["hash"], r"^[0-9a-f]{64}$")
                for ln in e["cycles"]:
                    self.assertTrue(ln.startswith("CYCLE "), ln)
                if e["status"] == G.STATUS_OK:
                    case = self.cases.get(name)
                    if case is not None:
                        self.assertEqual(len(e["cycles"]), len(case["stimulus"]))
                        for k, ln in enumerate(e["cycles"]):
                            self.assertTrue(ln.startswith("CYCLE %d " % k), ln)
                else:
                    self.assertTrue(e.get("message"))


if __name__ == "__main__":
    unittest.main()
