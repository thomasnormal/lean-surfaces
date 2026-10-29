#!/usr/bin/env python3
"""Offline tests of harness/sv/xcelium_compare.py: no simulator, no Lean.

Synthetic traces exercise the three equivalence layers, the row classes, the
declaration verdicts and the cause routing. Run:
    python3 harness/sv/test_xcelium_compare.py
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import xcelium_compare as C  # noqa: E402


def tr(*cycles):
    """tr(('a=01', 'y=x1'), ('a=10', 'y=11')) -> CYCLE lines."""
    return ["CYCLE %d %s" % (i, " ".join(c)) for i, c in enumerate(cycles)]


def rec(model, x, icarus="skip", case=None, accept=("src",), x_stale=False, x_status="ok", warnings=()):
    base = dict(name="r", example="e", top="partsel", signals=["a", "y"], stimulus=[{}] * len(model["src"]))
    base.update(case or {})
    case = base
    r = dict(name="r", case=case, accept=list(accept), model=model,
             xcelium=dict(status=x_status, cycles=x, stale=x_stale, warnings=list(warnings), message=None),
             icarus=(dict(status="ok", cycles=icarus, why=None) if icarus != "skip"
                     else dict(status="compile-fail", cycles=None, why="rc=134 boom")),
             ports=[])
    C.classify(r)
    return r


class DiffDetail(unittest.TestCase):
    def test_identical_is_none(self):
        self.assertIsNone(C.diff_detail(tr(("a=0", "y=1")), tr(("a=0", "y=1"))))

    def test_kinds(self):
        d = C.diff_detail(tr(("a=01", "y=xxxx")), tr(("a=01", "y=xx10")))   # a = Xcelium
        self.assertEqual(d["kinds"], {"A_unknown"})
        self.assertEqual(d["cycles"], [0])
        self.assertEqual(d["signals"], ["y"])
        d = C.diff_detail(tr(("y=1x",)), tr(("y=1z",)))
        self.assertEqual(d["kinds"], {"xz"})
        d = C.diff_detail(tr(("y=10",)), tr(("y=11",)))
        self.assertEqual(d["kinds"], {"value"})
        d = C.diff_detail(tr(("y=1",), ("y=1",)), tr(("y=1",)))
        self.assertEqual(d["length"], (2, 1))
        self.assertIn("missing", d["kinds"])

    def test_xk0(self):
        # differs in cycle 0 only, x vs known: the time-zero allowance
        d = C.diff_detail(tr(("y=x",), ("y=1",)), tr(("y=1",), ("y=1",)))
        self.assertTrue(C.xk0_equal(d))
        # the same difference in cycle 1 is NOT allowed
        d = C.diff_detail(tr(("y=1",), ("y=x",)), tr(("y=1",), ("y=1",)))
        self.assertFalse(C.xk0_equal(d))
        # cycle 0 with a value difference is NOT allowed
        d = C.diff_detail(tr(("y=0",), ("y=1",)), tr(("y=1",), ("y=1",)))
        self.assertFalse(C.xk0_equal(d))

    def test_xk_direction(self):
        d = C.diff_detail(tr(("y=xx",)), tr(("y=10",)))
        self.assertEqual(C.xk_direction(d), "A-only")
        d = C.diff_detail(tr(("y=10",)), tr(("y=xx",)))
        self.assertEqual(C.xk_direction(d), "B-only")
        d = C.diff_detail(tr(("y=x0",)), tr(("y=1x",)))
        self.assertEqual(C.xk_direction(d), "both")
        d = C.diff_detail(tr(("y=x0",)), tr(("y=11",)))
        self.assertIsNone(C.xk_direction(d))


class Classes(unittest.TestCase):
    A = tr(("a=0", "y=1"))
    B = tr(("a=0", "y=0"))
    ALLX = tr(("a=0", "y=x"))

    def test_equal_exact_icarus_agrees(self):
        r = rec({"src": self.A}, self.A, self.A)
        self.assertEqual(r["class"], "model==X, Icarus agrees")
        self.assertEqual(r["verdict"]["mx_layer"], "exact")

    def test_equal_up_to_accepted_schedule_is_its_own_layer(self):
        r = rec({"src": self.A, "rev": self.B}, self.B, self.B, accept=("src", "rev"))
        self.assertEqual(r["verdict"]["mx"], "equal")
        self.assertEqual(r["verdict"]["mx_layer"], "schedule")

    def test_differs_icarus_departs_from_neither(self):
        r = rec({"src": self.A}, self.ALLX, self.A)
        self.assertEqual(r["class"], "model!=X, Icarus==model (Xcelium departs from both)")
        r = rec({"src": self.A}, self.B, self.B)
        self.assertEqual(r["class"], "model!=X, Icarus==X (model departs from both)")
        r = rec({"src": self.A}, self.B, self.ALLX)
        self.assertEqual(r["class"], "model!=X, three-way split")

    def test_no_icarus(self):
        r = rec({"src": self.A}, self.A)
        self.assertEqual(r["class"], "model==X, no Icarus trace")
        r = rec({"src": self.A}, self.B)
        self.assertEqual(r["class"], "model!=X, no Icarus trace")

    def test_xcelium_not_run_and_stale_make_no_verdict(self):
        r = rec({"src": self.A}, None, self.A, x_status="xrun-compile-error")
        self.assertEqual(r["class"], "x-not-run")
        r = rec({"src": self.A}, self.B, self.A, x_stale=True)
        self.assertEqual(r["class"], "stale")

    def test_undeclared_icarus_difference_is_loud(self):
        r = rec({"src": self.A}, self.A, self.B)
        self.assertEqual(r["class"], "model==X, Icarus differs (UNDECLARED)")


class Declarations(unittest.TestCase):
    A = tr(("a=0", "y=1"))
    B = tr(("a=0", "y=0"))
    ALLX = tr(("a=0", "y=x"))

    def decl(self, x, icarus=None):
        od = dict(id="iverilog-test", sim="iverilog", sigma="src", sim_trace=self.B, lean_trace=self.A,
                  observed="Icarus departs", reference="IEEE")
        r = rec({"src": self.A}, x, icarus if icarus is not None else self.B, case=dict(oracle_disagreement=od))
        return r["declaration"]

    def test_confirmed(self):
        self.assertEqual(self.decl(self.A)["verdict"], "CONFIRMED")

    def test_contradicted_xcelium_sides_with_icarus(self):
        self.assertEqual(self.decl(self.B)["verdict"], "CONTRADICTED:X==icarus")

    def test_contradicted_neither(self):
        self.assertEqual(self.decl(self.ALLX)["verdict"], "CONTRADICTED:neither")

    def test_stale_recorded_trace_is_noted(self):
        d = self.decl(self.A, icarus=self.ALLX)
        self.assertTrue(any("sim_trace" in n for n in d["notes"]))

    def xdecl(self, x, model=None, icarus=None):
        """A declaration naming Xcelium itself: sim_trace is the PINNED Xcelium
        trace (here ALLX), lean_trace the model's (A)."""
        od = dict(id="xcelium-test", sim="xcelium", sigma="src", sim_trace=self.ALLX, lean_trace=self.A,
                  observed="Xcelium departs", reference="IEEE")
        r = rec({"src": model or self.A}, x, icarus if icarus is not None else self.A,
                case=dict(oracle_disagreement=od))
        return r["declaration"]

    def test_declared_xcelium_departure_holds_resolves_or_changes(self):
        self.assertEqual(self.xdecl(self.ALLX)["verdict"], "DECLARED-XCELIUM:holds")
        self.assertEqual(self.xdecl(self.A)["verdict"], "DECLARED-XCELIUM:resolved")
        self.assertEqual(self.xdecl(self.B)["verdict"], "DECLARED-XCELIUM:changed")
        # the model moved: the recorded lean_trace no longer holds
        d = self.xdecl(self.ALLX, model=self.B, icarus=self.B)
        self.assertEqual(d["verdict"], "DECLARED-XCELIUM:changed")
        self.assertTrue(any("lean_trace" in n for n in d["notes"]))

    def test_declared_xcelium_departure_does_not_compare_icarus_to_the_recorded_trace(self):
        # Icarus equals the model here (it is NOT the recorded sim_trace): no note.
        self.assertEqual(self.xdecl(self.ALLX, icarus=self.A)["notes"], [])

    def test_icarus_unavailable(self):
        r = rec({"src": self.A}, self.A, case=dict(icarus_unavailable=dict(id="iu")))
        self.assertEqual(r["declaration"], dict(kind="icarus_unavailable", id="iu", verdict="CONFIRMED",
                                                notes=[], text_claims_xcelium=False))
        r = rec({"src": self.A}, self.B, case=dict(icarus_unavailable=dict(id="iu")))
        self.assertEqual(r["declaration"]["verdict"], "model!=X")


class Routing(unittest.TestCase):
    def test_cause_by_dut_and_signal(self):
        c = dict(top="partsel")
        self.assertEqual(C.cell_cause(c, "ov_hi"), "P1")
        self.assertEqual(C.cell_cause(c, "dyn_up"), "P2")
        self.assertEqual(C.cell_cause(c, "w_hi"), "P3")
        self.assertIsNone(C.cell_cause(c, "rev_up"))
        self.assertEqual(C.cell_cause(dict(top="array_oob"), "over"), "P1")
        self.assertEqual(C.cell_cause(dict(top="array_oob_part"), "w_flat"), "P3")
        self.assertEqual(C.cell_cause(dict(top="m", file="hier_width"), "in_narrow"), "H1")
        # round 6: the admitted half of partsel keeps its run-time selects in P2
        self.assertEqual(C.cell_cause(dict(top="partsel_dyn"), "dyn_up"), "P2")
        self.assertIsNone(C.cell_cause(dict(top="partsel_dyn"), "rev_up"))

    def test_unrouted_cell_is_unclustered(self):
        A = tr(("a=0", "y=1"))
        r = rec({"src": A}, tr(("a=0", "y=0")), A, case=dict(top="unknown_dut"))
        self.assertEqual(C.row_clusters(r), ["UNCLUSTERED"])

    def test_clean_row_has_no_cluster(self):
        A = tr(("a=0", "y=1"))
        self.assertEqual(C.row_clusters(rec({"src": A}, A, A)), [])


if __name__ == "__main__":
    unittest.main()
