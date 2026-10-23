"""IEEE 16.3 immediate action lowering; value receipts are source-bound."""
from pathlib import Path
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=ImmediateActions | origin=spec | authority=IEEE-1800-2023#16.3 | map=checks:conditional-actions;implicit-error:retained-refusal;deferred:requires-observation-region;null-failure:unvalidated-parser-disagreement;invalid-source:frontend-error-barrier;symbolic:existing-boundary;effects:source-purity


class ImmediateActions(unittest.TestCase):
    def test_explicit_actions_preserve_assertion_kind(self):
        for keyword in ("assert", "assume", "cover"):
            body = keyword + '(gate) $display("yes");'
            if keyword != "cover":
                body += ' else $display("no");'
            design = lower("module top; logic gate; initial " + body + " endmodule")
            checks = [n for n in nodes(design) if n.get("assertion_lowered")]
            self.assertEqual(len(checks), 1)
            self.assertEqual((checks[0]["kind"], checks[0]["immediate_assertion"]), ("If", keyword))
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_default_assert_and_assume_diagnostic_is_not_dropped(self):
        for keyword in ("assert", "assume"):
            design = lower("module top; initial " + keyword + "(1); endmodule")
            check, = [n for n in nodes(design) if n.get("assertion_lowered")]
            self.assertEqual(check["else"]["sv_kind"], "ImmediateAssertion:implicit-error")

    def test_cover_has_no_failure_action(self):
        design = lower("module top; initial cover(0); endmodule")
        check, = [n for n in nodes(design) if n.get("assertion_lowered")]
        self.assertIsNone(check["else"])

    def test_explicit_empty_block_stays_distinct_from_omission(self):
        design = lower("module top; initial assert(0) else begin end endmodule")
        check, = [n for n in nodes(design) if n.get("assertion_lowered")]
        self.assertEqual(check["else"]["kind"], "Block")
        self.assertEqual(check["else"]["stmts"], [])

    def test_unvalidated_null_failure_stays_loud(self):
        design = lower("module top; initial assert(0) else; endmodule")
        self.assertIn("ImmediateAssertion:null-failure", [n.get("sv_kind") for n in nodes(design)])

    def test_deferred_forms_do_not_become_active_region_checks(self):
        for keyword in ("assert", "assume", "cover"):
            for delay in ("#0", "final"):
                design = lower("module top; logic gate; initial " + keyword + " " + delay + "(gate); endmodule")
                self.assertIn("ImmediateAssertion:deferred", [n.get("sv_kind") for n in nodes(design)])

    def test_effectful_and_folded_call_conditions_stay_loud(self):
        for cond in ("value++", "1 || bump()"):
            design = lower("module top; int value; function int bump(); value++; return 1; endfunction "
                           "initial assert(" + cond + ") else begin end endmodule")
            self.assertIn("ImmediateAssertion:condition", [n.get("sv_kind") for n in nodes(design)])

    def test_unsupported_actions_remain_visible(self):
        design = lower('module top; initial assert(0) else $error("failed"); endmodule')
        check, = [n for n in nodes(design) if n.get("assertion_lowered")]
        self.assertEqual(check["else"]["kind"], "SysCall")
        self.assertEqual(check["else"]["name"], "$error")

    def test_invalid_source_remains_a_design_barrier(self):
        design = lower("module top; initial assert(1) else begin end initial missing=1; endmodule", require_valid=False)
        self.assertIn("ImmediateAssertion:invalid-compilation", [n.get("sv_kind") for n in nodes(design)])

    def test_symbolic_path_keeps_its_boundary(self):
        design = symbolic("module divider; logic gate; always_comb assert(gate) else; endmodule")
        self.assertIn("ImmediateAssertion:symbolic", [n.get("sv_kind") for n in nodes(design)])

    def test_authored_acceptance_sources(self):
        root = Path(__file__).resolve().parents[2] / "Examples/system-verilog/immediate_assertions"
        for name in ("table", "actions", "timers"):
            design = lower((root / (name + ".sv")).read_text())
            self.assertTrue(any(n.get("assertion_lowered") for n in nodes(design)))
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))


if __name__ == "__main__":
    unittest.main()
