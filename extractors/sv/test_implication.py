"""Pure §11.4.7 logical implication lowers without changing operand widths."""
import unittest
from pathlib import Path

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=LogicalImplication | origin=spec | authority=IEEE-1800-2023#11.4.7 | map=lowering:not-antecedent-or-consequent-with-self-determined-operands;refusals:preserve-admission-before-folding


def implications(design):
    return [n for n in nodes(design) if n.get("implication_lowered")]


class LogicalImplication(unittest.TestCase):
    def test_mismatched_operand_widths_are_self_determined(self):
        design = lower("module top; logic signed [2:0] a; logic [4:0] b; logic [15:0] result; initial result = a -> b; endmodule")
        root, = implications(design)
        self.assertEqual((root["op"], root["width"]), ("||", 1))
        self.assertEqual((root["left"]["op"], root["left"]["width"]), ("!", 1))
        self.assertEqual(root["left"]["operand"]["width"], 3)
        self.assertEqual(root["right"]["width"], 5)
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_frontend_right_associativity_is_preserved(self):
        design = lower("module top; logic a, b, c, result; initial result = a -> b -> c; endmodule")
        root = implications(design)[0]
        self.assertTrue(root["right"]["implication_lowered"])
        self.assertEqual(root["left"]["operand"]["name"], "a")
        self.assertEqual(root["right"]["left"]["operand"]["name"], "b")

    def test_effectful_operands_stay_loud_even_when_skipped(self):
        for source in ("a++ -> b", "a -> b++", "1'b0 -> f()", "f() -> 1'b1"):
            design = lower("module top; int a, b; logic [15:0] result; function int f(); a++; return 1; endfunction initial result = " + source + "; endmodule")
            self.assertFalse(implications(design))
            self.assertTrue(any(n.get("sv_kind") == "BinaryExpression:LogicalImplication:source" for n in nodes(design)))

    def test_constant_implication_is_checked_before_folding(self):
        design = lower("module top; logic [15:0] result; initial result = 1'b0 -> 1'bx; endmodule")
        self.assertEqual(len(implications(design)), 1)

    def test_equivalence_stays_loud_even_when_constant(self):
        for source in ("a <-> b", "1'b0 <-> 1'b1"):
            design = lower("module top; logic a, b; logic [15:0] result; initial result = " + source + "; endmodule")
            self.assertTrue(any(n.get("sv_kind") == "BinaryExpression:LogicalEquivalence" for n in nodes(design)))

    def test_nonintegral_operands_are_loud(self):
        design = lower("module top; real a, b; logic result; initial result = a -> b; endmodule", require_valid=False)
        self.assertFalse(implications(design))
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_symbolic_implication_retains_logical_vocabulary(self):
        design = symbolic("module divider #(parameter W=4) (input logic [W-1:0] a, b, output logic result); assign result = a -> b; endmodule")
        root, = implications(design)
        self.assertEqual((root["op"], root["left"]["op"]), ("||", "!"))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_symbolic_arithmetic_context_preserves_operand_boundaries(self):
        design = symbolic("module divider #(parameter W=8) (input logic [1:0] a, input logic [2:0] b, output logic [W-1:0] result); assign result = (a -> b) / 1'b1; endmodule")
        root, = implications(design)
        self.assertEqual(root["left"]["operand"]["width"], 2)
        self.assertEqual(root["right"]["width"], 3)
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_frontend_error_barrier_in_both_modes(self):
        body = "logic a, b, result; int unrelated = missing; initial result = a -> b; endmodule"
        for design in (lower("module top; " + body, require_valid=False), symbolic("module divider; " + body)):
            self.assertTrue(any(n.get("sv_kind") == "LogicalImplication:invalid-compilation" for n in nodes(design)))

    def test_authored_values_fixture_is_admitted(self):
        path = Path(__file__).resolve().parents[2] / "Examples/system-verilog/implication/values.sv"
        design = lower(path.read_text())
        self.assertGreater(len(implications(design)), 20)
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))


if __name__ == "__main__":
    unittest.main()
