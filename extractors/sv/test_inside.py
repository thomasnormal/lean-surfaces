"""IEEE 1800-2023 §11.4.13: pure integral membership admission."""
import unittest
from pathlib import Path

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=IntegralInside | origin=spec | authority=IEEE-1800-2023#11.4.13 | map=lowering:one-bit-wildcard-or-inclusive-range-with-common-operand-types;refusals:retain-effects-and-unsupported-storage


def expression(source, declarations="", require_valid=True):
    return lower("module top; " + declarations +
                 " logic [15:0] result; initial result = " + source +
                 "; endmodule", require_valid=require_valid)


def membership(design):
    return [n for n in nodes(design) if n.get("inside_lowered")]


class IntegralInside(unittest.TestCase):
    def assert_clean(self, design):
        self.assertTrue(membership(design))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_wildcard_union_is_one_bit_before_result_extension(self):
        design = expression("a inside {b, 4'bx001}", "logic [3:0] a, b;")
        self.assert_clean(design)
        root, = membership(design)
        self.assertEqual((root["op"], root["width"]), ("||", 1))
        for comparison in (root["left"], root["right"]):
            self.assertEqual((comparison["op"], comparison["width"]), ("==?", 1))
            self.assertEqual([comparison[s]["width"] for s in ("left", "right")], [4, 4])

    def test_signed_and_mixed_common_types(self):
        for item, extension in (("b", "SignedResize"), ("u", "Resize")):
            with self.subTest(item=item):
                design = expression("a inside {" + item + "}",
                                    "logic signed [3:0] a; logic signed [7:0] b; logic [7:0] u;")
                self.assert_clean(design)
                root, = membership(design)
                self.assertEqual(root["left"]["kind"], extension)
                self.assertEqual([root[s]["width"] for s in ("left", "right")], [8, 8])

    def test_ranges_keep_signedness_and_inclusive_bounds(self):
        for signed, prefix in (("", ""), ("signed", "s")):
            design = expression("a inside {[lo:hi]}", "logic " + signed + " [7:0] a, lo, hi;")
            self.assert_clean(design)
            root, = membership(design)
            self.assertEqual(root["op"], "&&")
            self.assertEqual([root[s]["op"] for s in ("left", "right")], [prefix + ">=", prefix + "<="])

    def test_dollar_endpoints_use_common_type_extrema(self):
        for signed, low, high in (("", "00000000", "11111111"),
                                  ("signed", "10000000", "01111111")):
            design = expression("a inside {[$:hi], [lo:$]}", "logic " + signed + " [7:0] a, lo, hi;")
            self.assert_clean(design)
            root, = membership(design)
            self.assertEqual(root["left"]["left"]["right"]["bits"], low)
            self.assertEqual(root["right"]["right"]["right"]["bits"], high)

    def test_array_cells_use_common_extension_and_slice_order(self):
        for signed, extension in (("signed", "SignedResize"), ("", "Resize")):
            design = expression("a inside {cells[1:0]}", "logic signed [7:0] a; logic " + signed + " [3:0] cells [2:0];")
            self.assert_clean(design)
            root, = membership(design)
            reads = [root[s]["right"] for s in ("left", "right")]
            self.assertEqual([r["kind"] for r in reads], [extension] * 2)
            self.assertEqual([r["operand"]["name"] for r in reads], ["cells[1]", "cells[0]"])

    def test_nested_pure_membership_is_admitted(self):
        self.assert_clean(expression("(a inside {b}) inside {1'b1}", "logic [3:0] a, b;"))

    def test_effectful_subject_or_item_is_loud(self):
        for source in ("a++ inside {1, 2}", "a inside {1, b++}",
                       "a inside {[b++:3]}", "a inside {f()}"):
            design = expression(source, "int a, b; function int f(); b++; return 2; endfunction")
            self.assertFalse(membership(design))
            self.assertTrue(any(n.get("sv_kind") == "InsideExpression:source" for n in nodes(design)))

    def test_tolerance_ranges_are_not_colon_ranges(self):
        for operator in ("+/-", "+%-"):
            design = expression("a inside {[2 " + operator + " 1]}", "int a;", require_valid=False)
            self.assertFalse(membership(design))
            self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_nonintegral_and_dynamic_storage_are_loud(self):
        for declaration, source in (("real a;", "a inside {1.0}"),
                                    ("int a, cells[];", "a inside {cells}"),
                                    ("int a, cells[0:1][0:1];", "a inside {cells}")):
            design = expression(source, declaration)
            self.assertFalse(membership(design))
            self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_frontend_errors_preserve_admission_barrier(self):
        for subject in ("a", "4'd1"):
            design = expression(subject + " inside {[$:$]}", "logic [3:0] a;", require_valid=False)
            self.assertTrue(any(n.get("sv_kind") == "InsideExpression:invalid-compilation" for n in nodes(design)))

    def test_constant_folding_cannot_bypass_membership_admission(self):
        for source in ("1 inside {[2 +/- 1]}", "1 inside {[2 +%- 1]}"):
            design = expression(source, require_valid=False)
            self.assertTrue(any(n.get("sv_kind") == "InsideExpression:item" for n in nodes(design)))
        design = expression("1 inside {2}")
        self.assert_clean(design)

    def test_symbolic_membership_stays_loud(self):
        for source in ("a inside {0, 1}", "1 inside {2}", "int'(1 inside {2})"):
            design = symbolic("module divider #(parameter W=8) (input logic [W-1:0] a, output logic [W-1:0] result); assign result = " + source + "; endmodule")
            self.assertFalse(membership(design))
            self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_authored_fixture_is_admitted(self):
        path = Path(__file__).resolve().parents[2] / "Examples/system-verilog/inside/inside.sv"
        self.assert_clean(lower(path.read_text()))


if __name__ == "__main__":
    unittest.main()
