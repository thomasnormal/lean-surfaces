"""IEEE 12.5.4 admission and reuse of integral membership operators."""
from pathlib import Path
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=CaseInside | origin=spec | authority=IEEE-1800-2023#12.5.4 | map=lowering:asymmetric-wildcard-or-inclusive-range;admission:retain-effects-and-whole-case-type


def source(items, declarations="logic [3:0] subject;", subject="subject"):
    return "module top; " + declarations + " initial case(" + subject + ") inside " + items + " endcase endmodule"


def comparisons(design):
    return [n["cond"] for n in nodes(design) if n.get("case_lowered")]


class CaseInside(unittest.TestCase):
    def test_scalar_patterns_reuse_asymmetric_equality(self):
        design = lower(source("4'b1x0z:; 4'd2:;"))
        self.assertEqual([n["op"] for n in comparisons(design)], ["==?", "==?"])
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_whole_case_width_and_signedness(self):
        for label, width, resize in (("signed_item", 8, "SignedResize"),
                                     ("unsigned_item", 8, "Resize"),
                                     ("32'd2", 32, "Resize")):
            design = lower(source(label + ":;", "logic signed [3:0] subject; logic signed [7:0] signed_item; logic [7:0] unsigned_item;"))
            comparison, = comparisons(design)
            self.assertEqual(comparison["left"]["width"], width)
            self.assertEqual(comparison["right"]["width"], width)
            self.assertEqual(comparison["left"]["kind"], resize)

    def test_signed_inclusive_ranges_and_grouped_labels(self):
        design = lower(source("[lo:hi], 8'sd4:;", "logic signed [7:0] subject, lo, hi;"))
        bounds, scalar = comparisons(design)
        self.assertEqual(bounds["op"], "&&")
        self.assertEqual([bounds[s]["op"] for s in ("left", "right")], ["s>=", "s<="])
        self.assertEqual(scalar["op"], "==?")

    def test_dollar_labels_retain_context_boundary(self):
        design = lower(source("[$:hi]:; [lo:$]:;", "logic signed [7:0] subject, lo, hi;"))
        self.assertIn("CaseStatement:pattern", [n.get("sv_kind") for n in nodes(design)])

    def test_fixed_array_elements_retain_common_width_and_slice_order(self):
        design = lower(source("cells[1:0]:;", "logic signed [7:0] subject; logic signed [7:0] cells[2:0];"))
        reads = [n["right"] for n in comparisons(design)]
        self.assertEqual([n["kind"] for n in reads], ["Ident"] * 2)
        self.assertEqual([n["name"] for n in reads], ["cells[1]", "cells[0]"])

    def test_array_widening_needs_case_specific_conversion(self):
        for signed in ("", "signed"):
            design = lower(source("cells:;", "logic signed [7:0] subject; logic " + signed + " [3:0] cells[2:0];"))
            self.assertIn("CaseStatement:pattern", [n.get("sv_kind") for n in nodes(design)])

    def test_effectful_sources_cannot_be_folded_away(self):
        declarations = "int subject, lo; function int f(); lo++; return 1; endfunction"
        for subject, items, tag in [("subject++", "1:;", "subject"),
                                     ("f()", "1:;", "subject"),
                                     ("subject", "f():;", "pattern"),
                                     ("subject", "[lo++:4]:;", "pattern")]:
            design = lower(source(items, declarations, subject))
            self.assertIn("CaseStatement:" + tag, [n.get("sv_kind") for n in nodes(design)])

    def test_tolerance_and_unsupported_storage_stay_loud(self):
        for items, declarations in [("[2 +/- 1]:;", "int subject;"),
                                     ("[2 +%- 1]:;", "int subject;"),
                                     ("cells:;", "int subject, cells[];"),
                                     ("1.5:;", "real subject;")]:
            design = lower(source(items, declarations), require_valid=False)
            self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_qualifiers_and_default_only_remain_explicit(self):
        for qualifier in ("unique", "unique0", "priority"):
            design = lower(source("1:;").replace("initial case", "initial " + qualifier + " case"))
            self.assertIn("CaseStatement:" + qualifier.capitalize(), [n.get("sv_kind") for n in nodes(design)])
        self.assertIn("CaseStatement:empty", [n.get("sv_kind") for n in nodes(lower(source("default:;")))])

    def test_frontend_errors_retain_design_barrier(self):
        design = lower(source("1:;").replace("endmodule", "initial missing=1; endmodule"), require_valid=False)
        self.assertIn("CaseStatement:invalid-compilation", [n.get("sv_kind") for n in nodes(design)])

    def test_existing_symbolic_structural_path_is_preserved(self):
        design = symbolic("module divider(input logic [3:0] subject, output logic result); always_comb case(subject) inside 4'b1x0z: result=1; default: result=0; endcase endmodule")
        case, = [n for n in nodes(design) if n.get("kind") == "Case"]
        self.assertEqual(case["match"], "inside")
        self.assertFalse(comparisons(design))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_authored_sources_are_admitted(self):
        root = Path(__file__).resolve().parents[2] / "Examples/system-verilog/case_inside"
        for path in root.glob("*.sv"):
            design = lower(path.read_text())
            if path.stem == "array_widening":
                self.assertIn("CaseStatement:pattern", [n.get("sv_kind") for n in nodes(design)])
                continue
            self.assertTrue(comparisons(design))
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))


if __name__ == "__main__":
    unittest.main()
