"""Wildcard statement admission; full simulation receipts live in the fixtures."""
import unittest
from pathlib import Path
from test_bit_queries import lower, nodes
from test_division import symbolic

REPO = Path(__file__).resolve().parents[2]
# SYNTHETIC-ORACLE: tests=WildcardCase | origin=spec | authority=IEEE-1800-2023#12.5.1 | map=casez:symmetric-Z;casex:symmetric-XZ;control:first-match


def source(body, declarations=""):
    return "module top; logic [3:0] subject,item; " + declarations + " initial begin " + body + " end endmodule"


def comparisons(design):
    return [n for n in nodes(design) if n.get("kind") == "CaseMatch"]


class WildcardCases(unittest.TestCase):
    def test_both_modes_retain_dynamic_values(self):
        for mode in ("casez", "casex"):
            design=lower(source(mode+"(subject) item:; endcase"))
            comparison,=comparisons(design)
            self.assertEqual(comparison["mode"],mode)
            self.assertEqual(comparison["left"]["name"],"subject")
            self.assertEqual(comparison["right"]["name"],"item")
            self.assertEqual(comparison["width"],1)

    def test_whole_case_sizing_and_sign(self):
        for mode in ("casez","casex"):
            design=lower(source(mode+"(subject) 8'sd1:; 4'bz:; endcase"))
            for cmp in comparisons(design):
                self.assertEqual(cmp["left"]["width"],8)
                self.assertEqual(cmp["right"]["width"],8)

    def test_question_mark_is_a_z_value(self):
        cmp,=comparisons(lower(source("casez(subject) 4'b1??0:; endcase")))
        self.assertEqual(cmp["right"]["bits"],"1zz0")

    def test_source_order_and_grouped_labels(self):
        design=lower(source("casez(subject) default: subject=3; 4'bzzzz,4'b1000: subject=1; 4'b1zzz: subject=2; endcase"))
        cmp=comparisons(design)
        self.assertEqual([n["right"]["bits"] for n in cmp],["zzzz","1000","1zzz"])

    def test_delayed_body_is_retained_after_match(self):
        design=lower(source("casez(subject) 4'b1zzz: begin #2; subject=0; end default:; endcase"))
        lowered=next(n for n in nodes(design) if n.get("case_lowered"))
        self.assertEqual(lowered["cond"]["kind"],"CaseMatch")
        self.assertTrue(any(n.get("kind")=="Delay" for n in nodes(lowered["then"])))

    def test_effectful_values_and_nested_effects_stay_loud(self):
        for mode in ("casez","casex"):
            for body in (mode+"(subject++) item:; endcase",mode+"(subject) item++:; endcase",mode+"(subject+subject++) item:; endcase"):
                self.assertFalse(comparisons(lower(source(body))))

    def test_folded_calls_stay_loud(self):
        declarations='function automatic logic [3:0] value(); value=1; endfunction '
        for mode in ("casez","casex"):
            for body in (mode+"(1 ? value() : 4'd0) item:; endcase",mode+"(subject) value():; endcase"):
                self.assertFalse(comparisons(lower(source(body,declarations))))

    def test_qualifier_obligations_stay_loud(self):
        for mode in ("casez","casex"):
            for qualifier in ("unique","unique0","priority"):
                design=lower(source(qualifier+" "+mode+"(subject) item:; endcase"))
                self.assertFalse(comparisons(design))
                self.assertTrue(any(n.get("kind")=="Unsupported" for n in nodes(design)))

    def test_unsupported_types_stay_loud(self):
        for mode in ("casez","casex"):
            self.assertFalse(comparisons(lower(source(mode+"(1.5) 1.5:; endcase"),require_valid=False)))

    def test_invalid_compilation_has_design_barrier(self):
        design=lower(source("casez(subject) item:; endcase","int bad=missing;"),require_valid=False)
        self.assertTrue(any(n.get("sv_kind")=="CaseStatement:invalid-compilation" for n in nodes(design)))

    def test_symbolic_mode_retains_its_boundary(self):
        for mode in ("casez","casex"):
            design=symbolic('module divider(input logic [3:0] subject, output logic q); always_comb '+mode+'(subject) 4\'b1zzz:q=1; default:q=0; endcase endmodule')
            self.assertFalse(comparisons(design))
            self.assertTrue(any(n.get("kind")=="Unsupported" for n in nodes(design)))

    def test_authored_sources_are_admitted(self):
        for path in (REPO/"Examples/system-verilog/wildcard_cases").glob("*.sv"):
            design=lower(path.read_text())
            self.assertTrue(comparisons(design))
            self.assertFalse(any(n.get("kind")=="Unsupported" for n in nodes(design)))


if __name__=="__main__":
    unittest.main()
