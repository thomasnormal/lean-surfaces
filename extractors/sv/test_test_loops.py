"""IEEE 12.7.4/12.7.5 pre-/post-test loop lowering and admission."""
from pathlib import Path
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=TestLoops | origin=spec | authority=IEEE-1800-2023#12.7.4-12.7.5 | map=source-nodes:retain-condition-and-body;admission:existing-integral-purity-lifetime-boundaries


def loop(body, condition="value", post=False):
    return ("do " + body + " while(" + condition + ");" if post else
            "while(" + condition + ") " + body)


class TestLoops(unittest.TestCase):
    def test_nodes_retain_condition_width_and_body(self):
        for post, kind in ((False, "While"), (True, "DoWhile")):
            design = lower("module top; logic [3:0] value; initial " +
                           loop("value=0;", post=post) + " endmodule")
            node, = [n for n in nodes(design) if n.get("kind") == kind]
            self.assertEqual((node["condition"]["name"], node["condition"]["width"]),
                             ("value", 4))
            self.assertEqual(node["body"]["kind"], "BlockingAssign")
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_authored_fixtures_are_admitted(self):
        root = Path(__file__).resolve().parents[2] / "Examples/system-verilog/test_loops"
        for name in ("values", "waits", "timers"):
            design = lower((root / (name + ".sv")).read_text())
            self.assertTrue(any(n.get("kind") == "While" for n in nodes(design)))
            self.assertTrue(any(n.get("kind") == "DoWhile" for n in nodes(design)))
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_effectful_conditions_stay_loud(self):
        for post in (False, True):
            for condition in ("value++", "32'(f())"):
                design = lower("module top; integer value; function int f(); value++; return 0; endfunction initial " +
                               loop(";", condition, post) + " endmodule")
                self.assertTrue(any(n.get("sv_kind", "").endswith(":condition")
                                    for n in nodes(design)))

    def test_real_conditions_stay_loud(self):
        for post in (False, True):
            design = lower("module top; real value; initial " + loop(";", post=post) + " endmodule")
            self.assertTrue(any(n.get("sv_kind", "").endswith(":condition")
                                for n in nodes(design)))

    def test_unmodelled_scalar_body_lifetime_stays_loud(self):
        for post in (False, True):
            design = lower("module top; initial " +
                           loop("begin integer local_value=0; local_value++; end", "1", post) + " endmodule")
            self.assertTrue(any(n.get("sv_kind", "").endswith(":body-lifetime")
                                for n in nodes(design)))

    def test_automatic_array_body_reuses_lifetime_lowering(self):
        for post in (False, True):
            design = lower("module top; integer value; initial " +
                           loop("begin automatic int cells[0:1]='{1,2}; value=cells[0]; break; end", "1", post) + " endmodule")
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_symbolic_loops_stay_loud(self):
        for post in (False, True):
            design = symbolic("module divider; integer value; initial " +
                              loop("value=0;", post=post) + " endmodule")
            self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_frontend_errors_remain_design_barriers(self):
        for post in (False, True):
            design = lower("module top; integer value; initial " +
                           loop("value=0;", post=post) + " initial missing=1; endmodule", require_valid=False)
            self.assertTrue(any(n.get("sv_kind") == "Loop:invalid-compilation" for n in nodes(design)))


if __name__ == "__main__":
    unittest.main()
