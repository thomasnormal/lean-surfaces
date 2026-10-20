"""IEEE 12.7.6 source retention, control transfer and admission."""
from pathlib import Path
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=ForeverLoops | origin=spec | authority=IEEE-1800-2023#12.7.6 | map=source-node:retain-body;admission:existing-lifetime-invalid-source-and-symbolic-boundaries


class ForeverLoops(unittest.TestCase):
    def test_retains_body_and_source_span_without_synthetic_control(self):
        design = lower("module top; int value; initial forever begin value++; break; end endmodule")
        node, = [n for n in nodes(design) if n.get("kind") == "Forever"]
        self.assertEqual(set(node), {"kind", "span", "body"})
        self.assertIsNotNone(node["span"])
        self.assertEqual(node["body"]["kind"], "Block")
        self.assertTrue(any(n.get("kind") == "Break" for n in nodes(node)))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_delay_event_and_continue_survive(self):
        for body, kind in [("#2;", "Delay"), ("@(posedge edge_signal);", "WaitEvent"),
                           ("continue;", "Continue")]:
            design = lower("module top; logic edge_signal; initial forever " + body + " endmodule")
            node, = [n for n in nodes(design) if n.get("kind") == "Forever"]
            self.assertEqual(node["body"]["kind"], kind)

    def test_static_body_lifetime_is_hoisted(self):
        for lifetime in ("", "static ", "automatic "):
            design = lower("module top; initial forever begin " + lifetime +
                           "int value=0; value++; break; end endmodule")
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))
            field = "automatic_scalar" if lifetime == "automatic " else "static_local_storage"
            self.assertTrue(any(n.get(field) for n in nodes(design)))

    def test_automatic_array_lifetime_uses_existing_lowering(self):
        design = lower("module top; initial forever begin automatic int cells[0:1]='{1,2}; cells[0]++; break; end endmodule")
        self.assertTrue(any(n.get("kind") == "Forever" for n in nodes(design)))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_disable_and_other_body_effects_are_not_discarded(self):
        for body in ("disable outer;", "$warning(\"body\");"):
            design = lower("module top; initial begin : outer forever " + body + " end endmodule")
            self.assertTrue(any(n.get("kind") == "Forever" for n in nodes(design)))
            self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_symbolic_forever_stays_loud(self):
        design = symbolic("module divider; initial forever #2; endmodule")
        self.assertIn("ForeverLoopStatement", [n.get("sv_kind") for n in nodes(design)])

    def test_frontend_errors_remain_design_barriers(self):
        design = lower("module top; initial forever #2; initial missing=1; endmodule", require_valid=False)
        self.assertIn("Loop:invalid-compilation", [n.get("sv_kind") for n in nodes(design)])

    def test_authored_sources_are_admitted(self):
        root = Path(__file__).resolve().parents[2] / "Examples/system-verilog/forever_loops"
        for source in root.glob("*.sv"):
            design = lower(source.read_text())
            self.assertTrue(any(n.get("kind") == "Forever" for n in nodes(design)))
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))


if __name__ == "__main__":
    unittest.main()
