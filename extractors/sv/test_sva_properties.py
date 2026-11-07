"""Concurrent SVA members stay in the symbolic property envelope (F1)."""
import json
import tempfile
import unittest
from pathlib import Path

import extract


class SvaProperties(unittest.TestCase):
    def test_assert_assume_cover_are_retained_metadata(self):
        source = """module top(input logic clk, rst_n, a, b, output logic q);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= 1'b0; else q <= a;
  assert property (@(posedge clk) disable iff (!rst_n) a |-> b);
  assume property (@(posedge clk) a |=> b);
  cover property (@(posedge clk) a ##1 b);
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]
        self.assertEqual([p["property_kind"] for p in module["properties"]],
                         ["assert", "assume", "cover"])
        self.assertEqual([p["clock"] for p in module["properties"]],
                         ["clk", "clk", "clk"])
        self.assertEqual([p["kind"] for p in module["properties"]],
                         ["SvaProperty"] * 3)
        self.assertEqual(module["properties"][0]["ast"]["kind"], "SvaCheck")
        self.assertEqual(module["properties"][0]["ast"]["edge"], "posedge")
        self.assertEqual(module["properties"][0]["ast"]["property"]["kind"],
                         "SvaDisable")
        self.assertEqual(module["properties"][1]["ast"]["property"]["kind"],
                         "SvaNonoverlap")
        self.assertEqual(module["properties"][2]["ast"]["property"]["kind"],
                         "SvaAlways")
        self.assertEqual([p["kind"] for p in module["processes"]],
                         ["AlwaysPosedge"])
        self.assertFalse(any(n.get("sv_kind") == "ProceduralBlockSymbol:NoEventControl"
                             for n in module["others"]))

    def test_generate_scope_assertion_is_retained_at_module_level(self):
        source = """module top(input logic clk, a);
  if (1) begin : g
    assert property (@(posedge clk) a);
  end
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "generated.sv"
            out = Path(directory) / "generated.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]
        self.assertEqual(len(module["properties"]), 1)
        self.assertEqual(module["properties"][0]["property_kind"], "assert")
        self.assertEqual(module["properties"][0]["path"], ["g"])
        self.assertEqual(module["generates"][0]["then"], [])

    def test_structured_boolean_ast_keeps_slang_expression_tree(self):
        source = """module top(input logic clk, a, b, c);
  assert property (@(posedge clk) (a && b) |-> (!c || (a === b)));
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "expr.sv"
            out = Path(directory) / "expr.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            prop = json.loads(out.read_text())["design"]["modules"][0]["properties"][0]
        implication = prop["ast"]["property"]
        self.assertEqual(implication["kind"], "SvaImplication")
        self.assertEqual(implication["antecedent"]["test"]["expr"]["kind"],
                         "Binary")
        self.assertEqual(implication["antecedent"]["test"]["expr"]["op"], "&&")
        self.assertEqual(implication["consequent"]["test"]["expr"]["kind"],
                         "Binary")

    def test_qualified_signal_path_stays_one_observation_key(self):
        source = """module leaf(input logic a, output logic flag);
  assign flag = a;
endmodule
module top(input logic clk, a, output logic q);
  leaf u (.a(a), .flag(q));
  assert property (@(posedge clk) u.flag == a);
endmodule
"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "scoped.sv"
            out = Path(directory) / "scoped.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            prop = json.loads(out.read_text())["design"]["modules"][0]["properties"][0]
        expr = prop["ast"]["property"]["body"]["test"]["expr"]
        self.assertEqual(expr["op"], "==")
        self.assertEqual(expr["left"], {"kind": "Ident", "name": "u.flag"})
        self.assertEqual(expr["right"], {"kind": "Ident", "name": "a"})


if __name__ == "__main__":
    unittest.main()
