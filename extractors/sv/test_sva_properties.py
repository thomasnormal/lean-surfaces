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
        self.assertEqual([p["kind"] for p in module["processes"]],
                         ["AlwaysPosedge"])
        self.assertFalse(any(n.get("sv_kind") == "ProceduralBlockSymbol:NoEventControl"
                             for n in module["others"]))


if __name__ == "__main__":
    unittest.main()
