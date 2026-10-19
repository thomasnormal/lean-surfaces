"""Symbolic continuous assignments may split one sampled RHS over leaves."""
import json
import tempfile
import unittest
from pathlib import Path

import extract


class SymbolicConcatTargets(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())

    def test_direct_leaves_keep_source_order(self):
        envelope = self.extract(
            "module top(input logic [7:0] source, output wire [3:0] upper, "
            "output wire [3:0] lower); "
            "assign {upper, lower} = source; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(process["kind"], "Assign")
        self.assertEqual(process["target"]["kind"], "ConcatTarget")
        self.assertEqual([part["name"] for part in process["target"]["parts"]],
                         ["upper", "lower"])
        self.assertEqual(process["target"]["width"], 8)

    def test_nested_leaves_are_flattened(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output wire a, output wire b, "
            "output wire c, output wire d); "
            "assign {{a, b}, {c, d}} = source; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([part["name"] for part in process["target"]["parts"]],
                         ["a", "b", "c", "d"])

    def test_rhs_target_alias_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] a, output wire b, output wire c); "
            "assign {b, c} = {a[0], b}; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(process["kind"], "Unsupported")
        self.assertEqual(process["sv_kind"], "AssignmentExpression:target")

    def test_dynamic_leaf_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, input integer index, "
            "output wire [1:0] a, output wire b); "
            "assign {a[index], b} = source; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(process["kind"], "Unsupported")
        self.assertIn(process["sv_kind"],
                      {"AssignmentExpression:target",
                       "ContinuousAssignSymbol:InvalidExpression"})


if __name__ == "__main__":
    unittest.main()
