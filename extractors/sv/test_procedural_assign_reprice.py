"""Shape checks for procedural assign/force repricing."""

import unittest

from procedural_assign_reprice import procedural_assign_features


class ProceduralAssignReprice(unittest.TestCase):
    def test_assign_concat_and_rhs(self):
        self.assertEqual(
            procedural_assign_features("assign {a, b} = src;",
                                       "logic a, b; logic src;"),
            ("assign", "concat-lhs", "rhs-expression", "variable-target"),
        )

    def test_force_select_and_net(self):
        self.assertEqual(
            procedural_assign_features("force w[7:4] = 4'hf;",
                                       "wire [7:0] w;"),
            ("force", "select-lhs", "net-target"),
        )

    def test_contextual_priority_diagnostic_and_event(self):
        source = """\
:type: compile_error
module top;
  logic a;
  assign a = 1'b0;
  always @(posedge clk) force a = 1'b1;
endmodule
"""
        self.assertEqual(
            procedural_assign_features(
                "force a = 1'b1;",
                source + "// force overrides the prior assignment, is reevaluated, and is a new assign\n",
            ),
            ("force", "variable-target", "rhs-reevaluation",
             "priority-override", "replace-active",
             "mixed-assignment-diagnostic", "event-sensitive"),
        )


if __name__ == "__main__":
    unittest.main()
