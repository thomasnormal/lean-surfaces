"""Shape checks for event-expression repricing."""

import unittest

from event_expression_reprice import event_expression_features


class EventExpressionReprice(unittest.TestCase):
    def test_multibit_edge(self):
        self.assertEqual(
            event_expression_features(
                "always @(posedge bus) edge_count++;",
                "module top; logic [3:0] bus; endmodule",
                "/tests/chapter-9/9.4.2--edge.sv",
            ),
            ("edge-event", "multibit-lsb-edge"),
        )

    def test_expression_shapes(self):
        self.assertEqual(
            event_expression_features(
                "@(a | b) count++;",
                "module top; // expression result changes, no event if unchanged\nendmodule",
                "/tests/chapter-9/9.4.2--expr.sv",
            ),
            ("value-change-event", "binary-expression", "result-change-filter"),
        )

    def test_concat_select_and_scheduler(self):
        self.assertEqual(
            event_expression_features(
                "@({a, b}) count++;",
                "module top; logic [7:0] arr[4]; // aggregate expression\nendmodule",
                "/tests/chapter-4/4.4--regions.sv",
            ),
            ("value-change-event", "concat-expression", "singular-or-aggregate",
             "scheduler-context"),
        )


if __name__ == "__main__":
    unittest.main()
