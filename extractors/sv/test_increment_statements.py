"""Standalone integral increment/decrement statements lower to blocking writes."""

import unittest

from test_bit_queries import lower, nodes


class IncrementStatements(unittest.TestCase):
    def test_all_prefix_and_postfix_forms_are_admitted(self):
        design = lower(
            "module top; logic [3:0] value; initial begin "
            "value = 4'd1; value++; ++value; value--; --value; end endmodule"
        )
        statements = [node for node in nodes(design)
                      if node.get("kind") == "BlockingAssign"]
        self.assertEqual([statement["target"]["name"] for statement in statements],
                         ["value", "value", "value", "value", "value"])
        self.assertEqual([statement["value"].get("op") for statement in statements],
                         [None, "+", "+", "-", "-"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_selected_increment_stays_loud(self):
        design = lower(
            "module top; logic [3:0] value; initial value[0]++; endmodule"
        )
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:UnaryExpression-target"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
