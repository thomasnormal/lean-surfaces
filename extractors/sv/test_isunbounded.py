"""Pure bounded-parameter ``$isunbounded`` queries."""

import unittest

from test_bit_queries import lower, nodes


class IsUnbounded(unittest.TestCase):
    def test_bounded_parameter_is_zero(self):
        design = lower(
            'module top #(parameter int p = 5); '
            'initial if (!$isunbounded(p)) $display("PASS"); endmodule')
        values = [node for node in nodes(design)
                  if node.get("isunbounded_bounded")]
        self.assertEqual([(node["width"], node["bits"]) for node in values],
                         [(1, "0")])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_literal_is_zero(self):
        design = lower(
            'module top; initial if (!$isunbounded(5)) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("isunbounded_bounded")
                            for node in nodes(design)))

    def test_variable_argument_stays_loud(self):
        design = lower(
            'module top; int p; initial $display("%0d", '
            '$isunbounded(p)); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
