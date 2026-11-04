"""IEEE 1800 unary reduction admission for the legacy M0 envelope."""

import unittest

from test_bit_queries import lower, nodes


class UnaryReductions(unittest.TestCase):
    def test_all_reductions_are_one_bit_nodes(self):
        design = lower(
            "module r(input logic [3:0] a, output logic o, p); "
            "assign o = |a; assign p = ~^a; endmodule"
        )
        reductions = [node for node in nodes(design) if node.get("kind") == "Reduce"]
        self.assertEqual([node["op"] for node in reductions], ["|", "~^"])
        self.assertTrue(all(node["width"] == 1 for node in reductions))
        self.assertTrue(all(node["operand"]["width"] == 4 for node in reductions))

    def test_reduction_unknowns_are_preserved_in_the_envelope(self):
        design = lower(
            "module r(input logic [3:0] a, output logic o); "
            "assign o = &a; endmodule"
        )
        reduction = next(node for node in nodes(design) if node.get("kind") == "Reduce")
        self.assertEqual(reduction["op"], "&")
        self.assertEqual(reduction["operand"]["name"], "a")


if __name__ == "__main__":
    unittest.main()
