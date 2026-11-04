"""IEEE 1800-2023 §11.4.7 logical conjunction/disjunction admission."""

import unittest

from test_bit_queries import lower, nodes


class LogicalOperators(unittest.TestCase):
    def test_logical_operators_are_admitted(self):
        design = lower(
            "module top; logic clk; logic [1:0] value; logic both, either; "
            "always_ff @(posedge clk) begin "
            "both = value && 2'b01; either = value || 2'b00; end endmodule"
        )
        binaries = [node for node in nodes(design) if node.get("kind") == "Binary"]
        self.assertEqual([node["op"] for node in binaries], ["&&", "||"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_logical_results_are_one_bit(self):
        design = lower(
            "module top; logic [3:0] left, right; logic result; "
            "initial result = left && right; endmodule"
        )
        binary = next(node for node in nodes(design) if node.get("kind") == "Binary")
        self.assertEqual(binary["width"], 1)
        self.assertEqual((binary["left"]["width"], binary["right"]["width"]), (4, 4))


if __name__ == "__main__":
    unittest.main()
