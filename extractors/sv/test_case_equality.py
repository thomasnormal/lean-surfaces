"""IEEE 1800-2023 §11.4.5 exact four-state case equality admission."""

import unittest

from test_bit_queries import lower, nodes


class CaseEquality(unittest.TestCase):
    def test_case_equality_operators_are_admitted(self):
        design = lower(
            "module top; logic clk; logic [1:0] value; logic eq, neq; "
            "always_ff @(posedge clk) begin "
            "eq = value === 2'b1x; neq = value !== 2'b1x; end endmodule"
        )
        binaries = [node for node in nodes(design) if node.get("kind") == "Binary"]
        self.assertEqual([node["op"] for node in binaries], ["===", "!=="])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_case_equality_keeps_one_bit_result_and_operand_width(self):
        design = lower(
            "module top; logic [3:0] left, right; logic result; "
            "initial result = left === right; endmodule"
        )
        binary = next(node for node in nodes(design) if node.get("kind") == "Binary")
        self.assertEqual(binary["width"], 1)
        self.assertEqual((binary["left"]["width"], binary["right"]["width"]), (4, 4))

    def test_invalid_source_keeps_case_equality_node_visible(self):
        design = lower(
            "module top; logic [1:0] value, eq; initial eq = value === 2'b1x; "
            "initial missing = 1; endmodule",
            require_valid=False,
        )
        self.assertIn("===", [node.get("op") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
