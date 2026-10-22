"""Shape checks for invalid static-local repricing."""
import unittest

from static_invalid_reprice import invalid_features


class InvalidStaticReprice(unittest.TestCase):
    def test_number_space(self):
        self.assertEqual(invalid_features("logic [7:0] a = 8'b1010 0101;"),
                         ("embedded-space-in-number",))

    def test_declaration_order(self):
        self.assertEqual(invalid_features("$display(\"x\"); int x;"),
                         ("declaration-after-statement",))

    def test_label_and_name(self):
        self.assertEqual(invalid_features("labelA: begin : blockB end"),
                         ("label-and-block-name",))


if __name__ == "__main__":
    unittest.main()
