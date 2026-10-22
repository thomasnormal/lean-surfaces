"""Shape checks for XNOR repricing."""
import unittest

from xnor_reprice import xnor_features


class XnorReprice(unittest.TestCase):
    def test_tilde_caret_variables(self):
        self.assertEqual(xnor_features("a ~^ b"),
                         ("tilde-caret-spelling", "variable-operands"))

    def test_caret_tilde_variables(self):
        self.assertEqual(xnor_features("a ^~ b"),
                         ("caret-tilde-spelling", "variable-operands"))

    def test_literal_operands(self):
        self.assertEqual(xnor_features("1'b0 ~^ 1'b1"),
                         ("tilde-caret-spelling", "literal-operands"))


if __name__ == "__main__":
    unittest.main()
