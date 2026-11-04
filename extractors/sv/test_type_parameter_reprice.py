"""Shape checks for TypeParameterSymbol:TypeParameter repricing."""
import unittest

from type_parameter_reprice import type_parameter_features


class TypeParameterReprice(unittest.TestCase):
    def test_type_operator(self):
        self.assertEqual(type_parameter_features("sample_expr_t = type(sample + 1);"),
                         ("type-operator",))

    def test_typed_default(self):
        self.assertEqual(type_parameter_features("T = shortint"),
                         ("typed-default",))

    def test_empty_span(self):
        self.assertEqual(type_parameter_features(""), ("empty-span",))


if __name__ == "__main__":
    unittest.main()
