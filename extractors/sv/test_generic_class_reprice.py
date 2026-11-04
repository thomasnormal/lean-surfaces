"""Shape checks for GenericClassDefSymbol repricing."""
import unittest

from generic_class_reprice import generic_features


class GenericClassReprice(unittest.TestCase):
    def test_parameterized_features_overlap(self):
        source = ("virtual class C #(parameter type T = logic, parameter int N = 2); "
                  "typedef struct packed { logic [N-1:0] x; } item_t; "
                  "localparam int W = N; static function int f; endfunction endclass")
        self.assertEqual(generic_features(source),
                         ("virtual", "value-parameters", "type-parameters",
                          "typedef-members", "local-parameters",
                          "static-methods", "packed-aggregate-types"))

    def test_plain_generic_class_is_empty(self):
        self.assertEqual(generic_features("class C #(parameter int N = 1); endclass"),
                         ("value-parameters",))


if __name__ == "__main__":
    unittest.main()
