"""Shape checks for VariableSymbol:type repricing."""
import unittest

from variable_type_reprice import variable_type_features


class VariableTypeReprice(unittest.TestCase):
    def test_multidimensional_packed_element_storage(self):
        self.assertEqual(
            variable_type_features(
                "logic [3:0][2:1] n [1:5][2:8];", "n[1:5][2:8]"),
            ("unpacked-array-storage", "multidimensional-unpacked",
             "packed-and-unpacked-type"))

    def test_single_unpacked_dimension(self):
        self.assertEqual(
            variable_type_features("logic [3:0][7:0] arr [5];", "arr [5]"),
            ("unpacked-array-storage", "packed-and-unpacked-type"))

    def test_invalid_struct_dimension(self):
        self.assertEqual(
            variable_type_features(
                "struct { logic [3:0] a; logic [3:0] b; } [1:0] bad;",
                "bad"),
            ("invalid-packed-dimension-on-aggregate",))


if __name__ == "__main__":
    unittest.main()
