"""Shape checks for VariableSymbol:range repricing."""
import unittest

from variable_range_reprice import range_features


class VariableRangeReprice(unittest.TestCase):
    def test_direct_multidimensional_packed_range(self):
        self.assertEqual(
            range_features("logic [3:0][7:0] parray;", "parray"),
            ("multidimensional-packed-range",))

    def test_packed_struct_array_range(self):
        self.assertEqual(
            range_features("typedef struct packed { logic [3:0] bits; } T; "
                           "T [1:0][3:0] pv;", "pv"),
            ("packed-struct-array-range",))

    def test_other_direct_range_shape(self):
        self.assertEqual(
            range_features("bit [3:0][1:0] md;", "md"),
            ("multidimensional-packed-range",))


if __name__ == "__main__":
    unittest.main()
