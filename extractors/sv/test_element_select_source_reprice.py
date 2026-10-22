"""Shape checks for ElementSelectExpression source-type repricing."""
import unittest

from element_select_source_reprice import element_features


class ElementSelectSourceReprice(unittest.TestCase):
    def test_scalar_and_packed_union_shapes(self):
        self.assertEqual(
            element_features("logic scalar; initial scalar[0] = 1;",
                             "scalar[0]"),
            ("scalar-source",))
        self.assertEqual(
            element_features("typedef union packed { bit [15:0] word; "
                             "bit [1:0][7:0] bytes; } U; U u; "
                             "initial u.bytes[1] = 0;",
                             "u.bytes[1]"),
            ("packed-union-member",))

    def test_out_of_bounds_state_shapes(self):
        self.assertEqual(
            element_features("bit [7:0] a[4]; initial a[10] = 0;", "a[10]"),
            ("unpacked-array-oob", "two-state-oob"))
        self.assertEqual(
            element_features("logic [7:0] a[4]; initial a[10] = 0;",
                             "a[10]"),
            ("unpacked-array-oob", "four-state-oob"))

    def test_enum_out_of_bounds_keeps_base_rule(self):
        self.assertEqual(
            element_features("typedef enum logic [1:0] { A, B } E; "
                             "E a[4]; initial a[10] = A;", "a[10]"),
            ("unpacked-array-oob", "enum-base-default"))


if __name__ == "__main__":
    unittest.main()
