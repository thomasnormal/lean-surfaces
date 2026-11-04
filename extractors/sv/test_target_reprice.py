"""Shape classifier checks for the assignment-target repricing instrument."""
import unittest

from target_reprice import target_shape


class TargetReprice(unittest.TestCase):
    def test_shapes(self):
        self.assertEqual(target_shape("arr = '{default: 1};"),
                         "keyed/default/replicated or unpacked-array pattern RHS")
        self.assertEqual(target_shape("arr[idx] <= 1;"),
                         "dynamic element target")
        self.assertEqual(target_shape("{a, b} = src;"),
                         "concatenated or streaming target")
        self.assertEqual(target_shape("s.inner.x = 1;"),
                         "member target (nested packed, union or unsupported member)")
        self.assertEqual(target_shape("bus[3:0] = x;"),
                         "packed or unpacked part-select target")
        self.assertEqual(target_shape("bus[2] = x;"),
                         "constant element/bit target in a continuous or unsupported shape")
        self.assertEqual(target_shape("dst = src;"),
                         "whole aggregate/array target")


if __name__ == "__main__":
    unittest.main()
