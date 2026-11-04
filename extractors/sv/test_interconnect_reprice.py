"""Shape checks for the interconnect repricing instrument."""
import unittest

from interconnect_reprice import interconnect_features


class InterconnectReprice(unittest.TestCase):
    def test_initializer_is_a_diagnostic_shape(self):
        self.assertEqual(
            interconnect_features(
                "interconnect #1 ic = 1'b0;",
                ":type: compile_error\n",
            ),
            ("interconnect-declaration", "declaration-assignment",
             "delay-specification", "compile-error-shape"),
        )

    def test_array_dimensions_and_per_bit_resolution(self):
        self.assertEqual(
            interconnect_features(
                "interconnect [3:0] w3 [1:0];",
                "different bits in the array resolve to different net types",
            ),
            ("interconnect-declaration", "packed-dimension",
             "unpacked-dimension", "per-bit-net-resolution"),
        )

    def test_strength_and_multiple_delay_are_not_lowered(self):
        self.assertEqual(
            interconnect_features(
                "interconnect #(1,2,3) w1;",
                ":type: compile_error\n",
            ),
            ("interconnect-declaration", "delay-specification",
             "multiple-delay-values", "compile-error-shape"),
        )
        self.assertIn(
            "drive-or-charge-strength",
            interconnect_features(
                "interconnect (large) w2;",
                ":type: compile_error\n",
            ),
        )


if __name__ == "__main__":
    unittest.main()
