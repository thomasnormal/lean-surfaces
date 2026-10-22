"""Shape checks for the resolved-tri repricing instrument."""
import unittest

from tri_reprice import tri_features


class TriReprice(unittest.TestCase):
    def test_single_driver(self):
        self.assertEqual(
            tri_features("tri t; logic d; assign t = d;"),
            ("resolved-tri", "continuous-driver"),
        )

    def test_wire_equivalence(self):
        self.assertEqual(
            tri_features("wire w; tri t; assign w = 1'b1; assign t = 1'b1;"),
            ("resolved-tri", "continuous-driver", "wire-equivalence"),
        )

    def test_invalid_spelling_and_floating_observation(self):
        self.assertEqual(
            tri_features("tri reg r; tri z_val; assert (z_val);"),
            ("resolved-tri", "undriven-observation", "invalid-tri-reg-spelling",
             "four-state-floating-observation"),
        )


if __name__ == "__main__":
    unittest.main()
