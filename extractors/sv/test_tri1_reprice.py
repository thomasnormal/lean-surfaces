"""Shape checks for the implicit pull-up repricing instrument."""
import unittest

from tri1_reprice import tri1_features


class Tri1Reprice(unittest.TestCase):
    def test_undriven_tri1_is_pull_one(self):
        self.assertEqual(
            tri1_features("module top; tri1 n; initial if (n === 1'b1); endmodule"),
            ("implicit-pull1", "undriven-observation"),
        )

    def test_strong_driver_overrides_pullup(self):
        self.assertEqual(
            tri1_features("tri1 n; assign n = 1'b0;"),
            ("implicit-pull1", "continuous-driver",
             "strong-driver-overrides-pull"),
        )

    def test_release_and_unknown_driver(self):
        self.assertEqual(
            tri1_features(
                "tri1 n; logic drv; assign n = drv ? 1'b0 : 1'bz; "
                "assign other = 1'bx;",
            ),
            ("implicit-pull1", "continuous-driver",
             "strong-driver-overrides-pull", "four-state-x-driver",
             "driver-release"),
        )


if __name__ == "__main__":
    unittest.main()
