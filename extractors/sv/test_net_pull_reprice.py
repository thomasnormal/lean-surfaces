"""Shape checks for the implicit pull-net repricing instrument."""
import unittest

from net_pull_reprice import tri0_features


class NetPullReprice(unittest.TestCase):
    def test_undriven_tri0_is_pull_zero(self):
        self.assertEqual(
            tri0_features("module top; tri0 n; initial if (n === 1'b0); endmodule"),
            ("implicit-pull0", "undriven-observation"),
        )

    def test_strength_and_strong_driver(self):
        self.assertEqual(
            tri0_features(
                "tri0 n; assign (weak0, weak1) n = 1'b1; "
                "assign strong_n = 1'b1;",
            ),
            ("implicit-pull0", "continuous-driver", "explicit-strength",
             "strong-driver-overrides-pull"),
        )

    def test_unknown_driver_is_not_collapsed_to_pull_zero(self):
        self.assertEqual(
            tri0_features("tri0 n; assign n = 1'bx;"),
            ("implicit-pull0", "continuous-driver", "four-state-x-driver"),
        )


if __name__ == "__main__":
    unittest.main()
