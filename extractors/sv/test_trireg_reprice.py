"""Shape checks for the trireg repricing instrument."""
import unittest

from trireg_reprice import trireg_features


class TriregReprice(unittest.TestCase):
    def test_charge_strength_and_decay_vector(self):
        self.assertEqual(
            trireg_features(
                "trireg (small) signed [3:0] #(0,0,10) cap;",
                "trireg (small) signed [3:0] #(0,0,10) cap;",
            ),
            ("charge-strength", "charge-decay-delay", "packed-vector"),
        )

    def test_release_shape(self):
        self.assertEqual(
            trireg_features(
                "trireg t;",
                "trireg t; assign t = en ? 1'b1 : 1'bz; "
                "// capacitive state retains its charge",
            ),
            ("driver-release",),
        )

    def test_network_shape(self):
        self.assertEqual(
            trireg_features(
                "trireg_la;",
                "trireg (large) trireg_la; "
                "trireg (small) trireg_sm;",
            ),
            ("capacitive-network",),
        )


if __name__ == "__main__":
    unittest.main()
