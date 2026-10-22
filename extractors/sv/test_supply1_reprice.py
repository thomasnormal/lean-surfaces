"""Shape checks for NetSymbol:Supply1 repricing."""
import unittest

from supply1_reprice import supply1_features


class Supply1Reprice(unittest.TestCase):
    def test_supply_strength_and_logic_one(self):
        self.assertEqual(
            supply1_features("supply1 vcc;", "vcc"),
            ("supply-strength-driver", "logic-one-source"))

    def test_continuous_strength_context(self):
        self.assertEqual(
            supply1_features("wire w; assign (pull1,pull0) w=en; supply1 pwr;",
                             "pwr"),
            ("supply-strength-driver", "continuous-strength-context",
             "logic-one-source"))

    def test_other_name_keeps_strength(self):
        self.assertEqual(
            supply1_features("supply1 rail;", "rail"),
            ("supply-strength-driver",))


if __name__ == "__main__":
    unittest.main()
