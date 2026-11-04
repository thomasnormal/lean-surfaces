"""Shape checks for invalid continuous-assignment repricing."""
import unittest

from continuous_invalid_reprice import invalid_assign_features


class InvalidContinuousReprice(unittest.TestCase):
    def test_default_nettype_none(self):
        self.assertEqual(
            invalid_assign_features("`default_nettype none\nassign o = x;"),
            ("default-nettype-none-implicit-net",))

    def test_invalid_strength_value(self):
        self.assertEqual(
            invalid_assign_features("`default_nettype supply0\nassign o = x;"),
            ("invalid-default-nettype-value",))

    def test_undefineall_preserves_directive(self):
        self.assertEqual(
            invalid_assign_features("`default_nettype none\n`undefineall\n"
                                    "assign x = y;"),
            ("default-nettype-none-implicit-net",
             "undefineall-preserves-default-nettype"))


if __name__ == "__main__":
    unittest.main()
