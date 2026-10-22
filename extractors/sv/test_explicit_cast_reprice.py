"""Shape checks for explicit cast repricing."""
import unittest

from explicit_cast_reprice import cast_features


class ExplicitCastReprice(unittest.TestCase):
    def test_real_to_integral_rounding(self):
        self.assertEqual(cast_features("int'(2.7)"),
                         ("real-to-integral-rounding",))

    def test_negative_real_to_integral_rounding(self):
        self.assertEqual(cast_features("int'(-2.7)"),
                         ("real-to-integral-rounding",))

    def test_typed_assignment_pattern(self):
        self.assertEqual(cast_features("shortint'(T'{1, 2})"),
                         ("typed-assignment-pattern",))


if __name__ == "__main__":
    unittest.main()
