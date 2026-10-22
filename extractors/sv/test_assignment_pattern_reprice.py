"""Shape checks for assignment-pattern repricing."""
import unittest

from assignment_pattern_reprice import pattern_features


class AssignmentPatternReprice(unittest.TestCase):
    def test_typed_packed_cast_pattern(self):
        labels = pattern_features("typedef logic [1:0][3:0] T; "
                                  "shortint'({T'{1,2}, T'{3,4}})")
        self.assertIn("typed-packed-pattern", labels)
        self.assertIn("casted-pattern-expression", labels)

    def test_nested_pattern(self):
        self.assertIn("nested-pattern-in-concatenation",
                      pattern_features("{T'{1,2}, T'{3,4}}"))

    def test_fallback(self):
        self.assertEqual(pattern_features("'{1, 2}"),
                         ("other-integral-pattern-shape",))


if __name__ == "__main__":
    unittest.main()
