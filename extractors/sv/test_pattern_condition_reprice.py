"""Shape checks for pattern-condition repricing."""
import unittest

from pattern_condition_reprice import pattern_features


class PatternConditionReprice(unittest.TestCase):
    def test_constant_pattern(self):
        self.assertEqual(pattern_features("if (v matches 42) result = 1;"),
                         ("constant-integral-pattern",))

    def test_identifier_binding(self):
        self.assertEqual(pattern_features("if (v matches .bound) result=bound;"),
                         ("identifier-binding-pattern",))

    def test_struct_wildcard(self):
        self.assertEqual(
            pattern_features("if (p matches '{x: .xv, y: .*}) result=xv;"),
            ("struct-wildcard-pattern", "struct-member-pattern"))


if __name__ == "__main__":
    unittest.main()
