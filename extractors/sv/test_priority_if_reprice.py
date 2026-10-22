"""Shape checks for priority-if repricing."""
import unittest

from priority_if_reprice import priority_if_features


class PriorityIfReprice(unittest.TestCase):
    def test_first_order_and_overlap(self):
        labels = priority_if_features(
            "priority if (a > 0) y = 1; else if (a > 1) y = 2; else y = 3;",
            "initial begin end",
            "12.4.2--priority-if-first-true-selected.sv",
        )
        self.assertIn("priority-if", labels)
        self.assertIn("first-match", labels)
        self.assertIn("listed-order", labels)
        self.assertIn("condition-chain", labels)
        self.assertIn("multiple-true", labels)
        self.assertIn("explicit-else", labels)

    def test_no_match_and_invalid_placement(self):
        labels = priority_if_features(
            "priority if (a == 1) y = 1; else if (a == 2) y = 2;",
            "initial begin end",
            "12.4.2--priority-if-no-match-no-else-is-violation.sv",
        )
        self.assertIn("no-match-path", labels)
        self.assertIn("no-match-violation", labels)

        labels = priority_if_features(
            "if (a) y = 0; else priority if (b) y = 1;",
            "if (a) y = 0; else priority if (b) y = 1;",
            "12.4.2--priority-keyword-after-else-if-illegal.sv",
        )
        self.assertIn("invalid-after-else", labels)

    def test_index_and_always_comb(self):
        labels = priority_if_features(
            "priority if (a[0]) y = 1; else y = 0;",
            "always_comb begin end",
        )
        self.assertIn("indexed-select", labels)
        self.assertIn("always-comb-context", labels)
        self.assertIn("explicit-else", labels)


if __name__ == "__main__":
    unittest.main()
