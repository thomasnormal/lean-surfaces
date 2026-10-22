"""Shape checks for priority-case repricing."""
import unittest

from priority_case_reprice import priority_features


class PriorityCaseReprice(unittest.TestCase):
    def test_first_match_and_no_default_violation(self):
        labels = priority_features(
            "priority case (a) 1: y = 1; 2: y = 2; endcase",
            "initial begin end",
            "12.5.3--priority-case-no-match-violation.sv",
        )
        self.assertIn("priority-case", labels)
        self.assertIn("first-match", labels)
        self.assertIn("no-default", labels)
        self.assertIn("no-match-violation", labels)

    def test_casez_inside_and_wildcard(self):
        labels = priority_features(
            "priority casez (a) 3'b0??: y = 1; default: y = 0; endcase",
            "initial begin end",
        )
        self.assertIn("casez", labels)
        self.assertIn("wildcard-label", labels)
        self.assertIn("default", labels)
        self.assertNotIn("no-default", labels)

        labels = priority_features(
            "priority case (v) inside [1:5]: y = 1; default: y = 0; endcase",
            "initial begin end",
        )
        self.assertIn("inside", labels)

    def test_process_and_selection_shapes(self):
        labels = priority_features(
            "priority case (sel[0]) 1, 2: y <= x; endcase",
            "always_comb begin end",
        )
        self.assertIn("indexed-select", labels)
        self.assertIn("multi-label", labels)
        self.assertIn("nonblocking", labels)
        self.assertIn("always-comb-context", labels)


if __name__ == "__main__":
    unittest.main()
