"""Shape checks for unique0-case repricing."""
import unittest

from unique0_case_reprice import unique0_features


class Unique0CaseReprice(unittest.TestCase):
    def test_no_match_is_allowed(self):
        labels = unique0_features(
            "unique0 case (a) 1: y = 1; 2: y = 2; endcase",
            "initial begin end",
            "12.5.3--unique0-case-no-violation-no-match.sv",
        )
        self.assertIn("unique0-case", labels)
        self.assertIn("first-match", labels)
        self.assertIn("no-match-allowed", labels)
        self.assertIn("no-default", labels)
        self.assertIn("no-match-no-violation", labels)

    def test_overlap_and_wildcard(self):
        labels = unique0_features(
            "unique0 casex (a) 2'b1?: y = 1; 2'b?1: y = 2; endcase",
            "initial begin end",
            "12.5.3--unique0-case-violation-when-multiple-match.sv",
        )
        self.assertIn("casex", labels)
        self.assertIn("wildcard-label", labels)
        self.assertIn("multiple-match-violation", labels)

    def test_inside_and_default(self):
        labels = unique0_features(
            "unique0 case (v) inside [1:5]: y = 1; default: y = 0; endcase",
            "initial begin end",
        )
        self.assertIn("inside", labels)
        self.assertIn("default", labels)
        self.assertNotIn("no-default", labels)


if __name__ == "__main__":
    unittest.main()
