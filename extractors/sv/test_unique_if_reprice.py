"""Shape checks for unique-if repricing."""
import unittest

from unique_if_reprice import unique_if_features


class UniqueIfReprice(unittest.TestCase):
    def test_overlap_and_first_match(self):
        labels = unique_if_features(
            "unique if (a > 0) result = 1; else if (a > 1) result = 2;",
            "initial begin end",
            "12.4.2--unique-if-violation-report-deferred-to-observed-region.sv",
        )
        self.assertIn("unique-if", labels)
        self.assertIn("first-match", labels)
        self.assertIn("condition-chain", labels)
        self.assertIn("multiple-true", labels)
        self.assertIn("observed-region-report", labels)

    def test_no_match_and_explicit_else(self):
        labels = unique_if_features(
            "unique if (a == 1) result = 1; else if (a == 2) result = 2;",
            "initial begin end",
        )
        self.assertIn("no-match", labels)

        labels = unique_if_features(
            "unique if (a == 1) result = 1; else if (a == 2) result = 2; "
            "else result = 99;",
            "initial begin end",
        )
        self.assertNotIn("no-match", labels)
        self.assertIn("explicit-else", labels)

    def test_nested_context_and_flushes(self):
        labels = unique_if_features(
            "unique if (a) z = b; else if (not_a) z = c;",
            "always_comb begin\n"
            "  unique if (a) z = b; else if (not_a) z = c;\n"
            "  for (int j = 0; j < 2; j++) ;\nend",
            "12.4.2.1--unique-if-flush-on-event-control-resume.sv",
        )
        self.assertIn("always-comb-context", labels)
        self.assertIn("flush-on-event-resume", labels)
        self.assertIn("loop-context", labels)

        labels = unique_if_features(
            "unique if (a) z = b; else if (not_a) z = c;",
            "always_comb begin end",
            "12.4.2.1--unique-if-loop-all-violations-flushed-on-reschedule.sv",
        )
        self.assertIn("flush-on-reschedule", labels)

    def test_invalid_qualifier_after_else(self):
        labels = unique_if_features(
            "if (a) $display(\"0\"); else unique if (b) $display(\"1\");",
            "if (a) $display(\"0\"); else unique if (b) $display(\"1\");",
        )
        self.assertIn("invalid-after-else", labels)


if __name__ == "__main__":
    unittest.main()
