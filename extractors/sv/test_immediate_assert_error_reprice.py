"""Shape checks for the implicit immediate-assertion diagnostic instrument."""
import unittest

from immediate_assert_error_reprice import implicit_error_features


class ImmediateAssertErrorReprice(unittest.TestCase):
    def test_omitted_assert_failure(self):
        self.assertEqual(
            implicit_error_features("assert (0);", ""),
            ("implicit-error", "assert", "omitted-success-action",
             "false-condition", "diagnostic-bearing-kind"),
        )

    def test_named_assume_with_action_in_always(self):
        labels = implicit_error_features(
            "named: assume (1'b1) flag = 1;",
            "always_comb begin named: assume (1'b1) flag = 1; end",
        )
        self.assertIn("assume", labels)
        self.assertIn("named-assertion", labels)
        self.assertIn("explicit-success-action", labels)
        self.assertIn("true-condition", labels)
        self.assertIn("always-comb-context", labels)

    def test_block_action_is_not_dropped(self):
        labels = implicit_error_features(
            "assert (x) begin count++; end;", "")
        self.assertIn("explicit-success-action", labels)
        self.assertIn("block-context", labels)


if __name__ == "__main__":
    unittest.main()
