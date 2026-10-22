"""Shape checks for the always_latch repricing instrument."""
import unittest

from always_latch_reprice import latch_features


class AlwaysLatchReprice(unittest.TestCase):
    def test_inferred_latch_features(self):
        self.assertEqual(
            latch_features("always_latch if (en) q <= d;"),
            ("inferred-sensitivity", "nonblocking-assignment"))
        self.assertEqual(
            latch_features("always_latch begin if (en) begin if (load) "
                           "q = d; end end end"),
            ("inferred-sensitivity", "nested-enables"))

    def test_invalid_and_protected_shapes(self):
        self.assertEqual(
            latch_features("always_latch begin @(posedge clk) if (en) "
                           "q = d; end"),
            ("timing-control-diagnostic",))
        self.assertEqual(
            latch_features("`pragma protect begin\nalways_latch if (en) "
                           "q = d;\n`pragma protect end"),
            ("inferred-sensitivity", "protected-region"))

    def test_other_process_controls_do_not_hide_latch_sensitivity(self):
        self.assertEqual(
            latch_features("always_latch if (en) q = d; "
                           "always_ff @(posedge clk) q <= d;"),
            ("inferred-sensitivity", "nonblocking-assignment",
             "mixed-or-timed-processes"))


if __name__ == "__main__":
    unittest.main()
