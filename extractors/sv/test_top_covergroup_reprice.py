"""Shape checks for top-level CovergroupType repricing."""
import unittest

from top_covergroup_reprice import covergroup_features


class TopCovergroupReprice(unittest.TestCase):
    def test_clock_bins_and_extends(self):
        source = ("covergroup base @(posedge clk); coverpoint x { bins a = {0}; } "
                  "endgroup covergroup child extends base; endgroup")
        self.assertEqual(covergroup_features(source),
                         ("clocked", "coverpoints", "bins", "extends"))

    def test_plain_covergroup_is_empty(self):
        self.assertEqual(covergroup_features("covergroup cg; endgroup"), ())


if __name__ == "__main__":
    unittest.main()
