"""Shape checks for the CovergroupType:CovergroupType repricer."""
import unittest

from covergroup_reprice import covergroup_features


class CovergroupReprice(unittest.TestCase):
    def test_sampling_bins_and_cross(self):
        source = ("covergroup cg @(posedge clk); coverpoint x { bins a = {0}; } "
                  "cross x, y; endgroup")
        self.assertEqual(covergroup_features(source),
                         ("clocked", "coverpoints", "crosses", "bins"))

    def test_options_and_sample_method(self):
        source = ("covergroup cg with function sample(output int x); "
                  "option.weight = 2; coverpoint x with (item > 0); endgroup")
        self.assertEqual(covergroup_features(source),
                         ("coverpoints", "options", "sample-method",
                          "with-expression", "sample-argument-directions"))

    def test_plain_covergroup_is_empty(self):
        self.assertEqual(covergroup_features("covergroup cg; endgroup"), ())


if __name__ == "__main__":
    unittest.main()
