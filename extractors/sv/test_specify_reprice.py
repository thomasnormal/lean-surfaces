"""Shape checks for specify-block repricing."""
import unittest

from specify_reprice import specify_features


class SpecifyReprice(unittest.TestCase):
    def test_path_features_overlap(self):
        source = "specify if (en) (posedge a => (y +: d)) = (2, 3); endspecify"
        self.assertEqual(specify_features(source),
                         ("module-path", "edge-sensitive", "conditional-path",
                          "polarity", "state-dependent", "tuple-delay"))

    def test_timing_check_features(self):
        source = "specify $width(posedge sig[0], 5, 0, notifier); endspecify"
        self.assertEqual(specify_features(source),
                         ("timing-check", "edge-sensitive", "notifier", "select"))

    def test_comments_do_not_create_shapes(self):
        source = "specify // $display (a => y)\n endspecify"
        self.assertEqual(specify_features(source), ())


if __name__ == "__main__":
    unittest.main()
