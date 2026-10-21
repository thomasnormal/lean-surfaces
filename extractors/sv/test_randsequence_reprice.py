"""Shape checks for the randsequence repricing instrument."""
import unittest

from randsequence_reprice import production_features


class RandSequenceReprice(unittest.TestCase):
    def test_production_features(self):
        source = "randsequence(main) main: a := 2 | repeat (3) b; a: { if (x) y = 1; }; endsequence"
        self.assertEqual(production_features(source),
                         ("alternatives", "conditional", "repeat",
                          "weighted", "action-block"))

    def test_feature_rows_overlap(self):
        self.assertEqual(production_features("randsequence(main) main: left | right;"),
                         ("alternatives",))

    def test_unknown_span_stays_empty(self):
        self.assertEqual(production_features(""), ())


if __name__ == "__main__":
    unittest.main()
