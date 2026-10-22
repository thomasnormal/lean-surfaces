"""Shape checks for sequence repricing."""
import unittest

from sequence_reprice import sequence_features


class SequenceReprice(unittest.TestCase):
    def test_multiclock_and_temporal_shapes(self):
        self.assertEqual(
            sequence_features("sequence s; @(posedge a) x ##2 "
                              "@(posedge b) y; endsequence"),
            ("multiclock", "temporal-concatenation"))
        self.assertEqual(
            sequence_features("sequence s; @(posedge c) a intersect "
                              "@(posedge d) b; endsequence"),
            ("multiclock", "intersect"))

    def test_scope_and_endpoint_shapes(self):
        self.assertEqual(
            sequence_features("sequence s(lv); int local_v; a ##1 b; "
                              "endsequence : s"),
            ("local-variable", "formal-argument", "temporal-concatenation",
             "end-label"))
        self.assertEqual(
            sequence_features("sequence s; a ##1 other.matched; endsequence"),
            ("temporal-concatenation", "matched-endpoint"))

    def test_event_and_sampled_forms(self):
        self.assertEqual(
            sequence_features("sequence s(local event e); @(e) $rose(a); "
                              "endsequence"),
            ("local-variable", "formal-argument", "event-local-diagnostic",
             "sampled-value"))
        self.assertEqual(
            sequence_features("sequence s(sequence q); q; endsequence"),
            ("formal-argument", "sequence-typed-formal"))


if __name__ == "__main__":
    unittest.main()
