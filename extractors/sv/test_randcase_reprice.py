"""Shape checks for randcase repricing."""
import unittest

from randcase_reprice import randcase_features


class RandCaseReprice(unittest.TestCase):
    def test_zero_weight_and_indexed_increment(self):
        source = "randcase 0: counts[i]++; 1: counts[i] = 2; endcase"
        self.assertEqual(randcase_features(source),
                         ("zero-weight", "indexed-target", "increment"))

    def test_expression_weight_and_block(self):
        source = "randcase w + 1: begin value = 1; end endcase"
        self.assertEqual(randcase_features(source),
                         ("branch-block", "weight-expression"))

    def test_all_zero_weights(self):
        self.assertEqual(randcase_features("randcase 0: a = 1; 0: a = 2; endcase"),
                         ("zero-weight", "all-zero-weight"))


if __name__ == "__main__":
    unittest.main()
