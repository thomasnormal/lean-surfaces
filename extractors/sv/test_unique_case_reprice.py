"""Shape checks for unique-case repricing."""
import unittest

from unique_case_reprice import unique_features


class UniqueCaseReprice(unittest.TestCase):
    def test_wildcard_inside_and_default(self):
        source = "unique casez (x) inside 1: y <= a; default: y <= b; endcase"
        self.assertEqual(unique_features(source),
                         ("casez", "inside", "default", "nonblocking"))

    def test_indexed_multi_label_and_nested_block(self):
        source = "unique case (state[idx]) 1, 2: begin y = a; end endcase"
        self.assertEqual(unique_features(source),
                         ("nested-block", "indexed-select", "multi-label"))

    def test_plain_unique_case_has_no_extra_shape(self):
        self.assertEqual(unique_features("unique case (x) 1: y = a; endcase"), ())


if __name__ == "__main__":
    unittest.main()
