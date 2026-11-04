"""Shape checks for ProceduralBlockSymbol:Final repricing."""
import unittest

from final_reprice import final_features


class FinalReprice(unittest.TestCase):
    def test_shutdown_features_overlap(self):
        source = "final begin x = 1; $display(\"PASS\"); $finish; end"
        self.assertEqual(final_features(source),
                         ("block-body", "display", "finish", "assignment"))

    def test_invalid_wait_delay_and_assertion(self):
        source = "final begin #5; wait (x); assert (x) else $fatal; end"
        self.assertEqual(final_features(source),
                         ("block-body", "assertion", "delay", "wait"))

    def test_plain_final_is_empty(self):
        self.assertEqual(final_features("final;"), ())


if __name__ == "__main__":
    unittest.main()
