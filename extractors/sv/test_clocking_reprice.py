"""Shape checks for clocking-block repricing."""
import unittest

from clocking_reprice import clocking_features


class ClockingReprice(unittest.TestCase):
    def test_default_input_skew(self):
        source = "default clocking cb @(posedge clk); default input #1; input a; endclocking"
        self.assertEqual(clocking_features(source),
                         ("default", "input-clockvar", "skew"))

    def test_global_output_and_label(self):
        source = "global clocking gc @(posedge clk); output q; endclocking : gc"
        self.assertEqual(clocking_features(source),
                         ("global", "output-clockvar", "end-label"))

    def test_nested_event_and_sequence(self):
        source = "clocking cb @(posedge clk); sequence s; @(posedge clk2) a; endsequence endclocking"
        self.assertEqual(clocking_features(source),
                         ("sequence-or-property", "nested-event"))


if __name__ == "__main__":
    unittest.main()
