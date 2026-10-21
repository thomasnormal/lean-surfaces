"""Shape checks for nonblocking intra-assignment repricing."""
import unittest

from intra_nba_reprice import control_shape


class IntraNbaReprice(unittest.TestCase):
    def test_delay_and_zero_delay(self):
        self.assertEqual(control_shape("q <= #3 value"), "nonblocking delay")
        self.assertEqual(control_shape("q <= #0 value"), "nonblocking #0")

    def test_event_and_repeat(self):
        self.assertEqual(control_shape("q <= @(posedge clk) value"),
                         "nonblocking event")
        self.assertEqual(control_shape("q <= repeat(2) @(posedge clk) value"),
                         "nonblocking repeat/context")

    def test_missing_span_stays_contextual(self):
        self.assertEqual(control_shape(""), "nonblocking repeat/context")


if __name__ == "__main__":
    unittest.main()
