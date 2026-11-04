"""Shape checks for event iff repricing."""
import unittest

from event_iff_reprice import iff_features


class EventIffReprice(unittest.TestCase):
    def test_always_ff_edge_iff(self):
        self.assertEqual(
            iff_features("always_ff @(posedge clk iff en) count <= count + 1;"),
            ("always_ff-iff", "edge-qualified-iff"))

    def test_level_event_iff(self):
        self.assertEqual(
            iff_features("@(a iff enable == 1) count++;"),
            ("procedural-event-iff", "level-qualified-iff"))

    def test_always_edge_iff(self):
        self.assertEqual(
            iff_features("always @(posedge clk iff en) count++;"),
            ("procedural-always-iff", "edge-qualified-iff"))


if __name__ == "__main__":
    unittest.main()
