"""Shape checks for event-list repricing."""
import unittest

from event_list_reprice import event_list_features


class EventListReprice(unittest.TestCase):
    def test_edge_or_and_iff(self):
        source = "@(posedge a iff ena or negedge b iff enb) count++;"
        self.assertEqual(event_list_features(source),
                         ("or-list", "edge-event", "iff-filter"))

    def test_comma_and_parentheses(self):
        self.assertEqual(event_list_features("@((a or b)) count++;"),
                         ("or-list", "parenthesized-list"))
        self.assertEqual(event_list_features("@(posedge a, posedge b) count++;"),
                         ("comma-list", "edge-event"))

    def test_three_event_list(self):
        self.assertEqual(event_list_features("@(a or b, c) count++;"),
                         ("or-list", "comma-list", "three-or-more-events"))


if __name__ == "__main__":
    unittest.main()
