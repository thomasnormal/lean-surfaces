"""Shape checks for level-sensitive wait repricing."""
import unittest

from wait_reprice import wait_features


class WaitReprice(unittest.TestCase):
    def test_conjunction_and_case_equality(self):
        self.assertEqual(
            wait_features("wait (a && b === 1);"),
            ("level-sensitive", "conjunction", "case-equality"),
        )

    def test_negated_trailing_delay(self):
        self.assertEqual(
            wait_features("wait (!enable) #10 a = b;"),
            ("level-sensitive", "negated-condition", "trailing-delay"),
        )

    def test_event_triggered(self):
        self.assertEqual(
            wait_features("wait (done.triggered);"),
            ("level-sensitive", "event-triggered"),
        )

    def test_contextual_rechecks(self):
        self.assertEqual(
            wait_features("wait (ready);", "// already true at time 0\n",
                          "chapter-9/wait-level-sensitive-v3.sv"),
            ("level-sensitive", "already-true-or-no-block"),
        )


if __name__ == "__main__":
    unittest.main()
