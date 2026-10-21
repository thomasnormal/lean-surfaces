"""Shape checks for the fork/join repricing instrument."""
import unittest

from fork_join_reprice import join_flavor


class ForkJoinReprice(unittest.TestCase):
    def test_frontend_join_markers(self):
        self.assertEqual(join_flavor("BlockStatement:JoinAll"), "join")
        self.assertEqual(join_flavor("BlockStatement:JoinAny"), "join_any")
        self.assertEqual(join_flavor("BlockStatement:JoinNone"), "join_none")

    def test_source_fallback(self):
        self.assertEqual(join_flavor("Other", "fork a; join_none"), "join_none")
        self.assertEqual(join_flavor("Other", "fork a; join_any"), "join_any")

    def test_unknown_stays_loud(self):
        self.assertEqual(join_flavor("Other", "fork a; wait(a);"),
                         "other fork/join")


if __name__ == "__main__":
    unittest.main()
