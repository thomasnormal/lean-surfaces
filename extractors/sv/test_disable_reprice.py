"""Shape checks for disable-statement repricing."""
import unittest

from disable_reprice import disable_features


class DisableReprice(unittest.TestCase):
    def test_named_target(self):
        self.assertEqual(disable_features("disable search_loop;"),
                         ("named-target",))

    def test_statement_label(self):
        self.assertEqual(disable_features("done: disable inner;"),
                         ("statement-label",))

    def test_escaped_target(self):
        self.assertEqual(disable_features(r"disable \\kill-target ;"),
                         ("escaped-target",))


if __name__ == "__main__":
    unittest.main()
