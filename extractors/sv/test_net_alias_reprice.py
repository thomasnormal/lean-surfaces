"""Shape checks for net-alias repricing."""
import unittest

from net_alias_reprice import alias_features


class NetAliasReprice(unittest.TestCase):
    def test_chain(self):
        self.assertEqual(alias_features("alias a = b = c;"), ("chain",))

    def test_indexed_select(self):
        self.assertEqual(alias_features("alias bus[7:4] = high;"),
                         ("indexed-select",))

    def test_plain_pair(self):
        self.assertEqual(alias_features("alias a = b;"), ())


if __name__ == "__main__":
    unittest.main()
