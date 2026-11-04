"""Shape checks for the concurrent-assertion repricing instrument."""
import unittest

from concurrent_assert_reprice import assertion_shape


class ConcurrentAssertReprice(unittest.TestCase):
    def test_property_flavors(self):
        self.assertEqual(assertion_shape("a: assert property (@(posedge c) p);"),
                         "assert property")
        self.assertEqual(assertion_shape("cover property (@(posedge c) p);"),
                         "cover property")
        self.assertEqual(assertion_shape("assume property (@(posedge c) p);"),
                         "assume property")

    def test_sequence_and_expect(self):
        self.assertEqual(assertion_shape("cover sequence (@(posedge c) p);"),
                         "cover sequence")
        self.assertEqual(assertion_shape("expect (@(posedge c) p);"), "expect")

    def test_restrict_and_unknown(self):
        self.assertEqual(assertion_shape("restrict property (@(posedge c) p);"),
                         "restrict property")
        self.assertEqual(assertion_shape("?"), "other concurrent assertion")


if __name__ == "__main__":
    unittest.main()
