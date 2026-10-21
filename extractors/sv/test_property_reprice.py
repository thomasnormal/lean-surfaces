"""Shape checks for the PropertySymbol:Property repricing instrument."""
import unittest

from property_reprice import property_features


class PropertyReprice(unittest.TestCase):
    def test_clocked_implication_and_sampled_function(self):
        source = "property p; @(posedge clk) a |-> $past(b); endproperty"
        self.assertEqual(property_features(source),
                         ("clocked", "implication", "sampled-function"))

    def test_declaration_features_overlap(self):
        source = ("property p(property q); local int lv = 0; "
                  "accept_on(lv) a; endproperty : p")
        self.assertEqual(property_features(source),
                         ("local-variables", "abort-or-disable",
                          "formal-property", "end-label"))

    def test_plain_property_is_empty(self):
        self.assertEqual(property_features("property p; a; endproperty"), ())


if __name__ == "__main__":
    unittest.main()
