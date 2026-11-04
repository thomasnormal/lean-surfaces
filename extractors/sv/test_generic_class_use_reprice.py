"""Shape checks for GenericClassDefSymbol:GenericClassDef repricing."""
import unittest

from generic_class_use_reprice import generic_use_features


class GenericClassUseReprice(unittest.TestCase):
    def test_member_parameter_features(self):
        source = "class Packet #(parameter int P = 1); parameter int Q = 2; localparam int R = 3; endclass"
        self.assertEqual(generic_use_features(source),
                         ("value-parameter-member", "local-parameter-member"))

    def test_class_scope_resolution(self):
        self.assertEqual(generic_use_features("class P #(type C); C::T x; endclass"),
                         ("type-parameter-member", "class-scope-resolution"))


if __name__ == "__main__":
    unittest.main()
