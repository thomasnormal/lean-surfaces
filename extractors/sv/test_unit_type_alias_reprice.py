"""Shape checks for compilation-unit typedef repricing."""
import unittest

from unit_type_alias_reprice import unit_alias_features


class UnitTypeAliasReprice(unittest.TestCase):
    def test_packed_and_dynamic_shapes(self):
        self.assertEqual(
            unit_alias_features("typedef union packed { bit [15:0] a; "
                                "bit [7:0] b; } U;"),
            ("packed-union-width",))
        self.assertEqual(
            unit_alias_features("typedef union tagged { string s; int i; } U;"),
            ("nonintegral-packed-member", "tagged-union-dynamic-member"))
        self.assertEqual(
            unit_alias_features("typedef union { string s; int i; } U;"),
            ("nonintegral-packed-member", "untagged-union-dynamic-member"))

    def test_declaration_diagnostics(self):
        self.assertEqual(
            unit_alias_features("typedef struct [7:0] { bit a; } S;"),
            ("packed-dimension-qualifier",))
        self.assertEqual(
            unit_alias_features("typedef struct signed { int a; } S;"),
            ("unpacked-struct-signing",))
        self.assertEqual(
            unit_alias_features("typedef union { void v; int i; } U;"),
            ("void-in-untagged-union",))

    def test_tagged_and_member_rules(self):
        self.assertEqual(
            unit_alias_features("typedef union tagged packed { void V; "
                                "string S; } U;"),
            ("nonintegral-packed-member", "packed-tagged-union",
             "tagged-union-dynamic-member"))
        self.assertEqual(
            unit_alias_features("typedef struct { union { int i; real r; } "
                                "u = '{0}; int x; } S;"),
            ("nonintegral-packed-member", "union-member-default"))


if __name__ == "__main__":
    unittest.main()
