"""Shape checks for residual module typedef repricing."""
import unittest

from type_alias_reprice import type_alias_features


class TypeAliasReprice(unittest.TestCase):
    def test_struct_bits(self):
        self.assertEqual(
            type_alias_features("typedef struct { logic a; bit [7:0] b; } T; "
                               "initial $display($bits(T));"),
            ("bits-query", "aggregate-typedef"))

    def test_enum_diagnostics(self):
        self.assertEqual(
            type_alias_features("typedef enum {red, green} A; "
                               "typedef enum {red, blue} B;"),
            ("enum-typedef", "enum-member-redefinition"))
        self.assertEqual(
            type_alias_features("typedef enum {req[0]} E;"),
            ("enum-typedef", "nonpositive-enum-range"))

    def test_nonconstant_member(self):
        self.assertEqual(
            type_alias_features("int dyn_val = 5; typedef struct { "
                               "int addr = dyn_val; int crc; } packet;"),
            ("aggregate-typedef", "nonconstant-member-initializer"))


if __name__ == "__main__":
    unittest.main()
