"""Admission checks for plain user-defined four-state nettypes."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def lower(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class UserNettype(unittest.TestCase):
    def test_plain_user_nettypes_lower_to_high_impedance_cells(self):
        module = lower(
            "module top; nettype logic scalar_net; "
            "nettype logic [3:0] vector_net; scalar_net scalar; "
            "vector_net bus; endmodule")["modules"][0]
        self.assertEqual(
            [(decl["name"], decl["init"]["bits"])
             for decl in module["decls"]],
            [("scalar", "z"), ("bus", "zzzz")])
        self.assertFalse(module.get("others"))
        self.assertFalse(any(node.get("sv_kind") == "NetSymbol:UserDefined"
                             for node in nodes(module)))

    def test_continuous_driver_stays_loud(self):
        module = lower(
            "module top; nettype logic scalar_net; scalar_net n; "
            "assign n = 1'b1; endmodule")["modules"][0]
        self.assertTrue(any(node.get("sv_kind") == "NetSymbol:UserDefined"
                            for node in nodes(module)))


if __name__ == "__main__":
    unittest.main()
