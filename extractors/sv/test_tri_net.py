"""Admission checks for un-driven resolved ``tri`` nets."""

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


class TriNet(unittest.TestCase):
    def test_un_driven_tri_has_high_impedance_initializer(self):
        module = lower("module top; tri bus; endmodule")["modules"][0]
        self.assertEqual(module["decls"][0]["init"]["bits"], "z")
        self.assertFalse(any(node.get("sv_kind") == "NetSymbol:Tri"
                             for node in nodes(module)))

    def test_un_driven_vector_tri_repeats_high_impedance(self):
        module = lower("module top; tri [3:0] bus; endmodule")["modules"][0]
        self.assertEqual(module["decls"][0]["init"]["bits"], "zzzz")

    def test_dynamic_tri_driver_stays_loud(self):
        module = lower(
            "module top; tri bus; logic source; assign bus = source; "
            "endmodule")["modules"][0]
        self.assertTrue(any(node.get("sv_kind") == "NetSymbol:Tri"
                            for node in nodes(module)))


if __name__ == "__main__":
    unittest.main()
