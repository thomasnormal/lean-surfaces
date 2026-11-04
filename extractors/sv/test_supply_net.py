"""Admission checks for un-driven supply-strength nets."""

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


class SupplyNet(unittest.TestCase):
    def test_un_driven_scalar_supplies_have_constant_initializers(self):
        module = lower(
            "module top; supply0 gnd; supply1 vcc; endmodule")["modules"][0]
        self.assertEqual(
            [(decl["name"], decl["init"]["bits"])
             for decl in module["decls"]],
            [("gnd", "0"), ("vcc", "1")])
        self.assertFalse(any(node.get("sv_kind", "").startswith("NetSymbol:Supply")
                             for node in nodes(module)))

    def test_un_driven_vector_supply_repeats_the_value(self):
        module = lower(
            "module top; supply0 [3:0] gnd; endmodule")["modules"][0]
        self.assertEqual(module["decls"][0]["init"]["bits"], "0000")

    def test_supply_with_a_continuous_driver_stays_loud(self):
        module = lower(
            "module top; supply0 gnd; wire source; assign gnd = source; "
            "endmodule")["modules"][0]
        self.assertTrue(any(node.get("sv_kind") == "NetSymbol:Supply0"
                            for node in nodes(module)))


if __name__ == "__main__":
    unittest.main()
