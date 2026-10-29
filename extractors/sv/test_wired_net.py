"""Admission checks for un-driven wired-resolution nets."""

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


class WiredNet(unittest.TestCase):
    def test_un_driven_wired_nets_have_high_impedance_initializers(self):
        module = lower(
            "module top; wand a; wor b; triand c; trior d; endmodule")["modules"][0]
        self.assertEqual([decl["init"]["bits"] for decl in module["decls"]],
                         ["z", "z", "z", "z"])
        self.assertFalse(any(node.get("sv_kind", "").startswith("NetSymbol:")
                             for node in nodes(module)))

    def test_un_driven_vector_wand_repeats_high_impedance(self):
        module = lower("module top; wand [3:0] bus; endmodule")["modules"][0]
        self.assertEqual(module["decls"][0]["init"]["bits"], "zzzz")

    def test_dynamic_wired_driver_stays_loud(self):
        module = lower(
            "module top; wand bus; logic source; assign bus = source; "
            "endmodule")["modules"][0]
        self.assertTrue(any(node.get("sv_kind") == "NetSymbol:WAnd"
                            for node in nodes(module)))


if __name__ == "__main__":
    unittest.main()
