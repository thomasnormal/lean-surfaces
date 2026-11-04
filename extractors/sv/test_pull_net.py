"""Admission checks for un-driven implicit-pull nets."""

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


class PullNet(unittest.TestCase):
    def test_un_driven_tri0_and_tri1_have_pull_initializers(self):
        module = lower(
            "module top; tri0 gnd; tri1 vcc; endmodule")["modules"][0]
        self.assertEqual(
            [(decl["name"], decl["init"]["bits"])
             for decl in module["decls"]],
            [("gnd", "0"), ("vcc", "1")])
        self.assertFalse(any(node.get("sv_kind", "").startswith("NetSymbol:Tri")
                             for node in nodes(module)))

    def test_un_driven_vector_tri1_repeats_pull_one(self):
        module = lower("module top; tri1 [3:0] vcc; endmodule")["modules"][0]
        self.assertEqual(module["decls"][0]["init"]["bits"], "1111")

    def test_driven_pull_net_stays_loud(self):
        module = lower(
            "module top; tri0 gnd; logic source; assign gnd = source; "
            "endmodule")["modules"][0]
        self.assertTrue(any(node.get("sv_kind") == "NetSymbol:Tri0"
                            for node in nodes(module)))


if __name__ == "__main__":
    unittest.main()
