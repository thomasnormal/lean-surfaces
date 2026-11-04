"""Admission checks for direct whole-net aliases in the legacy tier."""

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


def module(source):
    return lower(source)["modules"][0]


class NetAlias(unittest.TestCase):
    def test_scalar_and_vector_aliases_share_one_cell(self):
        result = module(
            "module top; wire a; wire b; wire [3:0] x; wire [3:0] y; "
            "alias a = b; alias x = y; endmodule")
        self.assertEqual([decl["name"] for decl in result["decls"]], ["a", "x"])
        self.assertFalse(any(node.get("sv_kind") == "NetAliasSymbol:NetAlias"
                             for node in nodes(result)))

    def test_chained_aliases_collapse_to_the_first_net(self):
        result = module(
            "module top; wire a; wire b; wire c; alias a = b; alias b = c; "
            "endmodule")
        self.assertEqual([decl["name"] for decl in result["decls"]], ["a"])

    def test_selected_and_mismatched_aliases_remain_loud(self):
        result = module(
            "module top; wire [3:0] a; wire [3:0] b; wire [1:0] c; "
            "alias a[1:0] = b[1:0]; alias a = c; endmodule")
        walls = [node for node in nodes(result)
                 if node.get("sv_kind") == "NetAliasSymbol:NetAlias"]
        self.assertEqual(len(walls), 2)
        self.assertEqual([decl["name"] for decl in result["decls"]], ["a", "b", "c"])


if __name__ == "__main__":
    unittest.main()
