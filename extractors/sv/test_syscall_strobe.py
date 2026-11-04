"""Literal `$strobe` calls retain postponed output ordering."""

import unittest

import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


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


class StrobeTask(unittest.TestCase):
    def test_literal_strobe_is_a_syscall(self):
        design = lower(
            'module top; initial begin $display("A"); '
            '$strobe("B"); $display("C"); end endmodule')
        calls = [node for node in nodes(design) if node.get("kind") == "SysCall"]
        self.assertEqual([node["name"] for node in calls],
                         ["$display", "$strobe", "$display"])

    def test_pure_dynamic_strobe_argument_is_deferred(self):
        design = lower(
            'module top; logic [3:0] x; '
            'initial begin x = 4; $strobe("x=%0d", x); x = 9; end endmodule')
        calls = [node for node in nodes(design) if node.get("kind") == "SysCall"]
        self.assertEqual([node["name"] for node in calls], ["$strobe"])
        self.assertEqual(calls[0]["args"][0]["kind"], "Ident")

    def test_effectful_strobe_argument_stays_loud(self):
        design = lower(
            'module top; logic [3:0] x; '
            'initial $strobe("x=%0d", x++); endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
