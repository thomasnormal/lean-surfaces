"""Literal severity format arguments remain side-effect free."""

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


class QuietSeverityLiterals(unittest.TestCase):
    def test_literal_format_arguments_are_erased(self):
        design = lower(
            'module top; initial begin $warning("x=%0d", 7); '
            '$info("h=%h", 8\'h3a); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_identifier_argument_is_admitted(self):
        design = lower(
            'module top; logic [3:0] x; initial $warning("x=%0d", x); endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
