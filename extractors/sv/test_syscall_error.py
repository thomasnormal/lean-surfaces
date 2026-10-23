"""Literal $error is diagnostic-only; terminating tasks stay loud."""

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


class ErrorTask(unittest.TestCase):
    def test_literal_error_is_erased(self):
        design = lower(
            'module top; initial begin $error("diagnostic"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_fatal_remains_loud(self):
        design = lower(
            'module top; initial $fatal(1, "fatal"); endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_dynamic_error_argument_remains_loud(self):
        design = lower(
            'module top; logic [3:0] x; initial $error("x=%0d", x); endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
