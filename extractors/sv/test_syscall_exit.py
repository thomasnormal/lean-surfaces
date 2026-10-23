"""`$exit` is inert outside a program-originating process."""

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


class ExitTask(unittest.TestCase):
    def test_module_exit_is_ignored(self):
        design = lower('module top; initial begin $exit; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_module_exit_with_parentheses_is_ignored(self):
        design = lower('module top; initial begin $exit(); $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
