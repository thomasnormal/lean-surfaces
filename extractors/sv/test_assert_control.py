"""Bare assertion-control tasks are inert without assertion state."""

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


class AssertionControlTasks(unittest.TestCase):
    def test_bare_controls_are_inert(self):
        design = lower(
            'module top; initial begin $asserton; $assertoff; '
            '$assertkill; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_argumented_control_stays_loud(self):
        design = lower(
            'module top; initial begin $asserton(0); end endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_literal_assertcontrol_is_inert(self):
        design = lower(
            'module top; initial begin $assertcontrol(1); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_dynamic_assertcontrol_stays_loud(self):
        design = lower(
            'module top; int control; initial $assertcontrol(control); endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_literal_assertcontrol_argument_list_is_inert(self):
        design = lower(
            'module top; initial $assertcontrol(2, 5); endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
