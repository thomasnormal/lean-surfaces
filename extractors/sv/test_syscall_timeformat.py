"""Literal `$timeformat` is inert when no `%t` consumer exists."""

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


class TimeformatCalls(unittest.TestCase):
    def test_literal_timeformat_without_percent_t_is_inert(self):
        design = lower(
            'module top; initial begin $timeformat(-9, 2, " ns", 10); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("pure_diagnostic") == "$timeformat"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_percent_t_consumer_stays_loud(self):
        design = lower(
            'module top; initial begin $timeformat(-9, 2, " ns", 10); '
            '$display("%t", 0); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_dynamic_timeformat_argument_stays_loud(self):
        design = lower(
            'module top; integer p; initial begin $timeformat(-9, p, " ns", 10); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
