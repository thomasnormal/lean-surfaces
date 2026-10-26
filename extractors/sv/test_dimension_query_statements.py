"""Discarded fixed dimension queries have no represented state effect."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def extract_source(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()
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


class DimensionQueryStatements(unittest.TestCase):
    def test_fixed_queries_are_inert(self):
        design = extract_source(
            "module top; logic [7:0] value; initial begin "
            "$size(value); $high(value); $left(value); $right(value); "
            "$low(value); $increment(value); $dimensions(value); "
            "$unpacked_dimensions(value); end endmodule")
        marks = [node.get("dimension_query_statement") for node in nodes(design)
                 if node.get("dimension_query_statement")]
        self.assertEqual(
            marks,
            ["$size", "$high", "$left", "$right", "$low", "$increment",
             "$dimensions", "$unpacked_dimensions"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dynamic_or_effectful_queries_stay_loud(self):
        design = extract_source(
            "module top; logic [7:0] value; int dimension; "
            "initial begin $size(value, dimension); "
            "$size(value++); end endmodule")
        self.assertFalse(any(node.get("dimension_query_statement")
                             for node in nodes(design)))
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
