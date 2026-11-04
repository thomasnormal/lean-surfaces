"""Dimension metadata through an inner dynamic unpacked dimension."""

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


class MixedDimensionQueries(unittest.TestCase):
    def test_fixed_dimensions_through_inner_dynamic_array(self):
        design = lower(
            'module top; int values[3][][5]; '
            'initial begin $display("%0d %0d %0d", '
            '$size(values, 1), $size(values, 3), '
            '$unpacked_dimensions(values)); end endmodule')
        queries = [node for node in nodes(design)
                   if node.get("fixed_dimension_query")]
        self.assertEqual(
            [(node["fixed_dimension_query"], int(node["bits"], 2))
             for node in queries],
            [("$size", 3), ("$size", 5), ("$unpacked_dimensions", 3)])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_local_mixed_array_declaration_is_erased(self):
        design = lower(
            'module top; initial begin int values[3][][5]; '
            '$size(values, 1); $size(values, 3); end endmodule')
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dynamic_dimension_and_value_use_stay_loud(self):
        for source in (
                'module top; int values[3][][5]; '
                'initial $display("%0d", $size(values, 2)); endmodule',
                'module top; int values[3][][5]; '
                'initial begin $display("%0d", $size(values, 3)); '
                'values[0][0][0] = 1; end endmodule'):
            with self.subTest(source=source):
                self.assertTrue(any(node.get("kind") == "Unsupported"
                                    for node in nodes(lower(source))))


if __name__ == "__main__":
    unittest.main()
