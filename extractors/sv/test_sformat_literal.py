"""Literal ``$sformat`` writes to packed integral storage."""

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


class SformatLiteral(unittest.TestCase):
    def test_literal_sformat_is_an_integral_assignment(self):
        design = lower(
            '''module top;
               logic [7:0] narrow;
               logic [47:0] wide;
               initial begin
                 $sformat(narrow, "A");
                 $sformat(wide, "Hello");
               end
               endmodule''')
        lowered = [node for node in nodes(design)
                   if node.get("sformat_literal_assignment")]
        self.assertEqual(len(lowered), 2)
        self.assertEqual(lowered[0]["value"]["bits"], "01000001")
        self.assertEqual(lowered[1]["value"]["bits"],
                         "000000000100100001100101011011000110110001101111")
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_formatted_or_dynamic_sformat_stays_loud(self):
        design = lower(
            '''module top;
               logic [7:0] value;
               int source;
               initial begin
                 $sformat(value, "%0d", source);
               end
               endmodule''')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_selected_sformat_target_stays_loud(self):
        design = lower(
            '''module top;
               logic [15:0] value;
               initial $sformat(value[7:0], "A");
               endmodule''')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
