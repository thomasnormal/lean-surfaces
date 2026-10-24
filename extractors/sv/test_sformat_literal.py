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

    def test_constant_formatted_selected_writes_lower(self):
        design = lower(
            '''module top;
               logic [47:0] packet;
               initial begin
                 $sformat(packet[39:8], "%b", 4'b10xz);
                 $sformat(packet[39:8], "%s:%0d", "Q", 2);
                 $swrite(packet[39:8], "%0d", 5);
               end
               endmodule''')
        lowered = [node for node in nodes(design)
                   if node.get("constant_format_integral_assignment")]
        self.assertEqual(len(lowered), 3)
        self.assertTrue(all(node["target"]["kind"] == "SelectTarget"
                            for node in lowered))
        self.assertEqual(lowered[0]["value"]["bits"],
                         "00110001001100000111100001111010")
        self.assertEqual(lowered[1]["value"]["bits"],
                         "00000000000000000101000100110010")
        self.assertEqual(lowered[2]["value"]["bits"],
                         "00000000000000000000000000110101")

    def test_dynamic_or_unadmitted_formatted_write_stays_loud(self):
        design = lower(
            '''module top;
               logic [31:0] value;
               int source;
               initial begin
                 $swrite(value, "%0d", source);
                 $swrite(value, "%f", 1.0);
               end
               endmodule''')
        self.assertGreaterEqual(
            [node.get("sv_kind") for node in nodes(design)].count(
                "ExpressionStatement:CallExpression"), 2)


if __name__ == "__main__":
    unittest.main()
