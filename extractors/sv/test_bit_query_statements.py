"""Discarded literal bit queries have no represented state effect."""

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


class BitQueryStatements(unittest.TestCase):
    def test_literal_queries_are_inert(self):
        design = extract_source(
            "module top; initial begin "
            "$countbits(4'b1010, 1'b1, 1'bx); "
            "$countones(4'b1010); $onehot(4'b0001); "
            "$onehot0(4'b0000); $isunknown(4'b10x0); "
            "end endmodule")
        marks = [node.get("bit_query_statement") for node in nodes(design)
                 if node.get("bit_query_statement")]
        self.assertEqual(marks,
                         ["$countbits", "$countones", "$onehot",
                          "$onehot0", "$isunknown"])

    def test_dynamic_operand_stays_loud(self):
        design = extract_source(
            "module top; int value; initial $countones(value); endmodule")
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
