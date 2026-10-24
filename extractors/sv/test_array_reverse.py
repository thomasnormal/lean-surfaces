"""Fixed unpacked array ``reverse()`` lowering."""

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


class ArrayReverse(unittest.TestCase):
    def test_literal_fixed_array_reverse_lowers_to_cell_writes(self):
        design = lower(
            """module top;
               int values[3] = '{10, 20, 30};
               initial begin
                 values.reverse();
                 if (values[0] == 30 && values[2] == 10) $display("PASS");
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("fixed_array_reverse_lowered")]
        self.assertEqual(len(lowered), 1)
        writes = lowered[0]["stmts"]
        self.assertEqual([write["target"]["name"] for write in writes],
                         ["values[0]", "values[1]", "values[2]"])
        self.assertEqual([write["value"]["operand"]["bits"] for write in writes],
                         [format(value, "032b") for value in (30, 20, 10)])
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_dynamic_array_reverse_stays_loud(self):
        design = lower(
            """module top;
               int values[] = new[2];
               initial values.reverse();
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_nonliteral_fixed_array_reverse_stays_loud(self):
        design = lower(
            """module top;
               int source;
               int values[2] = '{source, 2};
               initial values.reverse();
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
