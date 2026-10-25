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

    def test_literal_dynamic_array_sort_and_rsort_lower_to_cell_writes(self):
        design = lower(
            """module top;
               int ascending[];
               int descending[];
               initial begin
                 ascending = new[4];
                 descending = new[4];
                 ascending[0] = 4; ascending[1] = 1;
                 ascending[2] = 3; ascending[3] = 2;
                 descending[0] = 4; descending[1] = 1;
                 descending[2] = 3; descending[3] = 2;
                 ascending.sort();
                 descending.rsort();
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("fixed_array_ordering_lowered")]
        self.assertEqual([node["fixed_array_ordering_lowered"] for node in lowered],
                         ["sort", "rsort"])
        self.assertEqual(
            [[write["value"]["operand"]["bits"] for write in node["stmts"]]
             for node in lowered],
            [[format(value, "032b") for value in (1, 2, 3, 4)],
             [format(value, "032b") for value in (4, 3, 2, 1)]])
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_dynamic_array_sort_with_unknown_cell_stays_loud(self):
        design = lower(
            """module top;
               int values[];
               int source;
               initial begin
                 values = new[2];
                 values[0] = source;
                 values[1] = 2;
                 values.sort();
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
