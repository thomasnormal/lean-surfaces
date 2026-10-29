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

    def test_procedural_pattern_copy_and_repeated_reverse_lower(self):
        design = lower(
            """module top;
               logic [7:0] source[3];
               logic [7:0] values[3];
               logic [7:0] sibling[3];
               initial begin
                 source = '{8'h10, 8'h20, 8'h30};
                 values = source;
                 sibling = source;
                 values.reverse();
                 values.reverse();
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("fixed_array_reverse_lowered")]
        self.assertEqual(len(lowered), 2)
        self.assertEqual(
            [[write["value"].get("bits") for write in node["stmts"]]
             for node in lowered],
            [["00110000", "00100000", "00010000"],
             ["00010000", "00100000", "00110000"]])

    def test_branching_procedural_reverse_stays_loud(self):
        design = lower(
            """module top;
               int values[2];
               initial begin
                 values = '{1, 2};
                 if (1) values.reverse();
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_procedural_four_state_pattern_preserves_xz(self):
        design = lower(
            """module top;
               logic [7:0] values[3];
               initial begin
                 values = '{8'b10xz01zx, 8'bz001x110, 8'b01zx10xz};
                 values.reverse();
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("fixed_array_reverse_lowered")]
        self.assertEqual(len(lowered), 1)
        self.assertEqual(
            [write["value"].get("bits") for write in lowered[0]["stmts"]],
            ["01zx10xz", "z001x110", "10xz01zx"])

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

    def test_fixed_array_pattern_sort_and_rsort_replay_source_order(self):
        design = lower(
            """module top;
               int signed values[0:3];
               initial begin
                 values = '{-3, 5, 0, -3};
                 values.sort();
                 values.rsort();
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("fixed_array_ordering_lowered")]
        self.assertEqual([node["fixed_array_ordering_lowered"] for node in lowered],
                         ["sort", "rsort"])
        def bits(value):
            while value.get("kind") == "Squash2":
                value = value["operand"]
            if value.get("kind") == "Unary":
                return format((-int(value["operand"]["bits"], 2)) & 0xffffffff,
                              "032b")
            return value["bits"]

        self.assertEqual(
            [[bits(write["value"]) for write in node["stmts"]]
             for node in lowered],
            [[format(value & 0xffffffff, "032b") for value in (-3, -3, 0, 5)],
             [format(value & 0xffffffff, "032b") for value in (5, 0, -3, -3)]])
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_fixed_array_sort_with_unknown_cell_stays_loud(self):
        design = lower(
            """module top;
               int values[0:1];
               int source;
               initial begin
                 values = '{source, 2};
                 values.sort();
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_fixed_array_sort_after_direct_cell_write_stays_loud(self):
        design = lower(
            """module top;
               int values[0:1] = '{1, 2};
               initial begin
                 values[0] = 9;
                 values.sort();
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_fixed_struct_array_sort_with_field_reorders_complete_records(self):
        design = lower(
            """module top;
               typedef struct { byte red; byte green; } color_t;
               color_t values[3];
               initial begin
                 values[0] = '{red: 5, green: 9};
                 values[1] = '{red: 1, green: 7};
                 values[2] = '{red: 3, green: 4};
                 values.sort with (item.red);
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("fixed_struct_array_ordering_with_lowered")]
        self.assertEqual([node["fixed_struct_array_ordering_with_lowered"]
                          for node in lowered], ["sort"])
        self.assertEqual(
            [write["target"]["name"] for write in lowered[0]["stmts"]],
            ["values[0].red", "values[0].green", "values[1].red", "values[1].green",
             "values[2].red", "values[2].green"])
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_fixed_struct_array_rsort_with_field_replays_pattern_values(self):
        design = lower(
            """module top;
               typedef struct { byte red; byte green; } color_t;
               color_t values[3];
               initial begin
                 values[0] = '{red: 5, green: 9};
                 values[1] = '{red: 1, green: 7};
                 values[2] = '{red: 3, green: 4};
                 values.rsort with (item.red);
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("fixed_struct_array_ordering_with_lowered")]
        self.assertEqual([node["fixed_struct_array_ordering_with_lowered"]
                          for node in lowered], ["rsort"])
        def bits(value):
            while value.get("kind") == "Squash2":
                value = value["operand"]
            return value.get("bits")

        self.assertEqual(
            [[bits(write["value"]) for write in node["stmts"]]
             for node in lowered],
            [["00000101", "00001001", "00000011", "00000100",
              "00000001", "00000111"]])

    def test_struct_array_sort_with_computed_key_stays_loud(self):
        design = lower(
            """module top;
               typedef struct { byte red; byte green; } color_t;
               color_t values[2];
               initial begin
                 values[0] = '{red: 1, green: 2};
                 values[1] = '{red: 2, green: 1};
                 values.sort with (item.red + 1);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_struct_array_sort_with_tuple_key_orders_lexicographically(self):
        design = lower(
            """module top;
               typedef struct { byte red; byte green; } color_t;
               color_t values[4];
               initial begin
                 values[0] = '{red: 1, green: 5};
                 values[1] = '{red: 2, green: 3};
                 values[2] = '{red: 3, green: 4};
                 values[3] = '{red: 4, green: 1};
                 values.sort(x) with ({x.green, x.red});
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("fixed_struct_array_ordering_with_lowered")]
        self.assertEqual([node["fixed_struct_array_ordering_with_lowered"]
                          for node in lowered], ["sort"])
        def bits(value):
            while value.get("kind") == "Squash2":
                value = value["operand"]
            return value.get("bits")
        self.assertEqual(
            [[bits(write["value"]) for write in node["stmts"]]
             for node in lowered],
            [["00000100", "00000001", "00000010", "00000011",
              "00000011", "00000100", "00000001", "00000101"]])

    def test_struct_array_repeated_order_requires_same_with_key(self):
        design = lower(
            """module top;
               typedef struct { byte red; byte green; } color_t;
               color_t values[2];
               initial begin
                 values[0] = '{red: 1, green: 2};
                 values[1] = '{red: 2, green: 1};
                 values.sort();
                 values.rsort with (item.red);
               end
               endmodule""")
        self.assertFalse(any(node.get("fixed_struct_array_ordering_with_lowered")
                             for node in nodes(design)))

    def test_struct_array_repeated_order_with_same_key_lowers_both_calls(self):
        design = lower(
            """module top;
               typedef struct { byte red; byte green; } color_t;
               color_t values[3];
               initial begin
                 values[0] = '{red: 5, green: 9};
                 values[1] = '{red: 1, green: 7};
                 values[2] = '{red: 3, green: 4};
                 values.sort with (item.red);
                 values.rsort with (item.red);
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("fixed_struct_array_ordering_with_lowered")]
        self.assertEqual([node["fixed_struct_array_ordering_with_lowered"]
                          for node in lowered], ["sort", "rsort"])
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
