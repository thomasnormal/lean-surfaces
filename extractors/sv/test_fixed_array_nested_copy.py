"""Whole bounded multidimensional fixed-array copies lower cellwise."""
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


class FixedArrayNestedCopy(unittest.TestCase):
    def test_whole_nested_copy_uses_ordinal_cells(self):
        design = lower(
            "module top; logic [3:0] source [0:1][0:2]; "
            "logic [3:0] target [5:6][9:7]; initial begin "
            "source = '{'{4'h1, 4'h2, 4'h3}, '{4'h4, 4'h5, 4'h6}}; "
            "target = source; if (target[5][9] === 4'h1 && "
            "target[5][7] === 4'h3 && target[6][9] === 4'h4 && "
            "target[6][7] === 4'h6) $display(\"PASS\"); "
            "end endmodule")
        blocks = [node for node in nodes(design)
                  if node.get("fixed_array_nested_copy_lowered")]
        self.assertEqual(len(blocks), 1)
        self.assertEqual(
            [stmt["target"]["name"] for stmt in blocks[0]["stmts"]],
            ["target[5][9]", "target[5][8]", "target[5][7]",
             "target[6][9]", "target[6][8]", "target[6][7]"])
        self.assertEqual(
            [stmt["value"]["name"] for stmt in blocks[0]["stmts"]],
            ["source[0][0]", "source[0][1]", "source[0][2]",
             "source[1][0]", "source[1][1]", "source[1][2]"])
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_mismatched_nested_shape_stays_loud(self):
        design = lower(
            "module top; logic [3:0] source [0:1][0:2]; "
            "logic [3:0] target [0:1][0:1]; "
            "initial target = source; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_nested_self_copy_stays_loud(self):
        design = lower(
            "module top; logic [3:0] value [0:1][0:1]; "
            "initial value = value; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_constant_nested_subarray_copies_to_flat_array(self):
        design = lower(
            "module top; logic [3:0] source [0:1][0:2]; "
            "logic [3:0] row [7:5]; initial begin "
            "source = '{'{4'h1, 4'h2, 4'h3}, '{4'h4, 4'h5, 4'h6}}; "
            "row = source[1]; if (row[7] === 4'h4 && row[5] === 4'h6) "
            "$display(\"PASS\"); end endmodule")
        blocks = [node for node in nodes(design)
                  if node.get("fixed_array_subarray_copy_lowered")]
        self.assertEqual(len(blocks), 1)
        self.assertEqual(
            [stmt["target"]["name"] for stmt in blocks[0]["stmts"]],
            ["row[7]", "row[6]", "row[5]"])
        self.assertEqual(
            [stmt["value"]["name"] for stmt in blocks[0]["stmts"]],
            ["source[1][0]", "source[1][1]", "source[1][2]"])

    def test_dynamic_outer_subarray_copies_a_flat_row(self):
        design = lower(
            "module top; logic [3:0] matrix [3:2][0:2]; "
            "logic [3:0] row [7:5]; logic [1:0] index; "
            "initial begin row = '{4'h1, 4'h2, 4'h3}; index = 2; "
            "matrix[index] = row; if (matrix[2][0] === 4'h1 && "
            "matrix[2][1] === 4'h2 && matrix[2][2] === 4'h3) "
            "$display(\"PASS\"); end endmodule")
        branches = [node for node in nodes(design)
                    if node.get("fixed_array_dynamic_subarray_copy_lowered")]
        self.assertEqual(len(branches), 1)
        self.assertEqual(
            [stmt["target"]["name"] for stmt in branches[0]["then"]["stmts"]],
            ["matrix[3][0]", "matrix[3][1]", "matrix[3][2]"])
        self.assertEqual(
            [stmt["value"]["name"] for stmt in branches[0]["then"]["stmts"]],
            ["row[7]", "row[6]", "row[5]"])
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_dynamic_outer_subarray_shape_mismatch_stays_loud(self):
        design = lower(
            "module top; int matrix [0:1][0:2]; int row [0:1]; int index; "
            "initial matrix[index] = row; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_dynamic_inner_prefix_subarray_copies_a_flat_row(self):
        design = lower(
            "module top; logic [3:0] cube [0:1][0:1][0:2]; "
            "logic [3:0] row [5:3]; logic index; initial begin "
            "row = '{4'ha, 4'hb, 4'hc}; index = 1; cube[0][index] = row; "
            "if (cube[0][1][0] === 4'ha && cube[0][1][1] === 4'hb && "
            "cube[0][1][2] === 4'hc) $display(\"PASS\"); "
            "end endmodule")
        branches = [node for node in nodes(design)
                    if node.get("fixed_array_dynamic_subarray_copy_lowered")]
        self.assertEqual(len(branches), 1)
        self.assertEqual(
            [stmt["target"]["name"] for stmt in branches[0]["then"]["stmts"]],
            ["cube[0][0][0]", "cube[0][0][1]", "cube[0][0][2]"])
        self.assertEqual(
            [stmt["target"]["name"] for stmt in branches[0]["else"]["then"]["stmts"]],
            ["cube[0][1][0]", "cube[0][1][1]", "cube[0][1][2]"])

    def test_dynamic_subarray_source_copies_into_a_flat_row(self):
        design = lower(
            "module top; logic [3:0] matrix [0:1][0:2]; "
            "logic [3:0] row [5:3]; logic index; initial begin "
            "matrix = '{'{4'h1, 4'h2, 4'h3}, '{4'h4, 4'h5, 4'h6}}; "
            "index = 1; row = matrix[index]; if (row[5] === 4'h4 && "
            "row[4] === 4'h5 && row[3] === 4'h6) $display(\"PASS\"); "
            "end endmodule")
        branches = [node for node in nodes(design)
                    if node.get("fixed_array_dynamic_subarray_read_copy_lowered")]
        self.assertEqual(len(branches), 1)
        self.assertEqual(
            [stmt["target"]["name"] for stmt in branches[0]["else"]["then"]["stmts"]],
            ["row[5]", "row[4]", "row[3]"])
        self.assertEqual(
            [stmt["value"]["name"] for stmt in branches[0]["else"]["then"]["stmts"]],
            ["matrix[1][0]", "matrix[1][1]", "matrix[1][2]"])

    def test_dynamic_subarray_source_shape_mismatch_stays_loud(self):
        design = lower(
            "module top; logic [3:0] matrix [0:1][0:2]; "
            "logic [3:0] row [1:0]; logic index; "
            "initial row = matrix[index]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
