"""Nested packed arrays lower as contiguous vectors with declared labels."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def extract_source(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def unsupported_nodes(value):
    found = []

    def walk(node):
        if isinstance(node, dict):
            if node.get("kind") == "Unsupported":
                found.append(node)
            for child in node.values():
                walk(child)
        elif isinstance(node, list):
            for child in node:
                walk(child)

    walk(value)
    return found


class PackedArrayMultidim(unittest.TestCase):
    def test_nested_canonical_array_uses_element_width_offsets(self):
        design = extract_source(
            "module top; logic [1:0][3:0] a; logic [3:0] out; "
            "assign out = a[1]; endmodule")
        process = design["modules"][0]["processes"][0]
        self.assertEqual(process["value"]["kind"], "SelectRead")
        self.assertEqual(process["value"]["index"]["bits"],
                         "00000000000000000000000000000100")
        self.assertFalse(unsupported_nodes(design))

    def test_upward_nested_array_normalizes_outer_and_inner_labels(self):
        design = extract_source(
            "module top; logic [0:1][0:3] a; logic out; "
            "assign out = a[0][0]; endmodule")
        process = design["modules"][0]["processes"][0]
        value = process["value"]
        self.assertEqual(value["kind"], "SelectRead")
        self.assertEqual(value["index"]["bits"],
                         "00000000000000000000000000000111")
        self.assertEqual(value["value"]["kind"], "Ident")
        self.assertFalse(unsupported_nodes(design))

    def test_nested_constant_scalar_write_flattens_to_root_vector(self):
        design = extract_source(
            "module top; logic [1:0][3:0] a; logic out; "
            "initial begin a[1][2] = 1'b1; out = a[1][2]; end endmodule")
        assignments = [node for node in design["modules"][0]["processes"][0]
                       ["body"]["stmts"] if node.get("kind") == "BlockingAssign"]
        self.assertEqual(assignments[0]["target"]["kind"], "SelectTarget")
        self.assertEqual(assignments[0]["target"]["index"]["bits"],
                         "00000000000000000000000000000110")
        self.assertEqual(assignments[1]["value"]["kind"], "SelectRead")
        self.assertEqual(assignments[1]["value"]["index"]["bits"],
                         "00000000000000000000000000000110")
        self.assertFalse(unsupported_nodes(design))

    def test_packed_enum_array_keeps_scalar_cells(self):
        design = extract_source(
            "module top; typedef enum bit [1:0] {A=2'd0, B=2'd1} E; "
            "E [3:0] states; logic [1:0] out; "
            "assign out = states[1]; endmodule")
        process = design["modules"][0]["processes"][0]
        value = process["value"]
        self.assertEqual(value["kind"], "Squash2")
        self.assertEqual(value["operand"]["kind"], "SelectRead")
        self.assertEqual(value["width"], 2)
        self.assertEqual(value["operand"]["index"]["bits"],
                         "00000000000000000000000000000010")
        self.assertFalse(unsupported_nodes(design))

    def test_dynamic_index_of_wide_packed_element_stays_loud(self):
        design = extract_source(
            "module top; logic [1:0][3:0] a; int i; logic [3:0] out; "
            "assign out = a[i]; endmodule")
        process = design["modules"][0]["processes"][0]
        self.assertEqual(process["kind"], "Assign")
        self.assertEqual(process["value"]["kind"], "Unsupported")
        self.assertEqual(process["value"]["sv_kind"],
                         "ElementSelectExpression:source-type")


if __name__ == "__main__":
    unittest.main()
