"""Whole-vector operations over one-dimensional noncanonical packed ranges."""
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


class PackedRanges(unittest.TestCase):
    def test_whole_ascending_vector_is_admitted(self):
        design = extract_source(
            "module top; logic [0:7] value; "
            "initial begin value = 8'hA5; "
            "if (value === 8'hA5) $display(\"PASS\"); end endmodule")
        kinds = [node.get("sv_kind") for node in nodes(design)]
        self.assertNotIn("VariableSymbol:range", kinds)
        decls = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertEqual([(decl["name"], decl["width"]) for decl in decls],
                         [("value", 8)])

    def test_constant_selected_ascending_vector_is_normalized(self):
        design = extract_source(
            "module top; logic [0:7] value; "
            "initial begin value[2] = 1'b1; "
            "if (value[2] === 1'b1) $display(\"PASS\"); end endmodule")
        targets = [node for node in nodes(design)
                   if node.get("kind") == "SelectTarget"]
        reads = [node for node in nodes(design)
                 if node.get("kind") == "SelectRead"]
        self.assertEqual(len(targets), 1)
        self.assertEqual(len(reads), 1)
        self.assertFalse(targets[0]["index_signed"])
        self.assertEqual(targets[0]["index"]["bits"], "0" * 29 + "101")

    def test_dynamic_selected_ascending_vector_normalizes_target(self):
        design = extract_source(
            "module top; logic [0:7] value; integer index; "
            "initial value[index] = 1'b1; endmodule")
        targets = [node for node in nodes(design)
                   if node.get("kind") == "SelectTarget"]
        self.assertEqual(len(targets), 1)
        self.assertEqual(targets[0]["index"]["op"], "-")
        self.assertEqual(targets[0]["index"]["left"]["bits"],
                         "0" * 31 + "111")
        self.assertTrue(targets[0]["index_signed"])

    def test_constant_part_select_ascending_vector_is_normalized(self):
        design = extract_source(
            "module top; logic [0:7] value; "
            "initial begin value[1:4] = 4'b1010; "
            "if (value[1:4] === 4'b1010) $display(\"PASS\"); "
            "end endmodule")
        targets = [node for node in nodes(design)
                   if node.get("kind") == "SelectTarget"]
        reads = [node for node in nodes(design)
                 if node.get("kind") == "SelectRead"]
        self.assertEqual(len(targets), 1)
        self.assertEqual(len(reads), 1)
        self.assertEqual(targets[0]["width"], 4)
        self.assertEqual(targets[0]["index"]["bits"], "0" * 29 + "011")
        self.assertEqual(reads[0]["index"]["bits"], "0" * 29 + "011")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dynamic_part_select_ascending_vector_remains_loud(self):
        design = extract_source(
            "module top; logic [0:7] value; integer index; "
            "initial value[index:index+2] = 3'b101; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_out_of_range_part_select_ascending_vector_remains_loud(self):
        design = extract_source(
            "module top; logic [0:7] value; "
            "initial value[6:9] = 4'b1010; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
