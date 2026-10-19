"""Whole fixed-unpacked positional assignments lowered to vector cells."""
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


class UnpackedArrayAssignments(unittest.TestCase):
    def test_positional_pattern_writes_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1]; "
            "initial begin value = '{8'h12, 8'h34}; "
            "if (value[1] === 8'h34) $display(\"PASS\"); end endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value[0]", "value[1]"])
        self.assertEqual([a["value"].get("bits", a["value"].get("operand", {}).get("bits"))
                          for a in assigns],
                         ["00010010", "00110100"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_default_pattern_writes_all_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1]; "
            "initial value = '{default:8'h12}; endmodule")
        targets = [node["target"]["name"] for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual(targets, ["value[0]", "value[1]"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_replicated_pattern_writes_all_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:2]; "
            "initial value = '{3{8'h12}}; endmodule")
        values = [node["value"]["bits"] for node in nodes(design)
                  if node.get("kind") == "BlockingAssign"]
        self.assertEqual(values, ["00010010"] * 3)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_wrong_length_replicated_pattern_stays_loud(self):
        design = extract_source(
            "module top; logic [7:0] value [0:2]; "
            "initial value = '{2{8'h12}}; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_destination_alias_stays_loud(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1]; "
            "initial value = '{value[1], 8'h34}; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_dynamic_index_is_bounded_over_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1]; int index; "
            "initial begin index = 1; value[index] = 8'h34; "
            "if (value[index] === 8'h34) $display(\"PASS\"); end endmodule")
        self.assertTrue(any(node.get("kind") == "If"
                            for node in nodes(design)))
        self.assertTrue(any(node.get("kind") == "Ternary"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dynamic_index_requires_fixed_one_dimensional_storage(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1][0:1]; logic [1:0] index; "
            "initial value[index][0] = 8'h34; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_whole_array_copy_reuses_cells(self):
        design = extract_source(
            "module top; logic [7:0] source [0:1]; logic [7:0] value [0:1]; "
            "initial begin source[0] = 8'h12; source[1] = 8'h34; "
            "value = source; if (value[1] === 8'h34) $display(\"PASS\"); "
            "end endmodule")
        targets = [node["target"]["name"] for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertIn("value[0]", targets)
        self.assertIn("value[1]", targets)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_mismatched_array_copy_stays_loud(self):
        design = extract_source(
            "module top; logic [7:0] source [0:2]; logic [7:0] value [0:1]; "
            "initial value = source; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_conditional_array_assignment_merges_cells(self):
        design = extract_source(
            "module top; logic [7:0] a [0:1]; logic [7:0] b [0:1]; "
            "logic [7:0] value [0:1]; logic choose; "
            "initial begin value = choose ? a : b; end endmodule")
        values = [node for node in nodes(design) if node.get("kind") == "Ternary"]
        self.assertEqual(len(values), 2)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_constant_slice_pattern_writes_selected_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:3]; "
            "initial begin value[1:2] = '{8'h12, 8'h34}; "
            "if (value[1] === 8'h12 && value[2] === 8'h34) "
            "$display(\"PASS\"); end endmodule")
        targets = [node["target"]["name"] for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual(targets, ["value[1]", "value[2]"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dynamic_slice_pattern_stays_loud(self):
        design = extract_source(
            "module top; logic [7:0] value [0:3]; integer i; "
            "initial value[i:i+1] = '{8'h12, 8'h34}; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_slice_copy_pairs_cells(self):
        design = extract_source(
            "module top; logic [7:0] source [0:3]; logic [7:0] value [0:3]; "
            "initial begin value[1:2] = source[2:3]; end endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value[1]", "value[2]"])
        self.assertEqual([a["value"]["name"] for a in assigns],
                         ["source[2]", "source[3]"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_overlapping_slice_copy_stays_loud(self):
        design = extract_source(
            "module top; logic [7:0] value [0:3]; "
            "initial value[1:2] = value[0:1]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_slice_default_pattern_writes_selected_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:3]; "
            "initial value[1:2] = '{default:8'h12}; endmodule")
        values = [node["value"]["bits"] for node in nodes(design)
                  if node.get("kind") == "BlockingAssign"]
        self.assertEqual(values, ["00010010", "00010010"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_slice_replicated_pattern_writes_selected_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:3]; "
            "initial value[1:2] = '{2{8'h34}}; endmodule")
        values = [node["value"]["bits"] for node in nodes(design)
                  if node.get("kind") == "BlockingAssign"]
        self.assertEqual(values, ["00110100", "00110100"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_slice_conditional_assignment_merges_cells(self):
        design = extract_source(
            "module top; logic [7:0] a [0:3]; logic [7:0] b [0:3]; "
            "logic [7:0] value [0:3]; logic choose; "
            "initial value[1:2] = choose ? a[2:3] : b[0:1]; endmodule")
        values = [node for node in nodes(design) if node.get("kind") == "Ternary"]
        self.assertEqual(len(values), 2)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
