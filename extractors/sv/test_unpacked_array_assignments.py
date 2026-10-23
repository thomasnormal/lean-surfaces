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
        values = [node["value"].get("bits") or
                  node["value"].get("operand", {}).get("bits")
                  for node in nodes(design)
                  if node.get("kind") == "BlockingAssign"]
        self.assertEqual(values, ["00010010"] * 3)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_nested_replicated_pattern_repeats_inner_elements(self):
        design = extract_source(
            "module top; int value [1:6]; "
            "initial value = '{3{4, 5}}; endmodule")
        values = [node["value"].get("bits") or
                  node["value"].get("operand", {}).get("bits")
                  for node in nodes(design)
                  if node.get("kind") == "BlockingAssign"]
        self.assertEqual(values, [format(v, "032b") for v in (4, 5, 4, 5, 4, 5)])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_nested_array_pattern_writes_all_leaf_cells(self):
        design = extract_source(
            "module top; int value [0:1][0:2]; "
            "initial value = '{2{'{3{7}}}}; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value[0][0]", "value[0][1]", "value[0][2]",
                          "value[1][0]", "value[1][1]", "value[1][2]"])
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

    def test_indexed_slice_copy_pairs_runtime_windows(self):
        design = extract_source(
            "module top; int source [0:9]; int value [0:9]; int i, j; "
            "parameter int c = 3; initial begin "
            "i = 2; j = 5; value[i+:c] = source[j+:c]; end endmodule")
        roots = [node for node in nodes(design)
                 if node.get("kind") == "If" and
                 node.get("cond", {}).get("op") == "==="]
        self.assertGreaterEqual(len(roots), 8)
        branch = next(root["then"] for root in roots
                      if root["cond"]["right"]["bits"].endswith("0010"))
        assigns = branch["stmts"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value[2]", "value[3]", "value[4]"])
        self.assertTrue(all(a["value"].get("kind") == "Squash2"
                            for a in assigns))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_indexed_down_slice_preserves_source_direction(self):
        design = extract_source(
            "module top; int source [0:9]; int value [0:9]; int i, j; "
            "parameter int c = 3; initial begin "
            "i = 4; j = 7; value[i-:c] = source[j-:c]; end endmodule")
        roots = [node for node in nodes(design)
                 if node.get("kind") == "If" and
                 node.get("cond", {}).get("op") == "==="]
        self.assertGreaterEqual(len(roots), 8)
        branch = next(root["then"] for root in roots
                      if root["cond"]["right"]["bits"].endswith("0100"))
        assigns = branch["stmts"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value[4]", "value[3]", "value[2]"])
        def then_names(node):
            out = []
            while isinstance(node, dict) and node.get("kind") == "Ternary":
                out.append(node["then"]["name"])
                node = node["else"]
            return out
        def selected_name(node, bits):
            while isinstance(node, dict) and node.get("kind") == "Ternary":
                if node["cond"]["right"]["bits"].endswith(bits):
                    return node["then"]["name"]
                node = node["else"]
            return None
        self.assertEqual([selected_name(a["value"]["operand"], bits)
                          for a, bits in zip(assigns, ("0111", "0111", "0111"))],
                         ["source[7]", "source[6]", "source[5]"])

    def test_indexed_slice_requires_positive_constant_width(self):
        design = extract_source(
            "module top; int source [0:3]; int value [0:3]; int i, j, c; "
            "initial value[i+:c] = source[j+:c]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "InvalidStatement"
                            for node in nodes(design)))

    def test_indexed_slice_self_copy_stays_loud(self):
        design = extract_source(
            "module top; int value [0:3]; int i, j; parameter int c = 2; "
            "initial value[i+:c] = value[j+:c]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_bitstream_cast_fills_fixed_array_from_msb(self):
        design = extract_source(
            "module top; typedef bit [23:0] bits_t; typedef bit [7:0] bytes_t [3]; "
            "initial begin bits_t bits; bytes_t bytes; bits = 24'habcdef; "
            "bytes = bytes_t'(bits); if (bytes[0] === 8'hab && "
            "bytes[1] === 8'hcd && bytes[2] === 8'hef) $display(\"PASS\"); end endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"].split(":bytes", 1)[1]
                          for a in assigns[-3:]],
                         ["[0]", "[1]", "[2]"])
        self.assertEqual([a["value"]["operand"]["index"]["bits"]
                          for a in assigns[-3:]],
                         [format(n, "032b") for n in (16, 8, 0)])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_struct_elements_pattern_flattens_each_array_row(self):
        design = extract_source(
            "typedef struct { int a; time b; } ab_t; "
            "module top; ab_t abkey[1:0]; initial begin "
            "abkey = '{'{a:1, b:2}, '{a:5, b:99}}; end endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["abkey[1].a", "abkey[1].b", "abkey[0].a", "abkey[0].b"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_struct_pattern_accepts_time_literals(self):
        design = extract_source(
            "typedef struct { int a; time b; } ab_t; module top; ab_t abkey[1:0]; "
            "initial abkey = '{'{a:1, b:2ns}, '{int:5, time:$time}}; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["abkey[1].a", "abkey[1].b", "abkey[0].a", "abkey[0].b"])
        self.assertEqual(assigns[1]["value"]["bits"], "0" * 62 + "10")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_whole_array_equality_pairs_cells(self):
        design = extract_source(
            "module top; logic [7:0] a [0:1]; logic [7:0] b [0:1]; "
            "initial if (a == b) $display(\"PASS\"); endmodule")
        ops = [node.get("op") for node in nodes(design)
               if node.get("kind") == "Binary"]
        self.assertIn("&&", ops)
        self.assertGreaterEqual(ops.count("=="), 2)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_slice_inequality_pairs_cells(self):
        design = extract_source(
            "module top; logic [7:0] a [0:3]; logic [7:0] b [0:3]; "
            "initial if (a[1:2] != b[2:3]) $display(\"PASS\"); endmodule")
        ops = [node.get("op") for node in nodes(design)
               if node.get("kind") == "Binary"]
        self.assertIn("||", ops)
        self.assertGreaterEqual(ops.count("!="), 2)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_mismatched_array_equality_stays_loud(self):
        design = extract_source(
            "module top; logic [7:0] a [0:1]; logic [7:0] b [0:2]; "
            "initial if (a == b) $display(\"PASS\"); endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_whole_array_case_equality_pairs_cells(self):
        design = extract_source(
            "module top; logic [7:0] a [0:1]; logic [7:0] b [0:1]; "
            "initial if (a === b) $display(\"PASS\"); endmodule")
        ops = [node.get("op") for node in nodes(design)
               if node.get("kind") == "Binary"]
        self.assertIn("&&", ops)
        self.assertGreaterEqual(ops.count("===",), 2)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_slice_case_inequality_pairs_cells(self):
        design = extract_source(
            "module top; logic [7:0] a [0:3]; logic [7:0] b [0:3]; "
            "initial if (a[1:2] !== b[2:3]) $display(\"PASS\"); endmodule")
        ops = [node.get("op") for node in nodes(design)
               if node.get("kind") == "Binary"]
        self.assertIn("||", ops)
        self.assertGreaterEqual(ops.count("!=="), 2)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_unpacked_array_concatenation_fills_cells(self):
        design = extract_source(
            "module top; int value [1:3]; "
            "initial value = {1, 2, 3}; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value[1]", "value[2]", "value[3]"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_unpacked_array_concat_alias_stays_loud(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1]; "
            "initial value = {value[0], 8'h12}; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_unpacked_concat_accepts_typed_array_pattern_operand(self):
        design = extract_source(
            "typedef int AI3 [1:3]; module top; AI3 source; int value [1:9]; "
            "initial value = {source, 4, AI3'{5, 6, 7}, 8, 9}; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns[-9:]],
                         [f"value[{i}]" for i in range(1, 10)])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_unpacked_concat_nested_pattern_width_mismatch_stays_loud(self):
        design = extract_source(
            "module top; typedef int AI2 [0:1]; AI2 source; int value [0:2]; "
            "initial value = {source, AI2'{1, 2}}; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_unpacked_assignment_pattern_lhs_pairs_scalar_targets(self):
        design = extract_source(
            "typedef int U3 [0:2]; module top; int source [0:2]; byte a, b, c; "
            "initial begin U3'{a, b, c} = source; end endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns[-3:]],
                         ["a", "b", "c"])
        self.assertEqual([a["value"]["operand"]["operand"]["name"]
                          for a in assigns[-3:]],
                         ["source[0]", "source[1]", "source[2]"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_unpacked_assignment_pattern_lhs_alias_stays_loud(self):
        design = extract_source(
            "typedef int U2 [0:1]; module top; int source [0:1]; "
            "initial U2'{source[0], source[1]} = source; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_constant_subarray_copy_pairs_remaining_cells(self):
        design = extract_source(
            "module top; int source [0:1][0:2]; int row [0:2]; "
            "initial row = source[1]; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["row[0]", "row[1]", "row[2]"])
        self.assertEqual([a["value"]["operand"]["name"] for a in assigns],
                         ["source[1][0]", "source[1][1]", "source[1][2]"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_constant_subarray_pattern_writes_remaining_cells(self):
        design = extract_source(
            "module top; int value [0:1][0:2]; "
            "initial value[1] = '{10, 20, 30}; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value[1][0]", "value[1][1]", "value[1][2]"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dynamic_subarray_copy_stays_loud(self):
        design = extract_source(
            "module top; int source [0:1][0:2]; int row [0:2]; int i; "
            "initial row = source[i]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_subarray_self_copy_stays_loud(self):
        design = extract_source(
            "module top; int value [0:1][0:2]; "
            "initial value[0] = value[1]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_packed_slice_inside_array_cells_copies_window(self):
        design = extract_source(
            "module top; bit [3:0][7:0] joe [0:9]; "
            "initial joe[7][3:2] = joe[6][1:0]; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        selected = assigns[-1]
        self.assertEqual(selected["target"]["kind"], "SelectTarget")
        self.assertEqual(selected["target"]["index"]["bits"],
                         "00000000000000000000000000010000")
        self.assertEqual(selected["value"]["kind"], "Squash2")
        self.assertEqual(selected["value"]["operand"]["kind"], "SelectRead")
        self.assertEqual(selected["value"]["operand"]["index"]["bits"],
                         "00000000000000000000000000000000")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dynamic_packed_slice_inside_array_cell_stays_loud(self):
        design = extract_source(
            "module top; bit [3:0][7:0] joe [0:9]; int i; "
            "initial joe[7][i +: 2] = joe[6][1:0]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_fixed_array_of_structs_copy_flattens_each_element(self):
        design = extract_source(
            "module top; typedef struct { int id; int value; } item_t; "
            "item_t source [0:1]; item_t target [0:1]; "
            "initial target = source; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["target[0].id", "target[0].value",
                          "target[1].id", "target[1].value"])
        self.assertEqual([a["value"]["operand"]["name"] for a in assigns],
                         ["source[0].id", "source[0].value",
                          "source[1].id", "source[1].value"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_fixed_array_of_structs_self_copy_stays_loud(self):
        design = extract_source(
            "module top; typedef struct { int id; int value; } item_t; "
            "item_t source [0:1]; initial source = source; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
