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

    def test_enum_type_key_and_scalar_default_pack_struct_cells(self):
        design = extract_source(
            "module top; typedef enum int {IDLE = 1, BUSY = 2} state_t; "
            "typedef struct packed { state_t state; int raw; } item_t; "
            "item_t items[0:1]; initial begin "
            "items = '{default: '{state_t: BUSY, default: 7}}; "
            "if (items[0].state == BUSY && items[0].raw == 7 && "
            "items[1].state == BUSY && items[1].raw == 7) "
            "$display(\"PASS\"); end endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["items[0]", "items[1]"])
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

    def test_destination_alias_is_snapshotted(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1]; "
            "initial value = '{value[1], 8'h34}; endmodule")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("array_pattern_snapshot")
                            for node in nodes(design)))

    def test_exact_blocking_self_copy_is_a_noop(self):
        design = extract_source(
            "module top; int value [0:1]; initial value = value; endmodule")
        self.assertTrue(any(node.get("fixed_array_self_copy_noop")
                            for node in nodes(design)))
        for source in (
                "module top; int value [0:1]; initial value <= value; endmodule",
                "module top; int value [0:1]; initial value[0:1] = value[0:1]; endmodule"):
            design = extract_source(source)
            self.assertTrue(any(node.get("sv_kind") == "AssignmentExpression:target"
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
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             and node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_postincrement_index_updates_after_write(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1]; int index; "
            "initial begin value[index++] = 8'h12; end endmodule")
        blocks = [node for node in nodes(design)
                  if node.get("kind") == "Block"
                  and node.get("postindexed_array_write_lowered")]
        self.assertEqual(len(blocks), 1)
        self.assertEqual(blocks[0]["stmts"][-1]["target"]["name"], "index")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             and node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_dist_uniform_dynamic_index_updates_seed_and_cell(self):
        design = extract_source(
            "module top; integer seed; integer value[0:1]; int index; "
            "initial begin seed = 9001; index = 0; "
            "value[index] = $dist_uniform(seed, 0, 1000); "
            "if (value[0] == 144) $display(\"PASS\"); end endmodule")
        calls = [node for node in nodes(design)
                 if node.get("kind") == "DistUniformAssign"]
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0]["target"], "value[0]")
        self.assertEqual(calls[0]["seed"], "seed")
        self.assertTrue(any(node.get("dist_uniform_array_write_lowered")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dist_uniform_scalar_assignment_updates_seed(self):
        design = extract_source(
            "module top; integer seed; integer value; "
            "initial begin seed = 9001; "
            "value = $dist_uniform(seed, 0, 1000); "
            "if (value == 144 && seed != 9001) $display(\"PASS\"); "
            "end endmodule")
        calls = [node for node in nodes(design)
                 if node.get("kind") == "DistUniformAssign"]
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]["target"], "value")
        self.assertEqual(calls[0]["seed"], "seed")
        self.assertTrue(calls[0]["dist_uniform_scalar_write"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dist_uniform_scalar_assignment_accepts_literal_bounds(self):
        design = extract_source(
            "module top; integer seed; integer value; "
            "initial begin seed = 42; "
            "value = $dist_uniform(seed, 10, 20); "
            "if (value >= 10 && value <= 20) $display(\"PASS\"); "
            "end endmodule")
        calls = [node for node in nodes(design)
                 if node.get("kind") == "DistUniformAssign"]
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]["low"], 10)
        self.assertEqual(calls[0]["high"], 20)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dist_uniform_scalar_assignment_accepts_signed_literal_bounds(self):
        design = extract_source(
            "module top; integer seed; integer value; "
            "initial begin seed = 42; "
            "value = $dist_uniform(seed, -50, 50); "
            "if (value >= -50 && value <= 50) $display(\"PASS\"); "
            "end endmodule")
        calls = [node for node in nodes(design)
                 if node.get("kind") == "DistUniformAssign"]
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]["low"], -50)
        self.assertEqual(calls[0]["high"], 50)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dist_uniform_scalar_assignment_accepts_immutable_literal_bound_history(self):
        design = extract_source(
            "module top; integer seed, value, low, high; "
            "initial begin seed = 42; low = 1; high = 10; "
            "value = $dist_uniform(seed, low, high); end endmodule")
        calls = [node for node in nodes(design)
                 if node.get("kind") == "DistUniformAssign"]
        self.assertEqual(len(calls), 1)
        self.assertEqual((calls[0]["low"], calls[0]["high"]), (1, 10))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_dist_uniform_scalar_assignment_rejects_reassigned_bound_history(self):
        design = extract_source(
            "module top; integer seed, value, low, high; "
            "initial begin seed = 42; low = 1; high = 10; "
            "low = 2; value = $dist_uniform(seed, low, high); end endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_dist_uniform_scalar_assignment_rejects_bound_write_after_call(self):
        design = extract_source(
            "module top; integer seed, value, low, high; "
            "initial begin seed = 42; low = 1; high = 10; "
            "value = $dist_uniform(seed, low, high); low = 2; end endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "CallExpression"
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

    def test_out_of_bounds_struct_read_uses_member_defaults(self):
        design = extract_source(
            "module top; typedef struct { int a = 42; int b; } pair_t; "
            "pair_t arr[3]; pair_t value; initial begin value = arr[10]; "
            "if (value.a === 42 && value.b === 0) $display(\"PASS\"); "
            "end endmodule")
        blocks = [node for node in nodes(design)
                  if node.get("kind") == "Block"
                  and node.get("unpacked_struct_oob_lowered")]
        self.assertEqual(len(blocks), 1)
        self.assertEqual([stmt["target"]["name"] for stmt in blocks[0]["stmts"]],
                         ["value.a", "value.b"])
        self.assertEqual(blocks[0]["stmts"][0]["value"]["operand"]["bits"],
                         format(42, "032b"))
        self.assertEqual(blocks[0]["stmts"][1]["value"]["operand"]["bits"],
                         "0" * 32)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_out_of_bounds_integral_array_reads_use_element_defaults(self):
        design = extract_source(
            "module top; typedef enum logic [1:0] { RED=2'b00, "
            "GREEN=2'b01, BLUE=2'b10 } color_t; "
            "bit [7:0] bits [0:3]; logic [7:0] logic_values [0:3]; "
            "color_t colors [0:3]; logic [7:0] result; "
            "initial begin result = bits[10]; result = logic_values[10]; "
            "result = colors[10]; end endmodule")
        reads = [node for node in nodes(design)
                 if node.get("unpacked_array_oob_read")]
        self.assertEqual(len(reads), 3)
        self.assertEqual([node["bits"] for node in reads],
                         ["0" * 8, "x" * 8, "x" * 2])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_out_of_bounds_array_reads_keep_scalar_boundaries(self):
        design = extract_source(
            "module top; logic scalar; int result; "
            "initial begin result = scalar[0]; end endmodule")
        self.assertFalse(any(node.get("unpacked_array_oob_read")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") ==
                            "ElementSelectExpression:source-type"
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

    def test_conditional_array_self_alias_merges_cells(self):
        design = extract_source(
            "module top; logic [7:0] source [0:1]; logic [7:0] value [0:1]; "
            "logic choose; initial begin value = choose ? value : source; "
            "end endmodule")
        values = [node for node in nodes(design) if node.get("kind") == "Ternary"]
        self.assertEqual(len(values), 2)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_conditional_array_self_alias_nonblocking_stays_loud(self):
        design = extract_source(
            "module top; logic [7:0] source [0:1]; logic [7:0] value [0:1]; "
            "logic choose; initial value <= choose ? value : source; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
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

    def test_dynamic_subarray_source_copy_expands_finite_rows(self):
        design = extract_source(
            "module top; int source [0:1][0:2]; int row [0:2]; int i; "
            "initial row = source[i]; endmodule")
        branches = [node for node in nodes(design)
                    if node.get("fixed_array_dynamic_subarray_read_copy_lowered")]
        self.assertEqual(len(branches), 1)
        self.assertEqual(
            [stmt["value"]["operand"]["name"]
             for stmt in branches[0]["else"]["then"]["stmts"]],
            ["source[1][0]", "source[1][1]", "source[1][2]"])

    def test_dynamic_array_constant_oob_write_is_noop(self):
        design = extract_source(
            "module top; bit values[]; initial begin values = new[2]; "
            "values[4] = 1'b1; $display(\"PASS\"); end endmodule")
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("kind") == "Empty" and
                            node.get("oob_write_noop")
                            for node in nodes(design)))

    def test_subarray_self_copy_is_a_noop(self):
        design = extract_source(
            "module top; int value [0:1][0:2]; "
            "initial value[0] = value[0]; endmodule")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("fixed_array_subarray_self_copy_noop")
                            for node in nodes(design)))

    def test_nonblocking_subarray_self_copy_stays_loud(self):
        design = extract_source(
            "module top; int value [0:1][0:2]; "
            "initial value[0] <= value[0]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_disjoint_subarray_copy_snapshots_distinct_rows(self):
        design = extract_source(
            "module top; int value [0:1][0:2]; "
            "initial begin value[0] = '{1, 2, 3}; "
            "value[1] = '{4, 5, 6}; value[0] = value[1]; "
            "if (value[0][0] == 4 && value[0][2] == 6) "
            "$display(\"PASS\"); end endmodule")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        lowered = [node for node in nodes(design)
                   if node.get("fixed_array_subarray_copy_lowered")]
        self.assertEqual(len(lowered), 1)
        self.assertEqual(
            [stmt["target"]["name"] for stmt in lowered[0]["stmts"]],
            ["value[0][0]", "value[0][1]", "value[0][2]"])

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

    def test_dynamic_packed_slice_inside_array_cell_uses_flattened_offset(self):
        design = extract_source(
            "module top; bit [3:0][7:0] joe [0:9]; int i; "
            "initial joe[7][i +: 2] = joe[6][1:0]; endmodule")
        targets = [node for node in nodes(design)
                   if node.get("kind") == "SelectTarget"]
        self.assertEqual(len(targets), 1)
        target = targets[0]
        self.assertEqual(target["value"]["name"], "joe[7]")
        self.assertEqual(target["width"], 16)
        self.assertFalse(target["descending"])
        self.assertTrue(target["index_signed"])
        self.assertEqual(target["index"]["kind"], "Binary")
        self.assertEqual(target["index"]["op"], "*")
        self.assertEqual(target["index"]["right"]["bits"],
                         "00000000000000000000000000001000")

    def test_dynamic_packed_slice_inside_array_cell_reads_and_writes(self):
        design = extract_source(
            "module top; bit [3:0][7:0] source [0:0]; "
            "bit [3:0][7:0] target [0:0]; int i; "
            "initial begin source[0] = 32'h11223344; target[0] = 0; "
            "i = 1; target[0][i +: 2] = source[0][1:0]; "
            "if (target[0][i +: 2] === 16'h3344) $display(\"PASS\"); "
            "end endmodule")
        selected = [node for node in nodes(design)
                    if node.get("kind") in ("SelectTarget", "SelectRead")]
        self.assertGreaterEqual(len(selected), 2)
        self.assertTrue(all(node["value"]["name"] in ("source[0]", "target[0]")
                            for node in selected))

    def test_dynamic_descending_packed_slice_inside_array_cell_keeps_direction(self):
        design = extract_source(
            "module top; bit [3:0][7:0] joe [0:9]; int i; "
            "initial joe[7][i -: 2] = joe[6][1:0]; endmodule")
        target = next(node for node in nodes(design)
                      if node.get("kind") == "SelectTarget")
        self.assertTrue(target["descending"])
        self.assertEqual(target["index"]["kind"], "Binary")
        self.assertEqual(target["index"]["op"], "-")

    def test_dynamic_packed_slice_inside_array_cell_ascending_stays_loud(self):
        design = extract_source(
            "module top; bit [0:3][7:0] joe [0:9]; int i; "
            "initial joe[7][i +: 2] = joe[6][1:0]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
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

    def test_fixed_array_of_structs_self_copy_is_a_noop(self):
        design = extract_source(
            "module top; typedef struct { int id; int value; } item_t; "
            "item_t source [0:1]; initial source = source; endmodule")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("fixed_array_struct_self_copy_noop")
                            for node in nodes(design)))

    def test_nonblocking_fixed_array_of_structs_self_copy_stays_loud(self):
        design = extract_source(
            "module top; typedef struct { int id; int value; } item_t; "
            "item_t source [0:1]; initial source <= source; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_struct_fixed_array_field_element_windows(self):
        design = extract_source(
            "module top; typedef struct { logic [3:0] values [0:1]; } T; "
            "T value; int index; initial begin "
            "value.values[0] = 4'h1; value.values[1] = 4'h2; "
            "index = 1; value.values[index] = 4'h3; "
            "if (value.values[0] == 4'h1 && value.values[1] == 4'h3) "
            "$display(\"PASS\"); end endmodule")
        module = design["modules"][0]
        self.assertEqual([decl["name"] for decl in module["decls"]
                          if decl.get("kind") == "Var"],
                         ["value.values[0]", "value.values[1]", "index"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_struct_fixed_array_field_pattern_write(self):
        design = extract_source(
            "module top; typedef struct { int values [0:1]; } T; T value; "
            "initial begin value.values = '{4, 8}; "
            "if (value.values[0] == 4 && value.values[1] == 8) "
            "$display(\"PASS\"); end endmodule")
        module = design["modules"][0]
        self.assertEqual(
            [decl["name"] for decl in module["decls"] if decl.get("kind") == "Var"],
            ["value.values[0]", "value.values[1]"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_struct_fixed_array_field_pattern_self_read_stays_loud(self):
        design = extract_source(
            "module top; typedef struct { int values [0:1]; } T; T value; "
            "initial value.values = '{value.values[0], 8}; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_unpacked_struct_array_field_default_recurses(self):
        design = extract_source(
            "module top; typedef struct { int scalar; int values [0:2]; } T; "
            "T value; initial value = '{default:7}; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value.scalar", "value.values[0]",
                          "value.values[1]", "value.values[2]"])
        self.assertEqual([a["value"].get("operand", a["value"]).get("bits")
                          for a in assigns], [format(7, "032b")] * 4)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_unpacked_struct_array_field_keyed_default(self):
        design = extract_source(
            "module top; typedef struct { int header; int payload [0:2]; } T; "
            "T value; initial value = '{header:12, default:7}; endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value.header", "value.payload[0]",
                          "value.payload[1]", "value.payload[2]"])
        self.assertEqual([a["value"].get("operand", a["value"]).get("bits")
                          for a in assigns],
                         [format(12, "032b")] + [format(7, "032b")] * 3)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_unpacked_struct_array_field_pattern_alias_stays_loud(self):
        design = extract_source(
            "module top; typedef struct { int scalar; int values [0:1]; } T; "
            "T value; initial value = '{scalar:value.scalar, default:7}; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_unpacked_struct_array_enum_type_key_default(self):
        design = extract_source(
            "module top; typedef enum int {IDLE=1, BUSY=2} state_t; "
            "typedef struct { state_t states [0:1]; int raw [0:1]; } T; "
            "T value; initial value = '{default: '{state_t: BUSY, default: 7}}; "
            "endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual([a["target"]["name"] for a in assigns],
                         ["value.states[0]", "value.states[1]",
                          "value.raw[0]", "value.raw[1]"])
        self.assertEqual([a["value"].get("bits") or
                          a["value"].get("operand", {}).get("bits")
                          for a in assigns],
                         [format(2, "032b")] * 2 + [format(7, "032b")] * 2)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
