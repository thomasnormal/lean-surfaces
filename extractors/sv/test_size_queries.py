"""Zero-size queries on untouched queue and dynamic-array declarations."""

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


class SizeQueries(unittest.TestCase):
    def test_uninitialized_queue_size_is_zero(self):
        design = lower(
            'module top; int q[$]; initial $display("%0d", q.size()); endmodule')
        values = [node for node in nodes(design)
                  if node.get("zero_size_query")]
        self.assertEqual([(node["width"], node["bits"]) for node in values],
                         [(32, "0" * 32)])

    def test_uninitialized_dynamic_array_size_is_zero(self):
        design = lower(
            'module top; int values[]; initial $display("%0d", values.size()); endmodule')
        self.assertTrue(any(node.get("zero_size_query") for node in nodes(design)))

    def test_mutated_queue_size_stays_loud(self):
        design = lower(
            'module top; int q[$]; initial begin q.push_back(1); '
            '$display("%0d", q.size()); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_initialized_queue_size_stays_loud(self):
        design = lower(
            'module top; int q[$] = {1}; initial $display("%0d", q.size()); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_uninitialized_string_len_is_zero(self):
        design = lower(
            'module top; string s; initial $display("%0d", s.len()); endmodule')
        self.assertTrue(any(node.get("zero_string_length_query")
                            for node in nodes(design)))

    def test_literal_string_len_is_exact(self):
        design = lower(
            'module top; initial begin string s = "hello"; '
            '$display("%0d", s.len()); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_length_query")]
        self.assertEqual([(node["width"], node["bits"]) for node in values],
                         [(32, format(5, "032b"))])

    def test_literal_string_write_before_len_stays_loud(self):
        design = lower(
            'module top; string s = "hello"; initial begin s = "x"; '
            '$display("%0d", s.len()); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_length_query")]
        self.assertEqual([(node["width"], int(node["bits"], 2)) for node in values],
                         [(32, 1)])

    def test_literal_string_assignment_history_tracks_each_len(self):
        design = lower(
            'module top; string s; initial begin s = "hello"; '
            '$display("%0d", s.len()); s = "xy"; '
            '$display("%0d", s.len()); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_length_query")]
        self.assertEqual([int(node["bits"], 2) for node in values], [5, 2])

    def test_dynamic_string_assignment_before_len_stays_loud(self):
        design = lower(
            'module top; string s; string other; initial begin '
            's = other; $display("%0d", s.len()); end endmodule')
        self.assertFalse(any(node.get("string_literal_length_query")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_literal_string_getc_returns_ascii_and_zero_bounds(self):
        design = lower(
            'module top; string s = "abc"; initial begin '
            '$display("%0d %0d %0d", s.getc(0), s.getc(10), s.getc(-1)); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_getc_query")]
        self.assertEqual([(node["width"], node["bits"]) for node in values], [
            (8, "01100001"), (8, "00000000"), (8, "00000000")])

    def test_dynamic_string_getc_index_stays_loud(self):
        design = lower(
            'module top; string s = "abc"; int i = 0; '
            'initial $display("%0d", s.getc(i)); endmodule')
        self.assertFalse(any(node.get("string_literal_getc_query")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_written_string_getc_stays_loud(self):
        design = lower(
            'module top; string s = "abc"; initial begin s = "x"; '
            '$display("%0d", s.getc(0)); end endmodule')
        self.assertFalse(any(node.get("string_literal_getc_query")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_non_ascii_string_getc_stays_loud(self):
        design = lower(
            'module top; string s = "é"; '
            'initial $display("%0d", s.getc(0)); endmodule')
        self.assertFalse(any(node.get("string_literal_getc_query")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_single_literal_continuous_net_driver_is_time_zero_assignment(self):
        design = lower(
            'module top; wire y; assign y = 1\'b1; '
            'initial $display("%0d", y); endmodule')
        lowered = [node for node in nodes(design)
                   if node.get("continuous_constant_lowered")]
        self.assertEqual(len(lowered), 2)
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_multiple_literal_continuous_net_drivers_resolve(self):
        design = lower(
            'module top; wire y; assign y = 1\'b1; assign y = 1\'b0; '
            'initial $display("%0d", y); endmodule')
        self.assertFalse(any(node.get("continuous_constant_lowered")
                             for node in nodes(design)))
        resolved = [node for node in nodes(design)
                    if node.get("continuous_static_resolution")
                    and node.get("body", {}).get("kind") == "BlockingAssign"]
        self.assertEqual(len(resolved), 1)
        self.assertEqual(resolved[0]["body"]["value"]["bits"], "x")

    def test_dynamic_continuous_net_driver_stays_loud(self):
        design = lower(
            'module top; logic a; wire y; assign y = a; '
            'initial $display("%0d", y); endmodule')
        self.assertFalse(any(node.get("continuous_constant_lowered")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("kind") == "Assign" for node in nodes(design)))

    def test_literal_continuous_variable_driver_lowers(self):
        design = lower(
            'module top; logic y; assign y = 1\'b1; '
            'initial $display("%0d", y); endmodule')
        lowered = [node for node in nodes(design)
                   if node.get("continuous_constant_lowered")]
        self.assertEqual(len(lowered), 2)
        self.assertEqual(lowered[0]["body"]["target"]["name"], "y")

    def test_written_string_len_stays_loud(self):
        design = lower(
            'module top; string s; initial begin s = "x"; '
            '$display("%0d", s.len()); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_length_query")]
        self.assertEqual([(node["width"], int(node["bits"], 2)) for node in values],
                         [(32, 1)])

    def test_empty_queue_write_keeps_size_zero(self):
        design = lower(
            'module top; int q[$]; initial begin q = {}; '
            '$display("%0d", q.size()); end endmodule')
        self.assertTrue(any(node.get("zero_size_query") for node in nodes(design)))

    def test_empty_string_write_keeps_len_zero(self):
        design = lower(
            'module top; string s; initial begin s = ""; '
            '$display("%0d", s.len()); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_length_query")]
        self.assertEqual([(node["width"], int(node["bits"], 2)) for node in values],
                         [(32, 0)])

    def test_nonempty_write_before_query_stays_loud(self):
        design = lower(
            'module top; int q[$]; initial begin q = {}; q.push_back(1); '
            '$display("%0d", q.size()); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_zero_dynamic_allocation_keeps_size_zero(self):
        design = lower(
            'module top; int values[]; initial begin values = new[0]; '
            '$display("%0d", values.size()); end endmodule')
        self.assertTrue(any(node.get("zero_size_query") for node in nodes(design)))

    def test_positive_dynamic_allocation_size_stays_loud(self):
        design = lower(
            'module top; int values[]; initial begin values = new[1]; '
            '$display("%0d", values.size()); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_unbounded_mailbox_literal_puts_report_exact_num(self):
        design = lower(
            'module top; mailbox box; initial begin box = new(); '
            'box.put(7); box.put(8); $display("%0d", box.num()); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("mailbox_literal_num")]
        self.assertEqual([(node["width"], int(node["bits"], 2)) for node in values],
                         [(32, 2)])
        self.assertEqual(sum(node.get("mailbox_literal_put", False)
                             for node in nodes(design)), 2)

    def test_mailbox_literal_sequence_rejects_other_methods_and_aliases(self):
        for source in (
                'module top; mailbox box; int result; initial begin box = new(); '
                'box.put(1); box.get(result); $display("%0d", box.num()); end endmodule',
                'module top; mailbox box; mailbox alias; initial begin box = new(); '
                'alias = box; $display("%0d", box.num()); end endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("mailbox_literal_num")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") == "Unsupported"
                                for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
