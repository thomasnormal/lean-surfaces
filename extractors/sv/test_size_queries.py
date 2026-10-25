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

    def test_empty_queue_literal_initializer_size_is_zero(self):
        design = lower(
            'module top; int q[$] = {}; initial $display("%0d", q.size()); endmodule')
        values = [node for node in nodes(design)
                  if node.get("zero_size_query")]
        self.assertEqual([(node["width"], node["bits"]) for node in values],
                         [(32, "0" * 32)])

    def test_procedural_empty_queue_initializer_size_is_zero(self):
        design = lower(
            'module top; initial begin int q[$] = {}; '
            '$display("%0d", q.size()); end endmodule')
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        values = [node for node in nodes(design)
                  if node.get("zero_size_query")]
        self.assertEqual([(node["width"], node["bits"]) for node in values],
                         [(32, "0" * 32)])

    def test_empty_queue_pop_front_returns_default_and_keeps_size(self):
        design = lower(
            'module top; initial begin int q[$]; int result; '
            '// q.pop_back() in prose is not a second operation.\n'
            'result = q.pop_front(); '
            'if (result === 0 && q.size() === 0) '
            '$display("PASS q.pop_front() result"); end endmodule')
        pops = [node for node in nodes(design)
                if node.get("queue_empty_pop")]
        sizes = [node for node in nodes(design)
                 if node.get("zero_size_query")]
        self.assertEqual([(node["queue_empty_pop"], node["bits"]) for node in pops],
                         [("pop_front", "0" * 32)])
        self.assertEqual(len(sizes), 1)
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_empty_queue_pop_back_returns_default(self):
        design = lower(
            'module top; int q[$]; int result; initial begin '
            'result = q.pop_back(); $display("%0d", result); end endmodule')
        pops = [node for node in nodes(design)
                if node.get("queue_empty_pop")]
        self.assertEqual([(node["queue_empty_pop"], node["bits"]) for node in pops],
                         [("pop_back", "0" * 32)])

    def test_discarded_empty_queue_pops_are_noops(self):
        design = lower(
            "module top; int q[$]; initial begin "
            "void'(q.pop_front()); void'(q.pop_back()); "
            'if (q.size() === 0) $display("PASS"); end endmodule')
        pops = [node for node in nodes(design)
                if node.get("queue_empty_pop_statement")]
        self.assertEqual([node["queue_empty_pop_statement"] for node in pops],
                         ["pop_front", "pop_back"])
        self.assertFalse(any(node.get("sv_kind") == "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_discarded_nonempty_queue_pop_stays_loud(self):
        design = lower(
            "module top; int q[$] = {1}; initial begin "
            "void'(q.pop_front()); end endmodule")
        self.assertFalse(any(node.get("queue_empty_pop_statement")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_empty_queue_pop_struct_returns_field_defaults(self):
        design = lower(
            'typedef struct { int id; bit [3:0] flags; } item_t; '
            'module top; item_t q[$]; item_t item; initial begin '
            'item.id = 99; item.flags = 4\'hf; item = q.pop_front(); '
            'if (q.size() == 0 && item.id == 0 && item.flags == 4\'h0) '
            '$display("PASS"); end endmodule')
        lowered = [node for node in nodes(design)
                   if node.get("queue_empty_struct_pop_lowered")]
        self.assertEqual(len(lowered), 1)
        self.assertEqual([stmt["target"]["name"] for stmt in lowered[0]["stmts"]],
                         ["item.id", "item.flags"])
        self.assertEqual([stmt["value"]["operand"]["bits"]
                          for stmt in lowered[0]["stmts"]],
                         ["0" * 32, "0000"])
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_nonempty_struct_queue_pop_stays_loud(self):
        design = lower(
            'typedef struct { int id; bit [3:0] flags; } item_t; '
            'module top; item_t q[$]; item_t item; initial begin '
            'q.push_back(\'{1, 4\'h2}); item = q.pop_front(); end endmodule')
        self.assertFalse(any(node.get("queue_empty_struct_pop_lowered")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_nonempty_queue_pop_stays_loud(self):
        design = lower(
            'module top; int q[$] = {1}; int result; initial begin '
            'result = q.pop_front(); end endmodule')
        self.assertFalse(any(node.get("queue_empty_pop")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_empty_associative_num_and_size_are_zero(self):
        design = lower(
            'module top; int values[string]; initial begin '
            '// values.num() in a comment is not a second query.\n'
            'if (values.num() === 0 && values.size() === 0) '
            '$display("PASS values.size()"); end endmodule')
        queries = [node for node in nodes(design)
                   if node.get("associative_empty_query")]
        self.assertEqual([node["associative_empty_query"] for node in queries],
                         ["num", "size"])
        self.assertTrue(all(node["bits"] == "0" * 32 for node in queries))
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_associative_write_before_num_stays_loud(self):
        design = lower(
            'module top; int values[string]; initial begin '
            'values["key"] = 1; if (values.num() === 1) $display("PASS"); '
            'end endmodule')
        self.assertFalse(any(node.get("associative_empty_query")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_empty_associative_first_and_last_return_zero(self):
        design = lower(
            'module top; int by_name[string]; int by_number[int]; '
            'string name; int key; int first_result, last_result; initial begin '
            'first_result = by_name.first(name); last_result = by_number.last(key); '
            'if (first_result === 0 && last_result === 0) $display("PASS"); '
            'end endmodule')
        endpoints = [node for node in nodes(design)
                     if node.get("associative_empty_endpoint")]
        self.assertEqual([node["associative_empty_endpoint"] for node in endpoints],
                         ["first", "last"])
        self.assertTrue(all(node["bits"] == "0" * 32 for node in endpoints))
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_empty_associative_endpoint_ignores_comments(self):
        design = lower(
            'module top; int values[string]; string key; int result; initial begin '
            '// values["comment"] = 1; values.next(key) is prose\n'
            'result = values.first(key); if (result === 0) $display("PASS"); '
            'end endmodule')
        self.assertTrue(any(node.get("associative_empty_endpoint") == "first"
                            for node in nodes(design)))

    def test_nonempty_associative_endpoint_stays_loud(self):
        design = lower(
            'module top; int values[string]; string key; int result; initial begin '
            'values["key"] = 1; result = values.first(key); end endmodule')
        self.assertFalse(any(node.get("associative_empty_endpoint")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_associative_endpoint_requires_named_index(self):
        design = lower(
            'module top; int values[string]; int result; initial '
            'result = values.first("key"); endmodule')
        self.assertFalse(any(node.get("associative_empty_endpoint")
                             for node in nodes(design)))

    def test_mailbox_type_mismatch_try_get_returns_negative(self):
        design = lower(
            'module top; mailbox box; string message; int result; initial begin '
            'box = new(); box.put(42); result = box.try_get(message); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("mailbox_type_mismatch_try_get")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "1" * 32)

    def test_mailbox_type_mismatch_alias_stays_loud(self):
        design = lower(
            'module top; mailbox box, alias_box; string message; int result; initial begin '
            'box = new(); alias_box = box; box.put(42); '
            'result = alias_box.try_get(message); end endmodule')
        self.assertFalse(any(node.get("mailbox_type_mismatch_try_get")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_empty_dynamic_bits_returns_zero(self):
        design = lower(
            'module top; int dyn[]; string text = ""; int result; initial begin '
            'result = $bits(dyn); if (result === 0 && $bits(text) === 0) '
            '$display("PASS"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("empty_dynamic_bits_query")]
        self.assertEqual(len(values), 2)
        self.assertTrue(all(node["bits"] == "0" * 32 for node in values))

    def test_allocated_dynamic_bits_stays_loud(self):
        design = lower(
            'module top; int dyn[]; int result; initial begin '
            'dyn = new[2]; result = $bits(dyn); end endmodule')
        self.assertFalse(any(node.get("empty_dynamic_bits_query")
                             for node in nodes(design)))

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

    def test_predefined_string_macro_assignment_is_literal_history(self):
        source = ('`define TEXT """\nmacro\ntext"""\n'
                  'module top; string s; initial begin s = `TEXT; '
                  '$display("%0d", s.len()); end endmodule')
        design = lower(source)
        values = [node for node in nodes(design)
                  if node.get("string_literal_length_query")]
        self.assertEqual([int(node["bits"], 2) for node in values], [11])

    def test_dynamic_string_assignment_before_len_stays_loud(self):
        design = lower(
            'module top; string s; string other; initial begin '
            's = other; $display("%0d", s.len()); end endmodule')
        self.assertFalse(any(node.get("string_literal_length_query")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_literal_string_atoi_scans_digits_and_underscores(self):
        design = lower(
            'module top; string s; int result; initial begin '
            's = "1_000x"; result = s.atoi(); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_atoi")]
        self.assertEqual([(node["width"], int(node["bits"], 2)) for node in values],
                         [(32, 1000)])

    def test_dynamic_string_atoi_stays_loud(self):
        design = lower(
            'module top; string s; string other; initial begin '
            's = other; $display("%0d", s.atoi()); end endmodule')
        self.assertFalse(any(node.get("string_literal_atoi")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_string_radix_methods_preserve_unknown_digits(self):
        design = lower(
            'module top; string h = "2x"; string b = "10x1"; '
            'string o = "7?"; logic [31:0] hv, bv, ov; initial begin '
            'hv = h.atohex(); bv = b.atobin(); ov = o.atooct(); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_radix")]
        self.assertEqual([node["string_literal_radix"] for node in values],
                         ["atohex", "atobin", "atooct"])
        self.assertEqual([node["bits"] for node in values], [
            "0" * 24 + "0010" + "xxxx",
            "0" * 28 + "10" + "x" + "1",
            "0" * 26 + "111" + "zzz",
        ])

    def test_string_radix_dynamic_and_invalid_digits_stay_loud(self):
        for source in (
                'module top; string s; string other; int result; initial begin '
                's = other; result = s.atohex(); end endmodule',
                'module top; string s = "8"; int result; initial '
                'result = s.atobin(); endmodule'):
            design = lower(source)
            self.assertTrue(any(str(node.get("sv_kind", "")).startswith("CallExpression")
                                for node in nodes(design)))

    def test_literal_string_compare_and_icompare_are_normalized(self):
        design = lower(
            'module top; string a; string b; initial begin a = "Alpha"; '
            'b = "alpha"; $display("%0d %0d", a.compare(b), a.icompare(b)); end endmodule')
        compare = [node for node in nodes(design)
                   if node.get("string_literal_compare")]
        icompare = [node for node in nodes(design)
                    if node.get("string_literal_icompare")]
        self.assertEqual([int(node["bits"], 2) for node in compare], [2**32 - 1])
        self.assertEqual([int(node["bits"], 2) for node in icompare], [0])

    def test_dynamic_string_compare_stays_loud(self):
        design = lower(
            'module top; string a; string b; initial begin a = b; '
            '$display("%0d", a.compare(b)); end endmodule')
        self.assertFalse(any(node.get("string_literal_compare")
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

    def test_written_string_getc_uses_latest_literal_assignment(self):
        design = lower(
            'module top; string s; initial begin s = "abc"; '
            '$display("%0d %0d %0d", s.getc(0), s.getc(3), s.getc(-1)); '
            's = "x"; $display("%0d", s.getc(0)); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_getc_query")]
        self.assertEqual([node["bits"] for node in values], [
            "01100001", "00000000", "00000000", "01111000"])

    def test_dynamic_string_assignment_getc_stays_loud(self):
        design = lower(
            'module top; string s; string other; initial begin s = other; '
            '$display("%0d", s.getc(0)); end endmodule')
        self.assertFalse(any(node.get("string_literal_getc_query")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_string_getc_rejects_non_ascii_alias_and_other_method(self):
        for source in (
                'module top; string s; initial begin s = "é"; '
                '$display("%0d", s.getc(0)); end endmodule',
                'module top; string s; string other; initial begin s = "abc"; '
                'other = s; $display("%0d", s.getc(0)); end endmodule',
                'module top; string s; initial begin s = "abc"; s.putc(65); '
                '$display("%0d", s.getc(0)); end endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_literal_getc_query")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") == "Unsupported"
                                for node in nodes(design)))

    def test_string_literal_queries_ignore_comments(self):
        design = lower(
            '/* s.getc(99) and s.len() in a comment are not runtime uses. */\n'
            'module top; string s = "a \\t b"; initial begin\n'
            '  // s.getc(98) and s.len() in line-comment prose\n'
            '  if (s.len() == 5 && s.getc(0) == 8\'h61 && '
            's.getc(2) == 8\'h09) $display("PASS");\n'
            'end endmodule')
        lengths = [node for node in nodes(design)
                   if node.get("string_literal_length_query")]
        getcs = [node for node in nodes(design)
                 if node.get("string_literal_getc_query")]
        self.assertEqual([int(node["bits"], 2) for node in lengths], [5])
        self.assertEqual([int(node["bits"], 2) for node in getcs], [97, 9])

    def test_escaped_newline_string_literal_queries_preserve_value(self):
        design = lower(
            'module top; string s; initial begin\n'
            '  // A quoted \\n escape precedes a line-continuation escape.\n'
            '  s = "AB.\\n\\\nCD";\n'
            '  if (s.len() == 6 && s.getc(0) == 8\'d65 && '
            's.getc(3) == 8\'d10 && s.getc(4) == 8\'d67) '
            '$display("PASS");\nend endmodule')
        lengths = [node for node in nodes(design)
                   if node.get("string_literal_length_query")]
        getcs = [node for node in nodes(design)
                 if node.get("string_literal_getc_query")]
        self.assertEqual([int(node["bits"], 2) for node in lengths], [6])
        self.assertEqual([int(node["bits"], 2) for node in getcs], [65, 10, 67])

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

    def test_positive_dynamic_allocation_size_is_exact(self):
        design = lower(
            'module top; int values[]; int result; initial begin '
            'values = new[4]; result = values.size(); '
            'if (result === 4) $display("PASS"); else $display("FAIL"); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("dynamic_array_literal_size")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "0" * 29 + "100")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_dynamic_allocation_size_with_other_method_stays_loud(self):
        design = lower(
            'module top; int values[]; initial begin values = new[1]; '
            'values.delete(); $display("%0d", values.size()); end endmodule')
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
        design = lower(
            'module top; mailbox box; int result; initial begin box = new(); '
            'box.put(1); box.get(result); $display("%0d", box.num()); end endmodule')
        self.assertTrue(any(node.get("mailbox_literal_get")
                            for node in nodes(design)))
        self.assertTrue(any(node.get("mailbox_literal_num")
                            for node in nodes(design)))

        design = lower(
            'module top; mailbox box; mailbox alias; initial begin box = new(); '
            'alias = box; $display("%0d", box.num()); end endmodule')
        self.assertFalse(any(node.get("mailbox_literal_num")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_mailbox_literal_fifo_get_writes_scalar_outputs(self):
        design = lower(
            'module top; mailbox box; int first, second; initial begin '
            'box = new(); box.put(10); box.put(20); box.get(first); '
            'box.get(second); end endmodule')
        gets = [node for node in nodes(design)
                if node.get("mailbox_literal_get")]
        self.assertEqual(len(gets), 2)
        self.assertEqual([node["value"]["bits"] for node in gets],
                         [format(value, "032b") for value in (10, 20)])
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_mailbox_literal_get_rejects_empty_or_dynamic_messages(self):
        for source in (
                'module top; mailbox box; int result; initial begin box = new(); '
                'box.get(result); end endmodule',
                'module top; mailbox box; int source, result; initial begin box = new(); '
                'box.put(source); box.get(result); end endmodule'):
            design = lower(source)
            self.assertTrue(any(node.get("sv_kind") ==
                                "ExpressionStatement:CallExpression"
                                for node in nodes(design)))

    def test_mailbox_literal_get_rejects_branching_sequence(self):
        design = lower(
            'module top; mailbox box; int result; initial begin box = new(); '
            'if (1) box.put(1); box.get(result); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
