"""IEEE 1800 §11.10.2 source-pure string comparisons."""
import unittest

from test_bit_queries import lower, nodes


class StringComparisons(unittest.TestCase):
    def test_named_literal_history_folds_equality_and_order(self):
        design = lower(
            'module top; string a, b, c; initial begin '
            'a = "apple"; b = "apple"; c = "banana"; '
            'if (a == b && a != c && a < c && a <= b && c > a && '
            'c >= b && a === b && a !== c) $display("PASS"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_compare")]
        self.assertEqual([value["bits"] for value in values],
                         ["1", "1", "1", "1", "1", "1", "1", "1"])

    def test_string_literal_comparison_folds_without_storage(self):
        design = lower(
            'module top; initial if ("foo" != "bar" && "a" < "b") '
            '$display("PASS"); endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_compare")]
        self.assertEqual([value["bits"] for value in values], ["1", "1"])

    def test_case_transform_comparison_replays_literal_history(self):
        design = lower(
            'module top; string text; initial begin '
            'text = "A1_b-?Z"; '
            'if (text.toupper() == "A1_B-?Z" && '
            'text.tolower() == "a1_b-?z") $display("PASS"); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_compare")]
        self.assertEqual([value["bits"] for value in values], ["1", "1"])

    def test_named_string_concatenation_replays_comparison_and_display(self):
        design = lower(
            'module top; string a, b, result; initial begin '
            'a = "Hello"; b = " World"; result = {a, b}; '
            'if (result == "Hello World") $display("%s", result); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_compare")]
        self.assertEqual([value["bits"] for value in values], ["1"])
        displays = [node for node in nodes(design)
                    if node.get("string_source_display")]
        self.assertEqual(len(displays), 1)

    def test_source_pure_string_query_initializers_replay_comparisons(self):
        design = lower(
            'module top; initial begin '
            'string source = "Hello"; '
            'string upper = source.toupper(); '
            'string lower = source.tolower(); '
            'string middle = source.substr(1, 3); '
            'string formatted = $sformatf("Value: %0d", 42); '
            'if (upper == "HELLO" && lower == "hello" && '
            'middle == "ell" && formatted == "Value: 42") '
            '$display("PASS"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_compare")]
        self.assertEqual(len(values), 4)
        self.assertFalse(any(node.get("sv_kind") ==
                             "VariableSymbol:2state"
                             for node in nodes(design)))

    def test_source_pure_string_query_observations_replay_len_and_substr(self):
        design = lower(
            'module top; initial begin '
            'string source = "Hello"; string type_name; '
            'type_name = $typename(int); '
            'if (source.len() == 5 && source.substr(1, 3) == "ell" && '
            'type_name.len() == 3 && type_name.substr(0, 2) == "int") '
            '$display("PASS"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_compare")]
        self.assertEqual(len(values), 2)
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_source_pure_string_compare_queries_replay_history(self):
        design = lower(
            'module top; initial begin '
            'string source = "Abc"; string type_name = $typename(int); '
            'string upper; upper = source.toupper(); '
            'if (type_name.compare("int") == 0 && '
            'upper.icompare("abc") == 0 && source.compare("Abc") == 0) '
            '$display("PASS"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_literal_compare")
                  or node.get("string_literal_icompare")]
        self.assertEqual(len(values), 3)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_source_pure_string_alias_replays_compare_queries(self):
        design = lower(
            'module top; string source = "abc"; string copy; '
            'initial begin copy = source; '
            'if (copy.compare("abc") == 0) $display("PASS"); '
            'end endmodule')
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_literal_compare")
                            for node in nodes(design)))

    def test_string_query_observations_replay_concat_and_replication(self):
        design = lower(
            'module top; initial begin '
            'string left = "Hi"; string right = "!"; string joined; '
            'string repeated; joined = {left, right}; repeated = {2{left}}; '
            'if (joined.len() == 3 && joined.substr(0, 1) == "Hi" && '
            'repeated.len() == 4 && repeated.compare("HiHi") == 0) '
            '$display("PASS"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("string_compare")]
        self.assertEqual(len(values), 1)
        self.assertEqual(
            len([node for node in nodes(design)
                 if node.get("string_literal_length_query")]), 2)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_string_query_observations_ignore_nul_character_writes(self):
        design = lower(
            'module top; initial begin string text = "abc"; '
            'text[1] = 0; '
            'if (text.len() == 3 && text.compare("abc") == 0) '
            '$display("PASS"); end endmodule')
        self.assertEqual(
            len([node for node in nodes(design)
                 if node.get("string_literal_length_query")]), 1)
        self.assertEqual(
            len([node for node in nodes(design)
                 if node.get("string_literal_compare")]), 1)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_computed_controlled_and_timed_histories_stay_loud(self):
        for source in (
                'module top; string a, b; initial begin '
                'a = "a"; b = {"b"}; if (a == b) $display("PASS"); '
                'end endmodule',
                'module top; string a, b; initial begin '
                'if (1) a = "a"; b = "b"; if (a == b) $display("PASS"); '
                'end endmodule',
                'module top; string a, b; initial begin '
                'a = "a"; #1 b = "b"; if (a == b) $display("PASS"); '
                'end endmodule',
                'module top; string a, b; initial begin '
                'a = "hé"; b = "hé"; if (a == b) $display("PASS"); '
                'end endmodule'):
            self.assertIn("NamedValueExpression:2state", nodes_to_kinds(lower(source)))


def nodes_to_kinds(value):
    return [node.get("sv_kind") for node in nodes(value)
            if node.get("sv_kind")]


if __name__ == "__main__":
    unittest.main()
