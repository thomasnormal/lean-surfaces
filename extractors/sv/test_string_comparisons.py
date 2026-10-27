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
