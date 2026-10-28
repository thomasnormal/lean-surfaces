"""Discarded pure string transformations retain their literal history gate."""
from pathlib import Path
import unittest

import extract
from test_bit_queries import lower, nodes
from test_division import symbolic


REPO = Path(__file__).resolve().parents[2]


def fixture():
    return lower((REPO / "Examples/system-verilog/string_transform_statements/"
                  "string_transform_statements.sv").read_text())


class StringTransformStatements(unittest.TestCase):
    def test_case_and_substr_queries_are_discarded(self):
        design = fixture()
        unsupported = [node for node in nodes(design)
                       if node.get("kind") == "Unsupported"]
        self.assertEqual(unsupported, [])
        self.assertEqual(
            [node.get("string_case_statement") for node in nodes(design)
             if node.get("string_case_statement")],
            ["toupper", "tolower"],
        )
        self.assertEqual(
            [node.get("string_substr_statement") for node in nodes(design)
             if node.get("string_substr_statement")],
            ["substr", "substr"],
        )

    def test_dynamic_and_effectful_string_forms_stay_loud(self):
        source = (
            'module top; string s; string other; initial begin '
            's = other; s.toupper(); s.putc(0, 65); end endmodule'
        )
        design = lower(source)
        walls = [node.get("sv_kind") for node in nodes(design)
                 if node.get("kind") == "Unsupported"]
        self.assertGreaterEqual(walls.count("ExpressionStatement:CallExpression"), 2)

    def test_literal_case_value_position_is_reconstructed(self):
        source = (
            'module top; string s = "abc"; string out; '
            'initial begin out = s.toupper(); '
            'if (out == "ABC") $display("PASS"); end endmodule'
        )
        design = lower(source)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_source_pure_case_value_position_replays_copy(self):
        source = (
            'module top; string s, other, out; '
            'initial begin other = "abc"; s = other; '
            'out = s.toupper(); if (out == "ABC") $display("PASS"); end endmodule'
        )
        design = lower(source)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_putc_replays_ascii_and_low_byte_history(self):
        source = (
            'module top; string s; initial begin s = "abc"; '
            's.putc(1, "X"); if (s == "aXc" && s.getc(1) == 8\'h58) '
            '$display("PASS"); end endmodule'
        )
        design = lower(source)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        source = (
            'module top; string s; initial begin s = "abc"; '
            's.putc(1, 32\'h144); if (s == "aDc") $display("PASS"); '
            'end endmodule'
        )
        design = lower(source)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_putc_ignored_and_out_of_range_history(self):
        source = (
            'module top; string s; initial begin s = "abc"; '
            's.putc(1, 0); s.putc(3, "X"); s.putc(-1, "Y"); '
            'if (s == "abc") $display("PASS"); end endmodule'
        )
        design = lower(source)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_putc_length_index_is_the_defined_out_of_range_noop(self):
        source = (
            'module top; string s; initial begin s = "abc"; '
            's.putc(s.len(), "X"); if (s == "abc") $display("PASS"); '
            'end endmodule'
        )
        design = lower(source)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_putc_dynamic_timed_and_non_ascii_forms_stay_loud(self):
        sources = (
            'module top; string s; int i; initial begin s = "abc"; '
            's.putc(i, "X"); end endmodule',
            'module top; string s; initial begin s = "abc"; '
            '#1 s.putc(1, "X"); end endmodule',
            'module top; string s; initial begin s = "abc"; '
            's.putc(1, "é"); end endmodule',
        )
        for source in sources:
            with self.subTest(source=source):
                design = lower(source)
                self.assertTrue(any(
                    node.get("sv_kind") == "ExpressionStatement:CallExpression"
                    for node in nodes(design)
                    if node.get("kind") == "Unsupported"))

    def test_symbolic_mode_stays_loud(self):
        design = symbolic(
            'module divider; string s = "abc"; '
            'initial begin s.toupper(); s.substr(1, 2); end endmodule'
        )
        walls = [node.get("sv_kind") for node in nodes(design)
                 if node.get("kind") == "Unsupported"]
        self.assertGreaterEqual(walls.count("ExpressionStatement:CallExpression"), 2)


if __name__ == "__main__":
    unittest.main()
