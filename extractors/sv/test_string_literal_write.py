"""Literal-only string concatenation writes are inert at self-check time 0."""

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


class LiteralStringWrites(unittest.TestCase):
    def test_literal_sformatf_hex_assignment_replays_text(self):
        design = lower(
            'module top; string lower, upper; initial begin '
            'lower = $sformatf("%h", 32\'hDEAD_BEEF); '
            'upper = $sformatf("%H", 32\'hDEAD_BEEF); '
            'if (lower != upper) $display("FAIL"); $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            sum(node.get("string_source_write_noop", False) for node in nodes(design)),
            2,
        )

    def test_literal_sformatf_string_assignment_replays_ascii_text(self):
        design = lower(
            'module top; string source, copy, upper; initial begin '
            'source = "Hello"; copy = $sformatf("%s", source); '
            'upper = $sformatf("%S", "World"); '
            'if (copy != "Hello" || upper != "World") $display("FAIL"); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            sum(node.get("string_source_write_noop", False) for node in nodes(design)),
            2,
        )

    def test_dynamic_or_unsupported_sformatf_string_assignment_stays_loud(self):
        for source in (
                'module top; string value; string source; initial begin '
                'value = $sformatf("%s", source); end endmodule',
                'module top; string value; initial begin '
                'value = $sformatf("%d", "hello"); end endmodule',
                'module top; string value; initial begin '
                'value <= $sformatf("%s", "hello"); end endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_source_write_noop")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") in ("Unsupported", "Invalid")
                                or node.get("sv_kind") ==
                                "AssignmentExpression:target"
                                for node in nodes(design)))

    def test_literal_sformatf_character_assignment_replays_low_byte(self):
        design = lower(
            'module top; string lower, upper; initial begin '
            'lower = $sformatf("%c", 8\'h41); '
            'upper = $sformatf("%C", 8\'h42); '
            'if (lower != "A" || upper != "B") $display("FAIL"); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            sum(node.get("string_source_write_noop", False) for node in nodes(design)),
            2,
        )

    def test_dynamic_or_non_ascii_sformatf_character_assignment_stays_loud(self):
        for source in (
                'module top; string value; int x; initial begin '
                'value = $sformatf("%c", x); end endmodule',
                'module top; string value; initial begin '
                'value = $sformatf("%c", 8\'h00); end endmodule',
                'module top; string value; initial begin '
                'value = $sformatf("%c", 9\'h100); end endmodule',
                'module top; string value; initial begin '
                'value <= $sformatf("%c", 8\'h41); end endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_source_write_noop")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") in ("Unsupported", "Invalid")
                                or node.get("sv_kind") ==
                                "AssignmentExpression:target"
                                for node in nodes(design)))

    def test_literal_sformatf_binary_assignment_replays_packed_width(self):
        design = lower(
            'module top; string lower, upper; initial begin '
            'lower = $sformatf("%b", 8\'b00001010); '
            'upper = $sformatf("%B", 4\'b1010); '
            'if (lower != "00001010" || upper != "1010") $display("FAIL"); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            sum(node.get("string_source_write_noop", False) for node in nodes(design)),
            2,
        )

    def test_unknown_or_dynamic_sformatf_binary_assignment_stays_loud(self):
        for source in (
                'module top; string value; int x; initial begin '
                'value = $sformatf("%b", x); end endmodule',
                'module top; string value; initial begin '
                'value = $sformatf("%b", 4\'bx101); end endmodule',
                'module top; string value; initial begin '
                'value <= $sformatf("%B", 4\'b1010); end endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_source_write_noop")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") in ("Unsupported", "Invalid")
                                or node.get("sv_kind") ==
                                "AssignmentExpression:target"
                                for node in nodes(design)))

    def test_literal_sformatf_octal_assignment_replays_lowercase_text(self):
        design = lower(
            'module top; string lower, upper; initial begin '
            'lower = $sformatf("%o", 8\'h0A); '
            'upper = $sformatf("%O", 4\'b1010); '
            'if (lower != "12" || upper != "12") $display("FAIL"); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            sum(node.get("string_source_write_noop", False) for node in nodes(design)),
            2,
        )

    def test_unknown_or_dynamic_sformatf_octal_assignment_stays_loud(self):
        for source in (
                'module top; string value; int x; initial begin '
                'value = $sformatf("%o", x); end endmodule',
                'module top; string value; initial begin '
                'value = $sformatf("%o", 4\'bx101); end endmodule',
                'module top; string value; initial begin '
                'value <= $sformatf("%O", 4\'b1010); end endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_source_write_noop")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") in ("Unsupported", "Invalid")
                                or node.get("sv_kind") ==
                                "AssignmentExpression:target"
                                for node in nodes(design)))

    def test_literal_sformatf_decimal_assignment_replays_text(self):
        design = lower(
            'module top; string lower, upper, zero; initial begin '
            'lower = $sformatf("%d", 8\'d42); '
            'upper = $sformatf("%D", 8\'d7); '
            'zero = $sformatf("%0d", 8\'d0); '
            'if (lower != "42" || upper != "7" || zero != "0") '
            '$display("FAIL"); $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            sum(node.get("string_source_write_noop", False) for node in nodes(design)),
            3,
        )

    def test_unknown_or_dynamic_sformatf_decimal_assignment_stays_loud(self):
        for source in (
                'module top; string value; int x; initial begin '
                'value = $sformatf("%d", x); end endmodule',
                'module top; string value; initial begin '
                'value = $sformatf("%D", 4\'bx101); end endmodule',
                'module top; string value; initial begin '
                'value <= $sformatf("%0d", 8\'d42); end endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_source_write_noop")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") in ("Unsupported", "Invalid")
                                or node.get("sv_kind") ==
                                "AssignmentExpression:target"
                                for node in nodes(design)))

    def test_literal_sformatf_zero_width_binary_octal_assignment_replays_text(self):
        design = lower(
            'module top; string binary, binary_zero, octal, octal_zero; '
            'initial begin binary = $sformatf("%0b", 8\'b00001010); '
            'binary_zero = $sformatf("%0B", 8\'b00000000); '
            'octal = $sformatf("%0o", 8\'h0A); '
            'octal_zero = $sformatf("%0O", 8\'h00); '
            'if (binary != "1010" || binary_zero != "0" || '
            'octal != "12" || octal_zero != "0") $display("FAIL"); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            sum(node.get("string_source_write_noop", False) for node in nodes(design)),
            4,
        )

    def test_unknown_or_dynamic_zero_width_sformatf_assignment_stays_loud(self):
        for source in (
                'module top; string value; int x; initial begin '
                'value = $sformatf("%0b", x); end endmodule',
                'module top; string value; initial begin '
                'value = $sformatf("%0O", 4\'bx101); end endmodule',
                'module top; string value; initial begin '
                'value <= $sformatf("%0b", 4\'b1010); end endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_source_write_noop")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") in ("Unsupported", "Invalid")
                                or node.get("sv_kind") ==
                                "AssignmentExpression:target"
                                for node in nodes(design)))

    def test_dynamic_sformatf_string_assignment_stays_loud(self):
        design = lower(
            'module top; string value; int x; initial begin '
            'value = $sformatf("%h", x); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_literal_string_index_assignment_replays_history(self):
        design = lower(
            'module top; string value; initial begin value = "hello"; '
            'value[0] = "h"; if (value != "hello") $display("FAIL"); '
            'value[0] = "H"; if (value != "Hello") $display("FAIL"); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            [node.get("string_index_literal_write_noop") for node in nodes(design)
             if node.get("string_index_literal_write_noop")],
            [True, True],
        )

    def test_dynamic_or_invalid_string_index_writes_stay_loud(self):
        for source in (
                'module top; string value; int i; initial value[i] = "H"; endmodule',
                'module top; string value; initial value[4] = "H"; endmodule',
                'module top; string value; initial value[0] = "hi"; endmodule',
                'module top; string value; initial value[0] <= "H"; endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_index_literal_write_noop")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") in ("Unsupported", "Invalid")
                                or node.get("sv_kind") ==
                                "AssignmentExpression:target"
                                for node in nodes(design)))

    def test_zero_string_character_assignment_is_ignored(self):
        design = lower(
            'module top; string value; initial begin value = "hello"; '
            'value[1] = 0; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_null_char_write_noop")
                            for node in nodes(design)))

    def test_nul_string_character_assignment_is_ignored(self):
        design = lower(
            'module top; string value; initial begin value = "hello"; '
            'value[1] = "\\0"; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_null_char_write_noop")
                            for node in nodes(design)))

    def test_corpus_nul_string_character_assignment_is_ignored(self):
        import os
        from pathlib import Path
        corpus = os.environ.get("SV_TESTS_ROOT")
        if not corpus:
            self.skipTest("SV_TESTS_ROOT is unavailable")
        source = Path(corpus) / "chapter-6" / \
            "6.16--string-assign-zero-char-ignored-v3.sv"
        if not source.exists():
            self.skipTest("sv-tests-2 checkout is unavailable")
        design = lower(source.read_text())
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_null_char_write_noop")
                            for node in nodes(design)))

    def test_corpus_literal_string_index_assignment_is_admitted(self):
        import os
        from pathlib import Path
        corpus = os.environ.get("SV_TESTS_ROOT")
        if not corpus:
            self.skipTest("SV_TESTS_ROOT is unavailable")
        source = Path(corpus) / "chapter-6" / \
            "6.16--string-index-assign-from-literal.sv"
        if not source.exists():
            self.skipTest("sv-tests-2 checkout is unavailable")
        design = lower(source.read_text())
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            [node.get("string_index_literal_write_noop") for node in nodes(design)
             if node.get("string_index_literal_write_noop")],
            [True, True],
        )

    def test_corpus_literal_sformatf_string_assignment_is_admitted(self):
        import os
        from pathlib import Path
        corpus = os.environ.get("SV_TESTS_ROOT")
        if not corpus:
            self.skipTest("SV_TESTS_ROOT is unavailable")
        source = Path(corpus) / "chapter-21" / \
            "21.2.1.1--format-H-same-as-h.sv"
        if not source.exists():
            self.skipTest("sv-tests-2 checkout is unavailable")
        design = lower(source.read_text())
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertEqual(
            sum(node.get("string_source_write_noop", False) for node in nodes(design)),
            2,
        )

    def test_nonzero_or_dynamic_string_character_writes_stay_loud(self):
        for source in (
                'module top; string value; initial value[1] = 65; endmodule',
                'module top; string value; int i; initial value[i] = 0; endmodule',
                'module top; string value; initial value <= 0; endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_null_char_write_noop")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") in ("Unsupported", "Invalid")
                                or node.get("sv_kind") ==
                                "AssignmentExpression:target"
                                for node in nodes(design)))

    def test_literal_concatenation_write_is_inert(self):
        design = lower(
            'module top; string value; initial begin '
            'value = {"left", "-", "right"}; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_literal_concat_write_noop")
                            for node in nodes(design)))

    def test_dynamic_concatenation_write_stays_loud(self):
        design = lower(
            'module top; string value; string source; initial begin '
            'value = {source, "right"}; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_nonblocking_literal_concatenation_stays_loud(self):
        design = lower(
            'module top; string value; initial begin '
            'value <= {"left", "right"}; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_constant_literal_replication_write_is_inert(self):
        design = lower(
            'module top; string value; initial begin '
            'value = {3{"x"}}; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_literal_replication_write_noop")
                            for node in nodes(design)))

    def test_dynamic_literal_replication_write_stays_loud(self):
        design = lower(
            'module top; string value; int count; initial begin '
            'value = {count{"x"}}; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_source_pure_string_replication_write_and_display(self):
        design = lower(
            'module top; string source; string value; initial begin '
            'source = "ab"; value = {2{source}}; '
            '$display("%s", value); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_source_write_noop")
                            for node in nodes(design)))
        displays = [node for node in nodes(design)
                    if node.get("kind") == "SysCall"
                    and node.get("name") == "$display"]
        self.assertEqual(len(displays), 1)
        self.assertEqual(displays[0]["args"][0]["bits"],
                         "01100001011000100110000101100010")

    def test_source_pure_string_replication_requires_literal_history(self):
        for source in (
                'module top; string source; string value; initial begin '
                'value = {2{source}}; end endmodule',
                'module top; string source; string value; initial begin '
                'source <= "ab"; value = {2{source}}; end endmodule',
                'module top; string source; string value; bit c; initial begin '
                'if (c) source = "ab"; value = {2{source}}; end endmodule'):
            design = lower(source)
            self.assertIn("AssignmentExpression:target",
                          [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
