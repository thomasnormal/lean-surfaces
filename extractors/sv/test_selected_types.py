"""Packed selected reads preserve the whole source's state kind."""
import unittest

from test_packed_assignment_targets import extract_source, nodes


class SelectedTypes(unittest.TestCase):
    def read(self, declaration, expression="value[index +: 4]"):
        design = extract_source(
            "module top; " + declaration + " integer index; logic [3:0] result; "
            "initial result = " + expression + "; endmodule")
        statement, = [n for n in nodes(design) if n.get("kind") == "BlockingAssign"]
        return design, statement["value"]

    def test_two_state_integrals_convert_selected_result(self):
        for declaration in ("bit [7:0] value;", "int value;", "byte value;",
                            "shortint value;", "longint value;"):
            with self.subTest(declaration=declaration):
                design, result = self.read(declaration)
                self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))
                self.assertEqual(result["kind"], "Squash2")
                self.assertEqual(result["width"], 4)
                self.assertEqual(result["operand"]["kind"], "SelectRead")
                self.assertEqual(result["operand"]["value"]["kind"], "Ident")

    def test_whole_struct_and_union_follow_aggregate_state(self):
        for shape in ("struct", "union"):
            for field, expected in (("bit", "Squash2"), ("logic", "SelectRead")):
                with self.subTest(shape=shape, field=field):
                    design, result = self.read(
                        shape + " packed { " + field + " [7:0] word; } value;")
                    self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))
                    self.assertEqual(result["kind"], expected)

    def test_mixed_struct_is_four_state_even_over_bit_field(self):
        _, result = self.read(
            "struct packed { logic [3:0] hi; bit [3:0] lo; } value;",
            "value[index -: 4]")
        self.assertEqual(result["kind"], "SelectRead")
        self.assertTrue(result["descending"])
        self.assertTrue(result["index_signed"])

    def test_bit_and_simple_part_reads_keep_two_state_conversion(self):
        for expression, width in (("value[index]", 1), ("value[9:6]", 4),
                                  ("value[index -: 4]", 4)):
            with self.subTest(expression=expression):
                _, result = self.read("bit [7:0] value;", expression)
                if result["kind"] == "Resize":
                    result = result["operand"]
                self.assertEqual(result["kind"], "Squash2")
                self.assertEqual(result["operand"]["width"], width)

    def test_ascending_two_state_constant_read_is_normalized(self):
        _, result = self.read("bit [0:7] value;", "value[1:4]")
        self.assertEqual(result["kind"], "Squash2")
        self.assertEqual(int(result["operand"]["index"]["bits"], 2), 3)

    def test_dynamic_noncanonical_two_state_range_preserves_squash(self):
        design, result = self.read("bit [0:7] value;")
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))
        self.assertEqual(result["kind"], "Squash2")
        self.assertEqual(result["operand"]["kind"], "SelectRead")

    def test_effectful_indices_and_unpacked_aggregates_stay_loud(self):
        for declaration, expression in (
                ("bit [7:0] value;", "value[index++ +: 4]"),
                ("struct packed { bit [7:0] word; } value;", "value[index++]"),
                ("struct { bit [7:0] word; } value;", "value[index +: 4]"),
                ("union tagged packed { bit [7:0] word; } value;", "value[index +: 4]")):
            with self.subTest(declaration=declaration, expression=expression):
                design = extract_source("module top; " + declaration +
                    " integer index; logic [3:0] result; initial result = " +
                    expression + "; endmodule")
                self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_disputed_control_escapes_stay_loud_before_resize_folding(self):
        for spelling in (r'"\a"', r'"\v"', r'"\f"'):
            for width in (8, 16):
                with self.subTest(spelling=spelling, width=width):
                    design = extract_source("module top; bit [" + str(width-1) +
                        ":0] value; initial value = " + spelling + "; endmodule")
                    self.assertTrue(any(n.get("sv_kind") == "StringLiteral:named-control-escape"
                                        for n in nodes(design)))

    def test_escaped_backslash_and_octal_controls_are_distinct(self):
        # an escaped backslash before an ordinary letter (also x) and the octal
        # spellings of the controls are plain bytes in every tool
        for spelling in (r'"\\a"', r'"\007\013\014"', r'"\\x41"'):
            with self.subTest(spelling=spelling):
                design = extract_source("module top; bit [23:0] value; "
                                        "initial value = " + spelling + "; endmodule")
                self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_hex_escapes_stay_loud(self):
        # IEEE Table 5-1 `\xdd`: slang, Icarus and Verilator give the byte, Yosys 0.53 and
        # Xcelium 24.03 read the letter x and the digits ("\x41" is 8'h31 in the scored
        # netlist), so the extractor must not admit it (tools-split audit, 2026-10-31).
        for spelling in (r'"\x41"', r'"\x4"', r'"\x07\x0b\x0c"', r'"A\x41"'):
            for width in (8, 16, 24):
                with self.subTest(spelling=spelling, width=width):
                    design = extract_source("module top; bit [" + str(width-1) +
                        ":0] value; initial value = " + spelling + "; endmodule")
                    self.assertTrue(any(n.get("sv_kind") == "StringLiteral:hex-escape"
                                        for n in nodes(design)))

    def test_hex_escape_confined_to_a_rare_region_stays_loud(self):
        # the attack the fourstate docstring describes: the disputed constant only matters
        # on one input value, where a sampled post-synthesis check may not look
        design = extract_source("module top(input logic [15:0] a, output logic [7:0] y); "
                                "assign y = (a == 16'hBEEF) ? \"\\x41\" : 8'h41; endmodule")
        self.assertTrue(any(n.get("sv_kind") == "StringLiteral:hex-escape" for n in nodes(design)))

    def test_named_control_escape_keeps_its_own_tag(self):
        design = extract_source("module top; bit [7:0] value; initial value = \"\\a\"; endmodule")
        kinds = {n.get("sv_kind") for n in nodes(design) if n.get("kind") == "Unsupported"}
        self.assertEqual(kinds, {"StringLiteral:named-control-escape"})


if __name__ == "__main__":
    unittest.main()
