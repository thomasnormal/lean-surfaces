"""Fixed-size query admission checks; expected runtime values use licensed fixtures."""

import unittest
from pathlib import Path

import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


REPO = Path(__file__).resolve().parents[2]


def lower(source, require_valid=True):
    extract._SYM = None
    extract._SOURCE_BYTES = source.encode()
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    errors = [diagnostic for diagnostic in compilation.getAllDiagnostics()
              if diagnostic.isError()]
    if require_valid and errors:
        raise AssertionError("query regression source has frontend errors")
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


def query_source(expression, declarations=""):
    return ("module top; " + declarations + " initial begin $display(\"%0d\", " +
            expression + "); $finish; end endmodule")


def query_nodes(design):
    return [node for node in nodes(design) if node.get("fixed_bits_query")]


class FixedBitQueries(unittest.TestCase):
    def assert_fixed_queries(self, source, expected):
        design = lower(source)
        literals = query_nodes(design)
        self.assertEqual([int(node["bits"], 2) for node in literals], expected)
        for node in literals:
            self.assertEqual(node["kind"], "Literal")
            self.assertEqual(node["width"], 32)
            self.assertEqual(len(node["bits"]), 32)
            self.assertIs(node.get("signed"), True)
        return design

    def assert_query_refused(self, source, require_valid=True):
        design = lower(source, require_valid=require_valid)
        self.assertFalse(query_nodes(design))
        self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_reference_fixtures_are_admitted(self):
        sources = sorted((REPO / "harness/sv/bit_queries").glob("*.sv"))
        self.assertEqual(len(sources), 6)
        for source in sources:
            with self.subTest(source=source.name):
                design = lower(source.read_text())
                self.assertTrue(query_nodes(design))
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_builtin_type_queries_return_signed_integer(self):
        widths = {"bit": 1, "logic": 1, "byte": 8, "shortint": 16,
                  "int": 32, "integer": 32, "longint": 64, "time": 64}
        for type_name, width in widths.items():
            with self.subTest(type_name=type_name):
                self.assert_fixed_queries(query_source("$bits(" + type_name + ")"), [width])

    def test_fixed_unpacked_array_and_struct_type_queries(self):
        declarations = ("typedef logic [2:0] array_t [4:1][0:2]; "
                        "typedef struct {logic [2:0] first; bit [4:0] second;} record_t; "
                        "typedef record_t records_t [0:2]; ")
        source = ("module top; initial begin " + declarations +
                  "$display(\"%0d %0d %0d\", $bits(array_t), $bits(record_t), "
                  "$bits(records_t)); end endmodule")
        design = self.assert_fixed_queries(source, [36, 8, 24])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_local_integral_alias_and_enum_queries(self):
        source = ("module top; initial begin typedef shortint unsigned size_t; "
                  "typedef enum logic [4:0] {LOW=3, HIGH=4} state_t; "
                  "$display(\"%0d %0d %0d\", $bits(size_t), $bits(state_t), "
                  "$bits(HIGH)); end endmodule")
        self.assert_fixed_queries(source, [16, 5, 5])

    def test_effectful_increment_and_assignment_arguments_stay_loud(self):
        expressions = ("subject++", "++subject", "subject--", "--subject",
                       "(subject = 8'd1)")
        for expression in expressions:
            with self.subTest(expression=expression):
                self.assert_query_refused(query_source("$bits(" + expression + ")",
                                                      "logic [7:0] subject; "))

    def test_other_calls_inside_query_arguments_stay_loud(self):
        declarations = ("function automatic byte effect(); $display(\"CALLED\"); "
                        "effect=1; endfunction ")
        self.assert_query_refused(query_source("$bits(effect())", declarations))
        self.assert_query_refused(query_source("$bits($unsigned(subject++))",
                                              "logic [7:0] subject; "))

    def test_effectful_selected_read_indices_stay_loud(self):
        declarations = "logic [7:0] subject; integer index; "
        expressions = ("subject[index++]", "subject[index++ +: 3]",
                       "subject[index++ -: 4]")
        for expression in expressions:
            with self.subTest(expression=expression):
                self.assert_query_refused(query_source("$bits(" + expression + ")",
                                                      declarations))

    def test_pure_selected_read_metadata_queries(self):
        declarations = "logic [7:0] subject; integer index; "
        expressions = {"subject[index + 1]": 1, "subject[index +: 3]": 3,
                       "subject[index -: 4]": 4}
        for expression, width in expressions.items():
            with self.subTest(expression=expression):
                design = self.assert_fixed_queries(query_source("$bits(" + expression + ")",
                                                                declarations), [width])
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_dynamic_container_fixed_element_query(self):
        source = query_source("$bits(values[0])", "int values[]; ")
        self.assert_fixed_queries(source, [32])

    def test_query_in_whole_case_is_a_pure_leaf(self):
        source = ("module top; logic [7:0] subject; integer index; initial begin "
                  "case ($bits(subject[index])) $bits(logic):; $bits(byte):; "
                  "endcase end endmodule")
        design = lower(source)
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))
        self.assertEqual(len([node for node in nodes(design) if node.get("case_lowered")]), 2)
        self.assertEqual(len(query_nodes(design)), 4)

    def test_effectful_query_is_not_a_pure_case_leaf(self):
        source = ("module top; logic [7:0] subject; initial begin "
                  "case ($bits(subject++)) 8:; endcase end endmodule")
        design = lower(source)
        self.assertFalse(query_nodes(design))
        self.assertIn("CaseStatement:subject", [node.get("sv_kind") for node in nodes(design)])

    def test_nested_query_has_integer_result_width(self):
        self.assert_fixed_queries(query_source("$bits($bits(bit))"), [32])

    def test_nested_query_cannot_hide_effectful_operand(self):
        source = query_source("$bits($bits(subject++))", "logic [7:0] subject; ")
        self.assert_query_refused(source)

    def test_conversion_cannot_erase_effectful_query_refusal(self):
        source = query_source("64'($bits(subject++))", "logic [7:0] subject; ")
        self.assert_query_refused(source)

    def test_conversion_context_preserves_signed_query_literal(self):
        expressions = ("64'($bits(byte))", "3'($bits(byte))", "$bits(byte) + 64'd1")
        for expression in expressions:
            with self.subTest(expression=expression):
                design = self.assert_fixed_queries(query_source(expression), [8])
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_integer_result_wraps_fixed_type_bitstream_width(self):
        dimensions = {"[65536][32768]": 0x80000000, "[65536][65536]": 0}
        for ranges, result in dimensions.items():
            with self.subTest(ranges=ranges):
                source = ("module top; initial begin typedef bit huge_t " + ranges + "; "
                          "$display(\"%0d\", $bits(huge_t)); end endmodule")
                design = self.assert_fixed_queries(source, [result])
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_dynamic_size_queries_stay_loud(self):
        declarations = {"int values[]; ": "values", "int values[$]; ": "values",
                        "int values[int]; ": "values"}
        for declaration, expression in declarations.items():
            with self.subTest(declaration=declaration):
                self.assert_query_refused(query_source("$bits(" + expression + ")", declaration))

    def test_string_and_real_queries_stay_loud(self):
        sources = [query_source("$bits(value)", "string value; "),
                   query_source("$bits(value)", "real value; "),
                   query_source("$bits(real)"), query_source("$bits(shortreal)")]
        for source in sources:
            with self.subTest(source=source):
                self.assert_query_refused(source)

    def test_unpacked_union_query_stays_loud(self):
        source = ("module top; initial begin "
                  "typedef union {logic [7:0] word; logic [3:0] nibble;} union_t; "
                  "$display(\"%0d\", $bits(union_t)); end endmodule")
        self.assert_query_refused(source)

    def test_interface_class_query_stays_loud(self):
        source = ("interface class marker; endclass " + query_source("$bits(marker)"))
        self.assert_query_refused(source, require_valid=False)

    def test_invalid_query_forms_stay_loud(self):
        for expression in ("$bits()", "$bits(int, int)", "$bits(unknown_type)"):
            with self.subTest(expression=expression):
                self.assert_query_refused(query_source(expression), require_valid=False)

    def test_general_system_and_function_calls_stay_loud(self):
        self.assert_query_refused(query_source("$clog2(subject)",
                                              "logic [7:0] subject; "))
        declarations = "function automatic int fixed_value(); fixed_value=4; endfunction "
        self.assert_query_refused(query_source("fixed_value()", declarations))

    def test_constant_clog2_is_folded_to_signed_int(self):
        source = ("module top; logic [31:0] a, b, c, d, e; "
                  "assign a = $clog2(0); assign b = $clog2(1); "
                  "assign c = $clog2(8); assign d = $clog2(9); "
                  "assign e = $clog2(-1); endmodule")
        design = lower(source)
        values = [
            int(process["value"]["bits"], 2)
            for process in design["modules"][0]["processes"]
        ]
        self.assertEqual(values, [0, 0, 3, 4, 32])
        for process in design["modules"][0]["processes"]:
            self.assertIs(process["value"].get("signed"), True)
            self.assertIs(process["value"].get("fixed_clog2"), True)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_constant_clog2_keeps_invalid_compilation_loud(self):
        source = ("module top; logic [31:0] value; assign value = $clog2(8); "
                  "endmodule module bad; initial undeclared = 1; endmodule")
        design = lower(source, require_valid=False)
        self.assertIn("$clog2:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_invalid_compilation_cannot_become_clean_by_lowering_query(self):
        source = (query_source("$bits(int)") +
                  " module bad; initial undeclared = 1; endmodule")
        design = lower(source, require_valid=False)
        self.assertIn("$bits:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_converted_query_retains_invalid_compilation_guard(self):
        source = ("module top; logic [63:0] value; initial value = $bits(int); endmodule "
                  "module bad; initial undeclared = 1; endmodule")
        design = lower(source, require_valid=False)
        literals = query_nodes(design)
        self.assertEqual(len(literals), 1)
        self.assertEqual(literals[0]["width"], 32)
        self.assertIs(literals[0].get("signed"), True)
        self.assertIn("$bits:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
