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

    def test_string_and_real_queries(self):
        for source in (query_source("$bits(value)", "string value; "),
                       query_source("$bits(value)", "real value; ")):
            with self.subTest(source=source):
                self.assert_query_refused(source)
        for source, width in ((query_source("$bits(real)"), 64),
                              (query_source("$bits(shortreal)"), 32)):
            with self.subTest(source=source):
                self.assert_fixed_queries(source, [width])

    def test_floating_type_query_does_not_admit_runtime_value(self):
        source = query_source("$bits(value)", "real value; ")
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
        self.assert_query_refused(query_source("$ln(subject)",
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

    def test_fixed_dimension_queries_fold_from_integral_types(self):
        source = ("module top; logic [7:0] vector; int integer_value; "
                  "initial $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d %0d "
                  "%0d %0d %0d %0d\", "
                  "$size(vector), $high(vector), $left(vector), $right(vector), "
                  "$low(vector), $increment(vector), $size(integer_value), "
                  "$high(integer_value), $left(integer_value), $right(integer_value), "
                  "$low(integer_value), $increment(integer_value), "
                  "$dimensions(integer_value), $unpacked_dimensions(integer_value)); "
                  "endmodule")
        design = lower(source)
        literals = [node for node in nodes(design)
                    if node.get("fixed_dimension_query")]
        self.assertEqual(
            [(node["fixed_dimension_query"], int(node["bits"], 2))
             for node in literals],
            [("$size", 8), ("$high", 7), ("$left", 7), ("$right", 0),
             ("$low", 0), ("$increment", 1), ("$size", 32), ("$high", 31),
             ("$left", 31), ("$right", 0), ("$low", 0), ("$increment", 1),
             ("$dimensions", 1), ("$unpacked_dimensions", 0)])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_explicit_constant_dimension_selectors(self):
        source = query_source(
            "$size(vector, 1) + $high(vector, 1 + 0) + $left(vector, DIM) + "
            "$right(vector, 1) + $low(vector, 1) + $increment(vector, 1)",
            "logic [7:0] vector; localparam int DIM = 1;")
        design = lower(source)
        queries = [node for node in nodes(design) if node.get("fixed_dimension_query")]
        self.assertEqual([int(node["bits"], 2) for node in queries], [8, 7, 7, 0, 0, 1])

    def test_fixed_type_dimensions_follow_declared_order_and_bounds(self):
        source = ("module top; initial begin "
                  "typedef logic [2:4][9:6] packed_t; "
                  "typedef int array_t [4:1][0:2]; "
                  "$display(\"%0d\", $dimensions(packed_t), "
                  "$unpacked_dimensions(packed_t), $size(packed_t, 1), "
                  "$left(packed_t, 1), $right(packed_t, 1), "
                  "$low(packed_t, 1), $high(packed_t, 1), "
                  "$increment(packed_t, 1), $size(packed_t, 2), "
                  "$increment(packed_t, 2), $dimensions(array_t), "
                  "$unpacked_dimensions(array_t), $size(array_t, 1), "
                  "$increment(array_t, 1), $size(array_t, 2), "
                  "$increment(array_t, 2), $size(array_t, 3), $left(array_t, 3)); "
                  "end endmodule")
        design = lower(source)
        queries = [node for node in nodes(design) if node.get("fixed_dimension_query")]
        self.assertEqual([int(node["bits"], 2) for node in queries],
                         [2, 0, 3, 2, 4, 2, 4, 0xffffffff, 4, 1,
                          3, 2, 4, 1, 3, 0xffffffff, 32, 31])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_unvisited_branch_keeps_static_dimension_selectors(self):
        source = ("module top; logic [7:0] vector; localparam int DIM = 1; "
                  "initial begin if ($size(vector) == 8) $display(\"PASS\"); "
                  "else $display(\"%0d %0d\", $size(vector, 1), $left(vector, DIM)); "
                  "end endmodule")
        design = lower(source)
        queries = [node for node in nodes(design) if node.get("fixed_dimension_query")]
        self.assertEqual([int(node["bits"], 2) for node in queries], [8, 8, 7])

    def test_unbound_compound_selector_stays_loud(self):
        source = ("module top; logic [7:0] vector; "
                  "initial if ($size(vector) == 8) $display(\"PASS\"); "
                  "else $display(\"%0d\", $size(vector, 1 + 0)); endmodule")
        design = lower(source)
        self.assertIn("CallExpression:dimension:dynamic",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_scalar_dimension_counts_are_zero(self):
        for type_name in ("bit", "logic", "reg"):
            with self.subTest(type_name=type_name):
                design = lower(query_source(
                    "$dimensions(value) + $unpacked_dimensions(value)",
                    type_name + " value;"))
                queries = [node for node in nodes(design)
                           if node.get("fixed_dimension_query")]
                self.assertEqual([int(node["bits"], 2) for node in queries], [0, 0])

    def test_fixed_dimension_type_aliases_have_no_runtime_effect(self):
        source = ("module top; typedef logic [2:4][9:6] packed_t; "
                  "typedef packed_t array_t [1:2]; "
                  "initial $display(\"%0d %0d\", $dimensions(array_t), "
                  "$size(array_t, 3)); endmodule")
        design = lower(source)
        queries = [node for node in nodes(design) if node.get("fixed_dimension_query")]
        self.assertEqual([int(node["bits"], 2) for node in queries], [3, 4])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_fixed_array_dimension_query_uses_flattened_cells(self):
        source = ("module top; typedef logic [7:0] array_t [1:2]; array_t values; "
                  "initial $display(\"%0d\", $size(values)); endmodule")
        design = lower(source)
        queries = [node for node in nodes(design) if node.get("fixed_dimension_query")]
        self.assertEqual([int(node["bits"], 2) for node in queries], [2])
        cells = [node for node in nodes(design)
                 if node.get("kind") == "Var" and node.get("name", "").startswith("values[")]
        self.assertEqual([node["name"] for node in cells], ["values[1]", "values[2]"])

    def test_erasing_fixed_type_alias_keeps_frontend_errors_loud(self):
        sources = (
            "typedef struct packed {int member = 5;} bad_t; "
            "module top; initial $finish; endmodule",
            "module top; typedef logic [2:4] range_t; "
            "initial undeclared = 1; endmodule",
        )
        for source in sources:
            with self.subTest(source=source):
                design = lower(source, require_valid=False)
                self.assertIn("TypeAlias:invalid-compilation",
                              [node.get("sv_kind") for node in nodes(design)])

    def test_tagged_union_metadata_stays_outside_dimension_tier(self):
        source = ("module top; typedef union tagged packed {void Invalid; int Valid;} tagged_t; "
                  "initial $display(\"%0d\", $dimensions(tagged_t)); endmodule")
        design = lower(source)
        self.assertFalse(any(node.get("fixed_dimension_query") for node in nodes(design)))
        self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_packed_aggregate_and_enum_dimensions(self):
        source = ("module top; initial begin "
                  "typedef struct packed {logic [2:0] first; bit second;} packet_t; "
                  "typedef enum logic [4:0] {LOW = 5'd3, HIGH = 5'd4} state_t; "
                  "typedef enum bit {OFF = 0, ON = 1} scalar_state_t; "
                  "$display(\"%0d\", $dimensions(packet_t), $size(packet_t), "
                  "$dimensions(state_t), $size(state_t), $dimensions(scalar_state_t)); "
                  "end endmodule")
        design = lower(source)
        queries = [node for node in nodes(design) if node.get("fixed_dimension_query")]
        self.assertEqual([int(node["bits"], 2) for node in queries], [1, 4, 1, 5, 1])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_runtime_or_effectful_dimension_selectors_stay_loud(self):
        for selector in ("dimension", "dimension++", "(dimension = 1)"):
            with self.subTest(selector=selector):
                source = query_source("$size(value, " + selector + ")",
                                      "logic [7:0] value; int dimension;")
                design = lower(source)
                self.assertFalse(any(node.get("fixed_dimension_query")
                                     for node in nodes(design)))
                self.assertTrue(any(node.get("kind") == "Unsupported"
                                    for node in nodes(design)))

    def test_invalid_dimension_selectors_stay_loud(self):
        for selector in ("0", "-1", "2", "32'bx", "32'bz"):
            with self.subTest(selector=selector):
                design = lower(query_source("$size(value, " + selector + ")",
                                            "logic [7:0] value;"), require_valid=False)
                self.assertFalse(any(node.get("fixed_dimension_query")
                                     for node in nodes(design)))
                self.assertTrue(any(node.get("kind") == "Unsupported"
                                    for node in nodes(design)))

    def test_dynamic_or_effectful_dimension_queries_stay_loud(self):
        for declaration, expression in (
                ("int values[];", "$size(values)"),
                ("int values[$];", "$high(values)"),
                ("int values[$];", "$left(values)"),
                ("int values[$];", "$increment(values)"),
                ("int values[];", "$dimensions(values)"),
                ("int values[];", "$unpacked_dimensions(values)"),
                ("logic [7:0] value;", "$size(value++)")):
            with self.subTest(declaration=declaration, expression=expression):
                self.assert_query_refused(query_source(expression, declaration))

    def test_fixed_dimension_query_keeps_invalid_compilation_loud(self):
        source = ("module top; logic [7:0] value; initial $display(\"%0d\", "
                  "$size(value)); endmodule "
                  "module bad; initial undeclared = 1; endmodule")
        design = lower(source, require_valid=False)
        self.assertIn("DimensionQuery:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_dimension_count_queries_keep_invalid_compilation_loud(self):
        source = ("module top; int value; initial $display(\"%0d\", "
                  "$dimensions(value)); endmodule "
                  "module bad; initial undeclared = 1; endmodule")
        design = lower(source, require_valid=False)
        self.assertIn("DimensionQuery:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_converted_dimension_query_retains_invalid_compilation_guard(self):
        source = ("module top; logic [63:0] value; "
                  "initial value = $dimensions(int); endmodule "
                  "module bad; initial undeclared = 1; endmodule")
        design = lower(source, require_valid=False)
        self.assertTrue(any(node.get("fixed_dimension_query") for node in nodes(design)))
        self.assertIn("DimensionQuery:invalid-compilation",
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
