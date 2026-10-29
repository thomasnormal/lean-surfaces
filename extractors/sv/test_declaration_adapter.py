"""The adapter follows source-history declaration erasure."""
import unittest

import census
import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


def blockers(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = source.encode()
    census.extract = extract
    return census.adapter_design_blockers(tree.sourceManager, compilation)


class DeclarationAdapter(unittest.TestCase):
    def test_finite_associative_declarations_are_metadata(self):
        self.assertEqual(
            blockers(
                'module top; initial begin int score[string]; '
                'logic [7:0] code[int]; $display("PASS"); '
                '$finish; end endmodule'),
            [])

    def test_dynamic_associative_use_remains_loud(self):
        residual = blockers(
            'module top; initial begin logic [7:0] score[string]; '
            'string key; key = "answer"; score[key] = 42; '
            '$display("PASS"); end endmodule')
        self.assertIn("AssignmentExpression:target", residual)

    def test_empty_dynamic_array_declarations_are_metadata(self):
        self.assertEqual(
            blockers(
                'module top; initial begin bit a[] = new[0]; '
                "logic b[] = '{}; $display(\"PASS\"); end endmodule"),
            [])

    def test_invalid_packed_dimensions_are_compile_time_metadata(self):
        self.assertEqual(
            blockers(
                "module top; initial begin bit [3:x] a; "
                "bit [3] b = 1'b0; $display(\"PASS\"); end endmodule"),
            [])

    def test_invalid_packed_dimension_effect_remains_loud(self):
        residual = blockers(
            "module top; function automatic int f(); f = 1; endfunction "
            "initial begin bit [3:x] a = f(); $display(\"PASS\"); end endmodule")
        self.assertIn("VariableDeclStatement:type", residual)

    def test_constant_extent_dynamic_declaration_follows_flat_lowering(self):
        self.assertEqual(
            blockers(
                'module top; initial begin int values[]; '
                'values = new[3]; values[0] = 1; '
                '$display("PASS"); end endmodule'),
            [])

    def test_symbolic_dynamic_extent_remains_loud(self):
        residual = blockers(
            'module top; initial begin int n; int values[]; n = 3; '
            'values = new[n]; values[0] = 1; '
            '$display("PASS"); end endmodule')
        self.assertIn("AssignmentExpression:target", residual)

    def test_fixed_array_declaration_follows_flat_lowering(self):
        self.assertEqual(
            blockers(
                'module top; initial begin int values[2]; '
                'values[0] = 10; values[1] = 20; '
                '$display("PASS"); end endmodule'),
            [])

    def test_unsupported_fixed_array_leaf_remains_loud(self):
        residual = blockers(
            'module top; initial begin real values[2]; '
            '$display("PASS"); end endmodule')
        self.assertIn("VariableDeclStatement:type", residual)

    def test_unpacked_struct_declaration_follows_flat_lowering(self):
        self.assertEqual(
            blockers(
                'module top; typedef struct { int x; bit y; } pair_t; '
                'initial begin pair_t value; value.x = 10; value.y = 1; '
                '$display("PASS"); end endmodule'),
            [])

    def test_unsupported_unpacked_struct_leaf_remains_loud(self):
        residual = blockers(
            'module top; typedef struct { real x; int y; } pair_t; '
            'initial begin pair_t value; $display("PASS"); end endmodule')
        self.assertIn("VariableDeclStatement:type", residual)

    def test_literal_assertcontrol_is_a_pure_diagnostic(self):
        self.assertEqual(
            blockers(
                'module top; initial begin $assertcontrol(2, 5); '
                '$display("PASS"); end endmodule'),
            [])

    def test_dynamic_assertcontrol_remains_loud(self):
        residual = blockers(
            'module top; int control; initial begin '
            '$assertcontrol(control); $display("PASS"); end endmodule')
        self.assertIn("Call:$assertcontrol", residual)

    def test_bare_assertion_controls_are_pure_diagnostics(self):
        self.assertEqual(
            blockers(
                'module top; initial begin $asserton; $assertoff; '
                '$assertkill; $display("PASS"); end endmodule'),
            [])

    def test_existing_pure_diagnostic_markers_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; initial begin '
                '$monitoroff; $monitoron(); '
                '$dumpfile("trace.vcd"); $dumpvars(0, top); '
                '$dumpon; $dumpoff; $dumpall; $dumpflush; '
                '$dumplimit(1024); $dumpportsflush(); '
                '$sdf_annotate("timing.sdf"); '
                '$timeformat(-9, 2, " ns", 10); $system(); '
                '$display("PASS"); end endmodule'),
            [])

    def test_dynamic_pure_diagnostic_arguments_remain_loud(self):
        residual = blockers(
            'module top; string path; initial begin '
            '$dumpfile(path); $display("PASS"); end endmodule')
        self.assertIn("Call:$dumpfile", residual)

    def test_discarded_pure_real_conversions_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; initial begin '
                '$itor(-17); $bitstoreal(64\'h3ff8_0000_0000_0000); '
                '$bitstoshortreal(32\'h3fc0_0000); $rtoi(0.5); '
                '$realtobits(1.0); $shortrealtobits(1.0); '
                '$display("PASS"); end endmodule'),
            [])

    def test_effectful_real_conversion_remains_loud(self):
        residual = blockers(
            'module top; integer x; initial begin x = 1; '
            '$itor(x++); $display("PASS"); end endmodule')
        self.assertIn("Call:$itor", residual)

    def test_discarded_pure_bit_queries_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; logic [3:0] value; initial begin '
                'value = 4\'b1010; '
                '$countbits(4\'b1010, 1\'b1, 1\'bx); '
                '$countones(value); $onehot(4\'b0001); '
                '$onehot0(value); $isunknown(4\'b10x0); '
                '$display("PASS"); end endmodule'),
            [])

    def test_computed_bit_query_remains_loud(self):
        residual = blockers(
            'module top; integer value; initial begin value = 1; '
            '$countones(value + 1); $display("PASS"); end endmodule')
        self.assertIn("Call:$countones", residual)

    def test_discarded_fixed_dimension_queries_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; logic [7:0] value; initial begin '
                '$size(value); $high(value); $left(value); $right(value); '
                '$low(value); $increment(value); $dimensions(value); '
                '$unpacked_dimensions(value); $display("PASS"); end endmodule'),
            [])

    def test_effectful_dimension_query_remains_loud(self):
        residual = blockers(
            'module top; logic [7:0] value; initial begin '
            '$size(value++); $display("PASS"); end endmodule')
        self.assertIn("Call:$size", residual)

    def test_discarded_pure_string_queries_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; string len_text, getc_text, atoi_text, radix_text; '
                'string left, rhs; initial begin '
                'len_text = "hello"; getc_text = "101"; '
                'atoi_text = "101"; radix_text = "101"; '
                'left = "101"; rhs = "101"; '
                'len_text.len(); getc_text.getc(0); atoi_text.atoi(); '
                'radix_text.atobin(); left.compare(rhs); left.icompare(rhs); '
                '$display("PASS"); end endmodule'),
            [])

    def test_dynamic_string_query_remains_loud(self):
        residual = blockers(
            'module top; string text, other; initial begin '
            'text = other; text.len(); $display("PASS"); end endmodule')
        self.assertIn("Call:len", residual)

    def test_discarded_pure_enum_methods_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; typedef enum logic [1:0] { A = 0, B = 1 } E; '
                'E value; initial begin value = B; value.name(); '
                'value.first(); value.last(); value.num(); value.next(); '
                'value.prev(); $display("PASS"); end endmodule'),
            [])

    def test_effectful_enum_method_remains_loud(self):
        residual = blockers(
            'module top; typedef enum logic [1:0] { A = 0, B = 1 } E; '
            'E value; int count; initial begin value = B; count = 0; '
            'value.next(count++); $display("PASS"); end endmodule')
        self.assertIn("Call:next", residual)

    def test_discarded_pure_floating_math_is_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; initial begin $sqrt(16.0); $pow(2.0, 3.0); '
                '$sin($sqrt(4.0)); $display("PASS"); end endmodule'),
            [])

    def test_effectful_floating_math_remains_loud(self):
        residual = blockers(
            'module top; int index; initial begin $sqrt(index++); '
            '$display("PASS"); end endmodule')
        self.assertIn("Call:$sqrt", residual)

    def test_discarded_empty_associative_queries_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; int num_values[string]; int size_values[string]; '
                'int first_values[string]; int last_values[int]; '
                'string first_key; int last_key; initial begin '
                'num_values.num(); size_values.size(); '
                'first_values.first(first_key); last_values.last(last_key); '
                '$display("PASS"); end endmodule'),
            [])

    def test_populated_associative_query_remains_loud(self):
        residual = blockers(
            'module top; int values[string]; initial begin '
            'values["answer"] = 1; values.num(); '
            '$display("PASS"); end endmodule')
        self.assertIn("Call:num", residual)

    def test_discarded_zero_size_queries_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; string text; int values[$]; initial begin '
                'text.len(); values.size(); $display("PASS"); end endmodule'),
            [])

    def test_populated_zero_size_query_remains_loud(self):
        residual = blockers(
            'module top; string text, other; initial begin text = other; '
            'text.len(); $display("PASS"); end endmodule')
        self.assertIn("Call:len", residual)

    def test_discarded_type_and_width_queries_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; int counter; initial begin '
                '$typename(counter++); $bits(counter++); '
                '$display("PASS"); end endmodule'),
            [])

    def test_malformed_type_query_remains_loud(self):
        residual = blockers(
            'module top; initial begin $typename(); '
            '$display("PASS"); end endmodule')
        self.assertIn("InvalidStatement", residual)

    def test_discarded_empty_subroutine_calls_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; task automatic noop(); endtask '
                'task automatic input_noop(input logic value); endtask '
                'initial begin noop(); input_noop(1\'b0); '
                '$display("PASS"); end endmodule'),
            [])

    def test_nonempty_subroutine_call_remains_loud(self):
        residual = blockers(
            'module top; task automatic noisy(); $display("NO"); endtask '
            'initial begin noisy(); $display("PASS"); end endmodule')
        self.assertIn("SubroutineSymbol:Subroutine", residual)

    def test_effectful_empty_input_task_call_remains_loud(self):
        residual = blockers(
            'module top; int counter; '
            'task automatic input_noop(input logic value); endtask '
            'initial begin input_noop(counter++); '
            '$display("PASS"); end endmodule')
        self.assertIn("SubroutineSymbol:Subroutine", residual)

    def test_discarded_scalar_metadata_queries_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                '`timescale 1ns/1ps\nmodule top; int counter; '
                'initial begin $clog2(8); $isunbounded(5); '
                '$signed(8\'hff); $unsigned(counter); $timeunit; '
                '$timeprecision; $display("PASS"); end endmodule'),
            [])

    def test_effectful_scalar_metadata_queries_remain_loud(self):
        residual = blockers(
            'module top; int counter; initial begin '
            '$clog2(counter++); $display("PASS"); end endmodule')
        self.assertIn("Call:$clog2", residual)

    def test_discarded_literal_sformatf_is_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; initial begin $sformatf("%H", 8\'hAB); '
                '$sformatf("%b", 4\'b1010); $display("PASS"); end endmodule'),
            [])

    def test_dynamic_sformatf_remains_loud(self):
        residual = blockers(
            'module top; string fmt; initial begin '
            '$sformatf(fmt, 8\'hAB); $display("PASS"); end endmodule')
        self.assertIn("Call:$sformatf", residual)

    def test_discarded_pure_array_queries_are_adapter_safe(self):
        self.assertEqual(
            blockers(
                'module top; logic [7:0] values [2]; '
                'initial begin values[0] = 1; values[1] = 2; '
                'values.min(); values.max(); values.unique(); '
                'values.unique_index(); values.sum(); values.product(); '
                'values.and(); values.or(); values.xor(); '
                '$display("PASS"); end endmodule'),
            [])

    def test_effectful_array_reduction_remains_loud(self):
        residual = blockers(
            'module top; int values [2]; int item; initial begin '
            'item = 0; values.sum(x) with (x + item++); '
            '$display("PASS"); end endmodule')
        self.assertIn("Call:sum", residual)


if __name__ == "__main__":
    unittest.main()
