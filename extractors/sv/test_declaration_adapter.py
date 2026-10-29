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


if __name__ == "__main__":
    unittest.main()
