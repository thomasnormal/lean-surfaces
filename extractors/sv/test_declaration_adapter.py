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

    def test_nonempty_dynamic_array_allocation_remains_loud(self):
        residual = blockers(
            'module top; initial begin bit a[] = new[1]; '
            '$display("PASS"); end endmodule')
        self.assertIn("VariableDeclStatement:type", residual)

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


if __name__ == "__main__":
    unittest.main()
