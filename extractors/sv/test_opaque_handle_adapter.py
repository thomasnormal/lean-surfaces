"""The adapter follows opaque class-handle declaration erasure."""
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


class OpaqueHandleAdapter(unittest.TestCase):
    def test_uninitialized_handles_are_metadata_at_both_scopes(self):
        self.assertEqual(
            blockers(
                'module top; mailbox module_box; semaphore module_sem; '
                'initial begin mailbox local_box; semaphore local_sem; '
                '$display("PASS"); $finish; end endmodule'),
            [])

    def test_handle_use_remains_loud(self):
        residual = blockers(
            'module top; mailbox box; '
            'initial begin if (box == null) $display("PASS"); end endmodule')
        self.assertIn("NamedValueExpression:2state", residual)

    def test_initialized_handle_is_not_erased_as_a_declaration(self):
        residual = blockers(
            'module top; mailbox box = new(2); '
            'initial $display("PASS"); endmodule')
        self.assertIn("VariableSymbol:2state", residual)

    def test_literal_semaphore_constructor_is_metadata(self):
        self.assertEqual(
            blockers(
                'module top; initial begin semaphore sem = new(5); '
                '$display("PASS"); $finish; end endmodule'),
            [])

    def test_dynamic_semaphore_constructor_remains_loud(self):
        residual = blockers(
            'module top; initial begin int keys = 5; '
            'semaphore sem = new(keys); $display("PASS"); end endmodule')
        self.assertIn("VariableDeclStatement:type", residual)

    def test_untouched_mixed_array_declaration_is_metadata(self):
        self.assertEqual(
            blockers(
                'module top; initial begin bit cells[2][][3]; '
                '$display("PASS"); $finish; end endmodule'),
            [])

    def test_mixed_array_value_use_remains_loud(self):
        residual = blockers(
            'module top; initial begin bit cells[2][][3]; '
            'cells[0][0][0] = 1; $display("PASS"); end endmodule')
        self.assertIn("VariableDeclStatement:type", residual)


if __name__ == "__main__":
    unittest.main()
