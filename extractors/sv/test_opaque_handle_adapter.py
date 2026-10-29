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


if __name__ == "__main__":
    unittest.main()
