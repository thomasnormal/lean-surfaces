"""Adapter admission follows extractor erasure for uncalled subroutines."""
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


class SubroutineAdapter(unittest.TestCase):
    def test_uncalled_subroutine_is_metadata(self):
        self.assertEqual(
            blockers(
                'module top; task unused; $display("NEVER"); endtask '
                'initial $display("PASS"); endmodule'),
            [])

    def test_called_subroutine_remains_loud(self):
        residual = blockers(
            'module top; task used; $display("NEVER"); endtask '
            'initial begin used(); $display("PASS"); end endmodule')
        self.assertIn("SubroutineSymbol:Subroutine", residual)


if __name__ == "__main__":
    unittest.main()
