"""Adapter admission for source-pure string histories."""
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


class StringAdapterHistory(unittest.TestCase):
    def test_literal_concat_and_replication_history_is_admitted(self):
        self.assertEqual(
            blockers(
                'module top; string str; initial begin '
                'str = {"Hello", "_", "World", "!"}; '
                '$display("%s", str); end endmodule'),
            [])
        self.assertEqual(
            blockers(
                'module top; string str; initial begin '
                'str = {4{"test"}}; $display("%s", str); end endmodule'),
            [])

    def test_unknown_string_history_remains_loud(self):
        residual = blockers(
            'module top; string str, source; initial begin '
            'str = source; $display("%s", str); end endmodule')
        self.assertIn("NamedValueExpression:2state", residual)


if __name__ == "__main__":
    unittest.main()
