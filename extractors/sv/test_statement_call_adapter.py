"""Adapter admission for the represented output/termination calls."""
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


class StatementCallAdapter(unittest.TestCase):
    def test_write_and_stop_use_existing_state(self):
        self.assertEqual(
            blockers(
                'module top; initial begin $write("PASS"); '
                '$display(""); $stop; end endmodule'),
            [])

    def test_other_statement_calls_remain_loud(self):
        residual = blockers(
            'module top; initial begin $info("diagnostic"); '
            '$display("PASS"); end endmodule')
        self.assertIn("Call:$info", residual)

    def test_inert_pure_diagnostics_follow_converter_erasure(self):
        self.assertEqual(
            blockers(
                '`timescale 1ns/1ps module top; initial begin '
                '$printtimescale; $printtimescale($unit); $exit; '
                '$display("PASS"); end endmodule'),
            [])

    def test_noninert_pure_diagnostic_forms_remain_loud(self):
        residual = blockers(
            'module top; initial $printtimescale(1); endmodule')
        self.assertTrue(
            "Call:$printtimescale" in residual or "InvalidStatement" in residual)


if __name__ == "__main__":
    unittest.main()
