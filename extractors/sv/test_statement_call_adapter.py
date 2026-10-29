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

    def test_supported_severity_and_fatal_calls_follow_converter(self):
        self.assertEqual(
            blockers(
                'module top; logic [3:0] x; initial begin x = 4\'d3; '
                '$info("x=%0d", x); $warning("warning"); '
                '$error("error"); $fatal(1, "done=%0d", x); end endmodule'),
            [])
        self.assertEqual(
            blockers(
                'module top; real value; initial '
                '$info("value=%f", value); endmodule'),
            [])

    def test_unsupported_severity_arguments_remain_loud(self):
        residual = blockers(
            'module top; real value; initial $info(value); endmodule')
        self.assertIn("Call:$info", residual)

    def test_unsupported_fatal_arguments_remain_loud(self):
        residual = blockers(
            'module top; real value; initial $fatal(1, value); endmodule')
        self.assertIn("Call:$fatal", residual)

    def test_lowered_array_ordering_methods_follow_converter(self):
        self.assertEqual(
            blockers(
                "module top; int values [0:3]; initial begin "
                "values = '{5, 1, 3, 2}; values.sort(); values.rsort(); "
                "$display(\"PASS\"); end endmodule"),
            [])

    def test_predefined_stdout_file_output_follows_converter(self):
        self.assertEqual(
            blockers(
                'module top; initial begin '
                '$fdisplay(32\'h8000_0001, "PASS"); '
                '$fwrite(32\'h8000_0001, ""); end endmodule'),
            [])

    def test_non_stdout_file_output_remains_loud(self):
        residual = blockers(
            'module top; initial begin '
            '$fdisplay(32\'h8000_0002, "x"); '
            '$fwrite(32\'h8000_0002, "x"); end endmodule')
        self.assertIn("Call:$fdisplay", residual)
        self.assertIn("Call:$fwrite", residual)

    def test_unlowered_array_ordering_remains_loud(self):
        residual = blockers(
            'module top; int values [0:3]; initial values.sort(); endmodule')
        self.assertIn("Call:sort", residual)

    def test_clean_elaborated_generate_metadata_follows_converter(self):
        self.assertEqual(
            blockers(
                'module top; logic value; if (1) begin : live '
                'initial value = 1\'b1; end '
                'initial begin if (value) $display("PASS"); '
                '$finish; end endmodule'),
            [])

    def test_unsupported_elaborated_generate_stays_loud(self):
        residual = blockers(
            'module top; if (1) begin : live initial #1; end '
            'initial $display("PASS"); endmodule')
        self.assertIn("TimedStatement:DelayControl", residual)

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
