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

    def test_opaque_declarations_follow_converter_erasure(self):
        self.assertEqual(
            blockers(
                'module top; real r = 0.5; realtime rt = 0.5; '
                'shortreal sr = 0.5; chandle h; event ev; '
                'initial $display("PASS"); endmodule'),
            [])

    def test_opaque_uses_remain_loud(self):
        residual = blockers(
            'module top; real r = 0.5; initial begin '
            '$display("%0d", r); end endmodule')
        self.assertIn("NamedValueExpression:2state", residual)

    def test_compile_time_typedefs_follow_converter_erasure(self):
        self.assertEqual(
            blockers(
                'module top; typedef bit [7:0] byte_t; '
                'typedef struct { bit [3:0] hi; bit [3:0] lo; } pair_t; '
                'byte_t b; pair_t p; initial $display("PASS"); endmodule'),
            [])

    def test_source_pure_string_statement_methods_are_admitted(self):
        self.assertEqual(
            blockers(
                'module top; string s = "Test"; initial begin '
                's.putc(2, "B"); s.itoa(12); s.bintoa(10); '
                's.octtoa(8); s.hextoa(255); $display("PASS"); '
                'end endmodule'),
            [])

    def test_dynamic_string_statement_method_remains_loud(self):
        residual = blockers(
            'module top; string s; int i; initial s.putc(i, "X"); endmodule')
        self.assertIn("Call:putc", residual)


if __name__ == "__main__":
    unittest.main()
