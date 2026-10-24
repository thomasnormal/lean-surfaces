"""Empty zero-argument functions produce their declared default value."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def lower(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class EmptyFunctionCalls(unittest.TestCase):
    def test_two_state_default_is_zero(self):
        design = lower(
            'module top; function bit [3:0] zero(); endfunction '
            'initial begin if (zero() == 4\'b0000) $display("PASS"); '
            'end endmodule')
        self.assertTrue(any(node.get("empty_function_default")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_four_state_default_is_unknown(self):
        design = lower(
            'module top; function logic [3:0] unknown(); endfunction '
            'initial begin if (unknown() === 4\'bxxxx) $display("PASS"); '
            'end endmodule')
        self.assertTrue(any(node.get("empty_function_default")
                            and set(node.get("bits", "")) == {"x"}
                            for node in nodes(design)))

    def test_literal_return_is_materialized_at_call_site(self):
        design = lower(
            'module top; function bit [3:0] seven(); return 4\'d7; endfunction '
            'initial begin if (seven() == 4\'d7) $display("PASS"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("literal_function_return")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "0111")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_literal_return_boundary_rejects_effectful_body(self):
        design = lower(
            'module top; logic [3:0] value; '
            'function bit [3:0] read(); return value; endfunction '
            'initial if (read() == 0) $display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_literal_return_accepts_integral_literal_input(self):
        design = lower(
            'module top; function bit [3:0] seven(input bit selector); '
            'return 4\'d7; endfunction initial begin '
            'if (seven(1\'b0) == 4\'d7) $display("PASS"); endmodule')
        values = [node for node in nodes(design)
                  if node.get("literal_function_return")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "0111")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_literal_return_rejects_dynamic_input(self):
        design = lower(
            'module top; bit selector; function bit [3:0] seven(input bit x); '
            'return 4\'d7; endfunction initial begin '
            'if (seven(selector) == 4\'d7) $display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_literal_return_rejects_output_formal(self):
        design = lower(
            'module top; bit result; function bit [3:0] seven(output bit out); '
            'return 4\'d7; endfunction initial begin '
            'if (seven(result) == 4\'d7) $display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_literal_return_statement_is_erased(self):
        design = lower(
            'module top; function bit [3:0] seven(); return 4\'d7; endfunction '
            'initial seven(); endmodule')
        self.assertTrue(any(node.get("literal_function_statement") == "seven"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_literal_return_statement_accepts_literal_input(self):
        design = lower(
            'module top; function bit [3:0] seven(input bit x); '
            'return 4\'d7; endfunction initial seven(1\'b0); endmodule')
        self.assertTrue(any(node.get("literal_function_statement") == "seven"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_literal_return_statement_with_argument_stays_loud(self):
        design = lower(
            'module top; bit x; function bit [3:0] seven(input bit x); '
            'return 4\'d7; endfunction initial seven(x); endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_rtoi_literal_truncates_toward_zero(self):
        design = lower(
            'module top; initial begin integer i; '
            'i = $rtoi(-2.7); '
            'if ($rtoi(123.9) === 123 && $rtoi(-2.7) === -2) '
            '$display("PASS"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("rtoi_literal")]
        self.assertEqual(len(values), 3)
        self.assertEqual(values[0]["bits"], "1" * 31 + "0")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_rtoi_literal_statement_is_inert(self):
        design = lower(
            'module top; initial begin $rtoi(0.5); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("rtoi_literal_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_rtoi_dynamic_and_out_of_range_stay_loud(self):
        dynamic = lower(
            'module top; real x; initial if ($rtoi(x) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(dynamic)))
        out_of_range = lower(
            'module top; initial if ($rtoi(2147483648.0) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind", "").startswith("CallExpression")
                            for node in nodes(out_of_range)))

    def test_realtobits_literal_uses_ieee_bits(self):
        design = lower(
            'module top; initial if ($realtobits(-2.5) === '
            '64\'hc004000000000000) $display("PASS"); endmodule')
        values = [node for node in nodes(design)
                  if node.get("realtobits_literal")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"],
                         "1100000000000100000000000000000000000000000000000000000000000000")

    def test_realtobits_dynamic_cast_and_overflow_stay_loud(self):
        dynamic = lower(
            'module top; real x; initial if ($realtobits(x) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(dynamic)))
        cast = lower(
            'module top; initial if ($realtobits(shortreal\'(1.0)) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(cast)))
        overflow = lower(
            'module top; initial if ($realtobits(1.0e400) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind", "").startswith("CallExpression")
                            for node in nodes(overflow)))

    def test_realtobits_literal_statement_is_inert(self):
        design = lower(
            'module top; initial begin $realtobits(1.0); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("realtobits_literal_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_shortrealtobits_literal_uses_single_bits(self):
        design = lower(
            'module top; initial if ($shortrealtobits(-2.5) === '
            '32\'hc0200000) $display("PASS"); endmodule')
        values = [node for node in nodes(design)
                  if node.get("shortrealtobits_literal")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "11000000001000000000000000000000")

    def test_shortrealtobits_dynamic_explicit_and_overflow_stay_loud(self):
        dynamic = lower(
            'module top; real x; initial if ($shortrealtobits(x) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(dynamic)))
        explicit = lower(
            'module top; initial if ($shortrealtobits(shortreal\'(1.0)) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(explicit)))
        overflow = lower(
            'module top; initial if ($shortrealtobits(1.0e400) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind", "").startswith("CallExpression")
                            for node in nodes(overflow)))

    def test_shortrealtobits_literal_statement_is_inert(self):
        design = lower(
            'module top; initial begin $shortrealtobits(1.0); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("shortrealtobits_literal_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
