"""Empty zero-argument functions produce their declared default value."""

import unittest
import json
import tempfile
from pathlib import Path

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
    def symbolic(self, source, retain_proc_rewrites=False):
        with tempfile.TemporaryDirectory() as directory:
            source_path = Path(directory) / "top.sv"
            output_path = Path(directory) / "top.sv.json"
            source_path.write_text(source)
            extract.process_symbolic("top", [str(source_path)], [],
                                    str(output_path),
                                    retain_proc_rewrites=retain_proc_rewrites)
            return json.loads(output_path.read_text())["design"]

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

    def test_symbolic_literal_return_is_materialized(self):
        design = self.symbolic(
            "module top(output wire [3:0] y); "
            "function automatic logic [3:0] seven(input logic selector); "
            "return 4'd7; endfunction assign y = seven(1'b0); endmodule")
        values = [node for node in nodes(design)
                  if node.get("literal_function_return")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "0111")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_literal_return_keeps_dynamic_actual_loud(self):
        design = self.symbolic(
            "module top(input logic selector, output wire [3:0] y); "
            "function automatic logic [3:0] seven(input logic x); "
            "return 4'd7; endfunction assign y = seven(selector); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_symbolic_retain_mode_keeps_user_function_call_source_node(self):
        design = self.symbolic(
            "module top(input logic selector, output logic [3:0] y); "
            "function automatic logic [3:0] step(input logic x); "
            "return x ? 4'd2 : 4'd1; endfunction "
            "assign y = step(selector); endmodule",
            retain_proc_rewrites=True)
        calls = [node for node in nodes(design)
                 if node.get("kind") == "FunctionCall"]
        self.assertEqual(len(calls), 1)
        self.assertTrue(calls[0]["symbolic_user_function_retained"])
        self.assertEqual(calls[0]["name"], "step")

    def test_symbolic_constant_expression_return_is_materialized(self):
        design = self.symbolic(
            "module top(output logic [3:0] y); "
            "function automatic logic [3:0] nine(input logic selector); "
            "return 4'd3 + 4'd6; endfunction assign y = nine(1'b0); endmodule")
        values = [node for node in nodes(design)
                  if node.get("literal_function_return")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_parameter_return_stays_symbolic(self):
        design = self.symbolic(
            "module top #(parameter logic [3:0] P=4'd9) "
            "(output logic [3:0] y); "
            "function automatic logic [3:0] choose(input logic selector); "
            "return P; endfunction assign y = choose(1'b0); endmodule")
        values = [node for node in nodes(design)
                  if node.get("literal_function_return")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "ParamRef")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_input_formal_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] id(input logic [3:0] x); "
            "return x; endfunction assign y = id(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Ident")
        self.assertEqual(values[0]["name"], "a")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_input_formal_expression_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "return x + 4'd1; endfunction assign y = bump(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_temporary_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t; t = x + 4'd1; return t; endfunction "
            "assign y = bump(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_initializer_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t = x + 4'd1; return t; endfunction "
            "assign y = bump(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_initializer_implicit_return_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t = x + 4'd1; bump = t; endfunction "
            "assign y = bump(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_assignment_implicit_return_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t; t = x + 4'd1; bump = t; endfunction "
            "assign y = bump(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_assignment_chain_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t; logic [3:0] u; t = x + 4'd1; "
            "u = t + 4'd1; return u; endfunction assign y = bump(a); "
            "endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_assignment_chain_implicit_return_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t; logic [3:0] u; t = x + 4'd1; "
            "u = t + 4'd1; bump = u; endfunction assign y = bump(a); "
            "endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_assignment_three_chain_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t; logic [3:0] u; logic [3:0] v; "
            "t = x + 4'd1; u = t + 4'd1; v = u + 4'd1; "
            "return v; endfunction assign y = bump(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_assignment_three_chain_implicit_return_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t; logic [3:0] u; logic [3:0] v; "
            "t = x + 4'd1; u = t + 4'd1; v = u + 4'd1; "
            "bump = v; endfunction assign y = bump(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_initializer_chain_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t = x + 4'd1; logic [3:0] u = t + 4'd1; "
            "return u; endfunction assign y = bump(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_local_initializer_chain_implicit_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t = x + 4'd1; logic [3:0] u = t + 4'd1; "
            "bump = u; endfunction assign y = bump(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_mixed_local_chain_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t = x + 4'd1; logic [3:0] u; "
            "u = t + 4'd1; return u; endfunction assign y = bump(a); "
            "endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_pure_mixed_local_chain_implicit_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "logic [3:0] t = x + 4'd1; logic [3:0] u; "
            "u = t + 4'd1; bump = u; endfunction assign y = bump(a); "
            "endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Binary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_stateful_function_stays_loud(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "logic [3:0] state; "
            "function automatic logic [3:0] bump(input logic [3:0] x); "
            "state = x; state = state + 4'd1; return state; endfunction "
            "assign y = bump(a); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_symbolic_output_formal_function_stays_loud(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "logic [3:0] tmp; "
            "function automatic logic [3:0] f(input logic [3:0] x, "
            "output logic [3:0] out); out = x; return x + 4'd1; "
            "endfunction always_comb y = f(a, tmp); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_symbolic_ref_formal_function_stays_loud(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "logic [3:0] tmp; "
            "function automatic logic [3:0] f(input logic [3:0] x, "
            "ref logic [3:0] out); out = x; return x + 4'd1; "
            "endfunction always_comb y = f(a, tmp); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_symbolic_discarded_pure_function_call_is_erased(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] id(input logic [3:0] x); "
            "return x; endfunction always_comb begin id(a); y = a; end "
            "endmodule")
        statements = [node for node in nodes(design)
                      if node.get("user_function_statement")]
        self.assertEqual(len(statements), 1)
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_symbolic_conditional_return_is_inlined(self):
        design = self.symbolic(
            "module top(input logic c, input logic [3:0] a, b, "
            "output logic [3:0] y); "
            "function automatic logic [3:0] mux(input logic s, "
            "input logic [3:0] x, z); if (s) return x; else return z; "
            "endfunction assign y = mux(c, a, b); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Ternary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_local_case_function_is_inlined(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] step(input logic [3:0] x); "
            "logic [3:0] t; begin case (x) 4'h0: t = 4'h3; "
            "default: t = 4'hc; endcase return t; end endfunction "
            "assign y = step(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Ternary")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_local_qualified_cases_are_inlined_when_provably_safe(self):
        for qualifier in ("unique", "unique0", "priority"):
            with self.subTest(qualifier=qualifier):
                design = self.symbolic(
                    "module top(input logic [3:0] a, output logic [3:0] y); "
                    "function automatic logic [3:0] step(input logic [3:0] x); "
                    "logic [3:0] t; begin " + qualifier +
                    " case (x) 4'h0: t = 4'h3; 4'h1: t = 4'h4; "
                    "default: t = 4'hc; endcase return t; end endfunction "
                    "assign y = step(a); endmodule")
                values = [node for node in nodes(design)
                          if node.get("user_function_inline")]
                self.assertEqual(len(values), 1)
                self.assertEqual(values[0]["kind"], "Ternary")
                self.assertEqual(values[0]["user_function_case_check"],
                                 qualifier)
                self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                                     for node in nodes(design)))

    def test_symbolic_qualified_case_default_function_name_keeps_local_x(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] step(input logic [3:0] x); "
            "logic [3:0] t; begin unique case (x) 4'h0: t = 4'h3; "
            "default: step = 4'hc; endcase return t; end endfunction "
            "assign y = step(a); endmodule")
        values = [node for node in nodes(design)
                  if node.get("user_function_inline")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["kind"], "Ternary")
        self.assertEqual(values[0]["user_function_case_check"], "unique")
        self.assertEqual(values[0]["else"]["kind"], "Literal")
        self.assertTrue(set(values[0]["else"]["bits"]) == {"x"})
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_symbolic_local_qualified_case_with_duplicate_label_stays_loud(self):
        design = self.symbolic(
            "module top(input logic [3:0] a, output logic [3:0] y); "
            "function automatic logic [3:0] step(input logic [3:0] x); "
            "logic [3:0] t; begin unique case (x) 4'h0: t = 4'h3; "
            "4'h0: t = 4'h4; default: t = 4'hc; endcase return t; "
            "end endfunction assign y = step(a); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_implicit_logic_return_is_materialized_at_call_site(self):
        design = lower(
            'module top; function f; f = 1\'b1; endfunction '
            'initial begin if (f() === 1\'b1) $display("PASS"); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("literal_function_return")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "1")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_implicit_return_statement_is_erased(self):
        design = lower(
            'module top; function int f(); f = 1; endfunction '
            'initial begin f(); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("literal_function_statement") == "f"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_automatic_implicit_return_is_materialized_at_call_site(self):
        design = lower(
            'module top; function automatic f; f = 1\'b1; endfunction '
            'initial begin if (f() === 1\'b1) $display("PASS"); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("literal_function_return")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "1")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_automatic_implicit_return_statement_is_erased(self):
        design = lower(
            'module top; function automatic int f(); f = 1; endfunction '
            'initial begin f(); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("literal_function_statement") == "f"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_literal_return_rejects_dynamic_input(self):
        design = lower(
            'module top; bit selector; function bit [3:0] seven(input bit x); '
            'return 4\'d7; endfunction initial begin '
            'if (seven(selector) == 4\'d7) $display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_literal_return_accepts_named_literal_history_input(self):
        design = lower(
            'module top; bit selector; function bit [3:0] seven(input bit x); '
            'return 4\'d7; endfunction initial begin '
            'selector = 1\'b0; if (seven(selector) == 4\'d7) $display("PASS"); '
            'selector = 1\'b1; if (seven(selector) == 4\'d7) $display("PASS"); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("literal_function_return")]
        self.assertEqual(len(values), 2)
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_literal_return_rejects_computed_named_input_history(self):
        design = lower(
            'module top; bit selector; function bit [3:0] seven(input bit x); '
            'return 4\'d7; endfunction initial begin '
            'selector = 1\'b0; selector = selector ^ 1\'b1; '
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

    def test_literal_return_statement_accepts_pure_computed_input(self):
        design = lower(
            'module top; function bit [3:0] seven(input bit x); '
            'return 4\'d7; endfunction initial seven(1\'b1 + 1\'b0); endmodule')
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

    def test_itor_literal_statement_is_inert(self):
        design = lower(
            'module top; initial begin $itor(-17); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("itor_literal_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_itor_dynamic_statement_is_inert(self):
        design = lower(
            'module top; integer value; initial begin $itor(value); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("itor_pure_statement")
                            for node in nodes(design)))

    def test_itor_pure_computed_statement_is_inert(self):
        design = lower(
            'module top; integer value; initial begin value = 3; '
            '$itor(value + 2); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("itor_pure_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_itor_effectful_computed_statement_stays_loud(self):
        design = lower(
            'module top; integer value; initial begin '
            '$itor(value++); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_bitstoreal_literal_statement_is_inert(self):
        design = lower(
            'module top; initial begin $bitstoreal(64\'h3ff8_0000_0000_0000); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("bitstoreal_literal_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_bitstoreal_dynamic_statement_is_inert(self):
        design = lower(
            'module top; logic [63:0] bits; initial begin $bitstoreal(bits); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("bitstoreal_pure_statement")
                            for node in nodes(design)))

    def test_bitstoreal_pure_computed_statement_is_inert(self):
        design = lower(
            'module top; logic [63:0] bits; initial begin bits = 64\'h1; '
            '$bitstoreal(bits | 64\'h2); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("bitstoreal_pure_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_bitstoreal_wrong_width_stays_loud(self):
        design = lower(
            'module top; logic [31:0] bits; initial begin '
            '$bitstoreal(bits); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_bitstoreal_effectful_statement_stays_loud(self):
        design = lower(
            'module top; logic [63:0] bits; initial begin '
            '$bitstoreal(bits++); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_bitstoshortreal_literal_statement_is_inert(self):
        design = lower(
            'module top; initial begin $bitstoshortreal(32\'h3fc0_0000); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("bitstoshortreal_literal_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_bitstoshortreal_dynamic_statement_is_inert(self):
        design = lower(
            'module top; logic [31:0] bits; initial begin $bitstoshortreal(bits); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("bitstoshortreal_pure_statement")
                            for node in nodes(design)))

    def test_bitstoshortreal_pure_computed_statement_is_inert(self):
        design = lower(
            'module top; logic [31:0] bits; initial begin bits = 32\'h1; '
            '$bitstoshortreal(bits | 32\'h2); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("bitstoshortreal_pure_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_bitstoshortreal_wrong_width_stays_loud(self):
        design = lower(
            'module top; logic [63:0] bits; initial begin '
            '$bitstoshortreal(bits); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_bitstoshortreal_effectful_statement_stays_loud(self):
        design = lower(
            'module top; logic [31:0] bits; initial begin '
            '$bitstoshortreal(bits++); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_realtobits_pure_operand_statement_is_inert(self):
        design = lower(
            'module top; real value; initial begin $realtobits(value); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("realtobits_pure_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_realtobits_nested_pure_math_statement_is_inert(self):
        design = lower(
            'module top; initial begin $realtobits($sqrt(16.0)); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("realtobits_pure_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_realtobits_effectful_operand_stays_loud(self):
        design = lower(
            'module top; integer value; initial begin '
            '$realtobits($sqrt(value++)); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_shortrealtobits_pure_operand_statement_is_inert(self):
        design = lower(
            'module top; real value; initial begin $shortrealtobits(value); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("shortrealtobits_pure_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_shortrealtobits_effectful_operand_stays_loud(self):
        design = lower(
            'module top; integer value; initial begin '
            '$shortrealtobits($sqrt(value++)); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_rtoi_pure_operand_statement_is_inert(self):
        design = lower(
            'module top; real value; initial begin $rtoi(value); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("rtoi_pure_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_rtoi_nested_pure_math_statement_is_inert(self):
        design = lower(
            'module top; initial begin $rtoi($sqrt(16.0)); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("rtoi_pure_statement")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_rtoi_effectful_operand_stays_loud(self):
        design = lower(
            'module top; integer value; initial begin '
            '$rtoi($sqrt(value++)); $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_rtoi_literal_itor_conversion_is_exact(self):
        design = lower(
            'module top; initial if ($rtoi($itor(-17)) === -17) '
            '$display("PASS"); endmodule')
        values = [node for node in nodes(design)
                  if node.get("rtoi_literal")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "1" * 27 + "01111")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_rtoi_named_real_literal_history_is_exact(self):
        design = lower(
            'module top; real positive; real negative; initial begin '
            'positive = 123.9; negative = -2.7; '
            'if ($rtoi(positive) === 123 && $rtoi(negative) === -2) '
            '$display("PASS"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("rtoi_literal")]
        self.assertEqual(len(values), 2)
        self.assertEqual(values[0]["bits"], "0" * 24 + "01111011")
        self.assertEqual(values[1]["bits"], "1" * 31 + "0")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_rtoi_named_real_dynamic_history_stays_loud(self):
        design = lower(
            'module top; real value; real other; initial begin '
            'value = 3.5; other = value; '
            'if ($rtoi(other) === 3) $display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_rtoi_itor_dynamic_input_stays_loud(self):
        design = lower(
            'module top; integer value; initial if ($rtoi($itor(value)) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_rtoi_itor_named_literal_history_is_exact(self):
        design = lower(
            'module top; integer value; initial begin value = -17; '
            'if ($rtoi($itor(value)) === -17) $display("PASS"); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("rtoi_literal")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "1" * 27 + "01111")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_rtoi_itor_named_control_write_stays_loud(self):
        design = lower(
            'module top; integer value; initial begin value = 1; '
            'if (1) value = 2; if ($rtoi($itor(value)) === 2) '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
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

    def test_realtobits_literal_itor_conversion_is_exact(self):
        design = lower(
            'module top; initial if ($realtobits($itor(-17)) === '
            '64\'hc031000000000000) $display("PASS"); endmodule')
        values = [node for node in nodes(design)
                  if node.get("realtobits_literal")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"],
                         "1100000000110001000000000000000000000000000000000000000000000000")

    def test_realtobits_itor_dynamic_input_stays_loud(self):
        design = lower(
            'module top; integer value; initial if ($realtobits($itor(value)) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_realtobits_itor_named_literal_history_is_exact(self):
        design = lower(
            'module top; integer value; initial begin value = -17; '
            'if ($realtobits($itor(value)) === '
            "64'hc031000000000000) $display(\"PASS\"); endmodule")
        values = [node for node in nodes(design)
                  if node.get("realtobits_literal")]
        self.assertEqual(len(values), 1)
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_realtobits_itor_named_computed_history_stays_loud(self):
        design = lower(
            'module top; integer value; integer other; initial begin '
            'value = 17; other = value; '
            'if ($realtobits($itor(other)) === 0) $display("PASS"); '
            'end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

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

    def test_shortrealtobits_literal_itor_conversion_is_exact(self):
        design = lower(
            'module top; initial if ($shortrealtobits($itor(-17)) === '
            '32\'hc1880000) $display("PASS"); endmodule')
        values = [node for node in nodes(design)
                  if node.get("shortrealtobits_literal")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"],
                         "11000001100010000000000000000000")

    def test_shortrealtobits_itor_dynamic_input_stays_loud(self):
        design = lower(
            'module top; integer value; initial if ($shortrealtobits($itor(value)) === 0) '
            '$display("PASS"); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

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

    def test_realtobits_literal_bound_name_is_exact(self):
        design = lower(
            'module top; logic [63:0] bits; real value; initial begin '
            'value = -2.5; bits = $realtobits(value); end endmodule')
        literals = [node for node in nodes(design)
                    if node.get("realtobits_literal")]
        self.assertEqual(len(literals), 1)
        self.assertEqual(literals[0]["bits"],
                         "1100000000000100000000000000000000000000000000000000000000000000")

    def test_shortrealtobits_literal_bound_name_is_exact(self):
        design = lower(
            'module top; logic [31:0] bits; shortreal value = 1.0; initial '
            'bits = $shortrealtobits(value); end endmodule')
        literals = [node for node in nodes(design)
                    if node.get("shortrealtobits_literal")]
        self.assertEqual(len(literals), 1)
        self.assertEqual(literals[0]["bits"],
                         "00111111100000000000000000000000")

    def test_literal_bound_real_control_write_stays_loud(self):
        design = lower(
            'module top; logic [63:0] bits; real value; initial begin '
            'value = 1.0; if (1) value = 2.0; bits = $realtobits(value); '
            'end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            and "$realtobits" in node.get("text", "")
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
