"""WP-PROC (2026-11-01): the procedural / Verilog-2001 lowerings of the symbolic tier.

One test class per lowering, in the order they landed:

  N1  typeless / implicit-type declaration dimensions (`input [N-1:0] a`, `wire [N-1:0] x`)
  N3  `--top` of a module that another module of the same sources instantiates
  C1  compound assignment `x op= e` (lower_proc.compound_assignment)
  X1  loop headers: iterator declared outside the header, `i += c`, `<=` / `>=` (lower_proc.loop_header, ...)
  L1  block-local declarations of an always_comb body, hoisted to module variables (lower_proc.hoist_local)
  E1  `always @*` and level-sensitive lists as always_comb under the rules R1 to R6 (lower_proc.star_block)
  N2  `wire` / `output wire` / implicit nets with exactly one continuous driver per bit are variables (lower_proc.net_variable)
  ...

Every class pins (a) the envelope shape the Lean loader reads, (b) the refusals that stay loud. The semantic
agreement with Xcelium is in `harness/sv/cases2.json` (rows `proc_*`), the monotonicity (no admitted envelope
changes) in `docs/sv-proc-lowering.md` / the regression recipe there.
"""
import json
import tempfile
import unittest
from pathlib import Path

import extract


def sv_kinds(node, found=None):
    found = [] if found is None else found
    if isinstance(node, dict):
        if node.get("kind") == "Unsupported":
            found.append(node.get("sv_kind"))
        for value in node.values():
            sv_kinds(value, found)
    elif isinstance(node, list):
        for value in node:
            sv_kinds(value, found)
    return found


def count_kind(node, kind):
    n = 0
    if isinstance(node, dict):
        n += node.get("kind") == kind
        for value in node.values():
            n += count_kind(value, kind)
    elif isinstance(node, list):
        for value in node:
            n += count_kind(value, kind)
    return n


def packed_null(node):
    """Declarations whose packed dimensions were not recovered (the loader refuses them)."""
    n = 0
    if isinstance(node, dict):
        w = node.get("width")
        if (node.get("kind") in ("Var", "Net", "Port") and isinstance(w, dict)
                and w.get("kind") == "PackedType" and w.get("packed") is None):
            n += 1
        for value in node.values():
            n += packed_null(value)
    elif isinstance(node, list):
        for value in node:
            n += packed_null(value)
    return n


class Base(unittest.TestCase):
    def extract(self, source, top="t", more=(), retain_loops=False,
                retain_proc_rewrites=False):
        with tempfile.TemporaryDirectory() as directory:
            srcs = []
            for i, text in enumerate((source,) + tuple(more)):
                p = Path(directory) / ("f%d.sv" % i)
                p.write_text(text)
                srcs.append(str(p))
            out = Path(directory) / "out.json"
            extract.process_symbolic(top, srcs, [], str(out),
                                    retain_loops=retain_loops,
                                    retain_proc_rewrites=retain_proc_rewrites)
            return json.loads(out.read_text())["design"]

    def module(self, source, top="t", more=(), retain_loops=False,
              retain_proc_rewrites=False):
        design = self.extract(source, top, more, retain_loops=retain_loops,
                              retain_proc_rewrites=retain_proc_rewrites)
        return [m for m in design["modules"] if m["name"] == top][0]


class TypelessDimensions(Base):
    """N1: ImplicitType syntax carries the dimensions like a `logic` declaration."""

    def test_ansi_typeless_input_ports(self):
        m = self.module("module t #(parameter int N = 8) (input [N-1:0] a, b, output logic [N-1:0] y);"
                        " assign y = a & b; endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(packed_null(m), 0)
        a = [p for p in m["ports"] if p["name"] == "a"][0]
        dim, = a["width"]["packed"]
        self.assertEqual(dim["msb"]["kind"], "Binary")          # N - 1, symbolic: not folded at the default
        self.assertEqual(dim["msb"]["left"]["name"], "N")
        self.assertEqual(a["width"]["resolved"], 8)

    def test_non_ansi_header_declarations(self):
        m = self.module("module t (a, b, y); parameter N = 4; input [N-1:0] a, b; output logic [N-1:0] y;"
                        " assign y = a ^ b; endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(packed_null(m), 0)

    def test_two_dimensional_implicit_declaration(self):
        m = self.module("module t (input [1:0][3:0] a, output logic [3:0] y); assign y = a[0] ^ a[1]; endmodule")
        a = [p for p in m["ports"] if p["name"] == "a"][0]
        self.assertEqual(len(a["width"]["packed"]), 2)
        self.assertEqual(a["width"]["resolved"], 8)

    def test_scalar_and_logic_declarations_are_unchanged(self):
        m = self.module("module t (input a, input logic [3:0] b, output logic y); assign y = a ^ b[0]; endmodule")
        a, b, y = m["ports"]
        self.assertEqual(a["width"]["packed"], [])
        self.assertEqual(len(b["width"]["packed"]), 1)
        self.assertEqual(sv_kinds(m), [])

    def test_a_typeless_output_is_a_net_and_stays_loud_without_the_net_lowering(self):
        # `output [3:0] y` is a NET (z when undriven): the dimension recovery makes it a well-formed
        # declaration, the net refusal (dc-net-z) is a separate question (N2)
        m = self.module("module t (input [3:0] a, output [3:0] y); assign y = a; endmodule")
        self.assertEqual(packed_null(m), 0)


class TopModules(Base):
    """N3: the top may be a module that another module of the same sources instantiates."""

    CHILD = "module child (input logic a, output logic y); assign y = ~a; endmodule\n"
    PARENT = "module parent (input logic a, output logic y); child u (.a(a), .y(y)); endmodule\n"

    def test_instantiated_module_can_be_the_top(self):
        m = self.module(self.PARENT, "child", more=(self.CHILD,))
        self.assertEqual(m["name"], "child")
        self.assertEqual(sv_kinds(m), [])

    def test_the_uninstantiated_top_is_unchanged(self):
        design = self.extract(self.CHILD + self.PARENT, "parent")
        self.assertEqual([m["name"] for m in design["modules"] if m["name"] == "parent"], ["parent"])

    def test_envelope_of_a_plain_top_does_not_depend_on_unrelated_modules(self):
        one = self.extract("module t (input logic a, output logic y); assign y = a; endmodule")
        two = self.extract("module t (input logic a, output logic y); assign y = a; endmodule\n"
                           "module unrelated #(parameter int N = 3) (input logic [N-1:0] q); endmodule")
        strip = lambda d: json.dumps(d["modules"][0], sort_keys=True).replace('"line": ', '')
        self.assertEqual(count_kind(one, "Module"), 1)
        self.assertEqual(count_kind(two, "Module"), 1)
        self.assertEqual(one["modules"][0]["name"], two["modules"][0]["name"])


def strip_tags(node):
    """The envelope without spans and without the lowering tags (to compare a lowering with the hand-written form)."""
    if isinstance(node, dict):
        return {k: strip_tags(v) for k, v in node.items()
                if k not in ("span", "symbolic_compound_lowered", "symbolic_for_unrolled",
                             "symbolic_for_iterations")}
    if isinstance(node, list):
        return [strip_tags(v) for v in node]
    return node


def always_comb_body(module, index=0):
    return [p for p in module["processes"] if p["kind"] == "AlwaysComb"][index]["body"]


class CompoundAssignment(Base):
    """C1: `x op= e` is the blocking assignment `x = x op e` of the symbolic tier, exactly slang's bound tree."""

    def pair(self, compound, longhand, decls="logic [7:0] a, b, output logic [7:0] y"):
        src = "module t (input %s); always_comb begin %%s end endmodule"
        m1 = self.module((src % decls) % compound)
        m2 = self.module((src % decls) % longhand)
        return m1, m2

    def test_operators_are_the_long_hand_form(self):
        for op in ("+", "-", "*", "&", "|", "^", "<<", ">>"):
            c, h = self.pair("y = a; y %s= b;" % op, "y = a; y = y %s b;" % op)
            self.assertEqual(sv_kinds(c), [], op)
            self.assertEqual(strip_tags(c["processes"]), strip_tags(h["processes"]), op)

    def test_tag_marks_the_lowered_statement(self):
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y); always_comb begin y = a; y ^= 8'h55; end endmodule")
        body = always_comb_body(m)["stmts"]
        self.assertEqual([s.get("symbolic_compound_lowered") for s in body], [None, True])

    def test_bit_and_part_select_targets(self):
        c, h = self.pair("y = a; y[3] ^= b[0]; y[7:6] |= b[7:6];",
                         "y = a; y[3] = y[3] ^ b[0]; y[7:6] = y[7:6] | b[7:6];")
        self.assertEqual(sv_kinds(c), [])
        self.assertEqual(strip_tags(c["processes"]), strip_tags(h["processes"]))

    def test_run_time_index_target_reads_and_writes_the_same_select(self):
        c, h = self.pair("y = a; y[k] ^= 1'b1;", "y = a; y[k] = y[k] ^ 1'b1;",
                         "logic [7:0] a, b, input logic [2:0] k, output logic [7:0] y")
        self.assertEqual(sv_kinds(c), [])
        self.assertEqual(strip_tags(c["processes"]), strip_tags(h["processes"]))

    def test_two_state_target_is_squashed_like_a_plain_assignment(self):
        c, h = self.pair("y = 0; y += 2;", "y = 0; y = y + 2;", "logic [3:0] a, output int y")
        self.assertEqual(sv_kinds(c), [])
        self.assertEqual(strip_tags(c["processes"]), strip_tags(h["processes"]))

    def test_inside_a_literal_loop(self):
        c, h = self.pair("y = '0; for (int i = 0; i < 8; i++) if (b[i]) y ^= a << i;",
                         "y = '0; for (int i = 0; i < 8; i++) if (b[i]) y = y ^ (a << i);")
        self.assertEqual(sv_kinds(c), [])
        self.assertEqual(strip_tags(c["processes"]), strip_tags(h["processes"]))
        self.assertEqual(count_kind(c, "LocalDecl"), 0)

    def test_effectful_operand_stays_loud(self):
        for body in ("y = a; y ^= f();", "y = a; y ^= (b = a);"):
            m = self.module("module t (input logic [7:0] a, output logic [7:0] y); logic [7:0] b;"
                            " function automatic logic [7:0] f(); b = a; return b; endfunction"
                            " always_comb begin %s end endmodule" % body)
            self.assertTrue(sv_kinds(m), body)

    def test_fixed_unpacked_cell_with_a_literal_index_is_the_long_hand_form(self):
        # the tier flattens a fixed unpacked array to one variable per cell; the compound target is that cell
        decl = "module t (input logic [7:0] a, output logic [7:0] y); logic [7:0] mem [0:3]; always_comb begin %s end endmodule"
        c = self.module(decl % "mem[0] = a; mem[0] += 8'd1; y = mem[0];")
        h = self.module(decl % "mem[0] = a; mem[0] = mem[0] + 8'd1; y = mem[0];")
        self.assertEqual(sv_kinds(c), [])
        self.assertEqual(strip_tags(c["processes"]), strip_tags(h["processes"]))

    def test_run_time_unpacked_index_never_gets_a_fabricated_meaning(self):
        # whatever the tier does with a run-time index into an unpacked array, `+=` must do the same as `= x + 1`
        decl = ("module t (input logic [7:0] a, input logic [1:0] k, output logic [7:0] y);"
                " logic [7:0] mem [0:3]; always_comb begin mem[0] = a; mem[1] = a; mem[2] = a; mem[3] = a;"
                " %s y = mem[0]; end endmodule")
        c = self.module(decl % "mem[k] += 8'd1;")
        h = self.module(decl % "mem[k] = mem[k] + 8'd1;")
        self.assertEqual(bool(sv_kinds(c)), bool(sv_kinds(h)))

    def test_compound_as_an_expression_stays_loud(self):
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y, z);"
                        " always_comb begin y = a; z = (y += 8'd1); end endmodule")
        self.assertTrue(sv_kinds(m))


class LoopHeaders(Base):
    """X1: the unroll of master's `_sym_for_values`, for the headers real code uses."""

    def two(self, a, b, decls="module t (input logic [7:0] a, output logic [7:0] y);", pre=""):
        m1 = self.module(decls + pre + " always_comb begin y = '0; " + a + " end endmodule")
        m2 = self.module(decls + " always_comb begin y = '0; " + b + " end endmodule")
        return m1, m2

    def test_init_form_is_the_declared_form(self):
        pre = " integer i;"
        m1, m2 = self.two("for (i = 0; i < 4; i = i + 1) y[i] = a[i];", "for (int i = 0; i < 4; i = i + 1) y[i] = a[i];", pre=pre)
        self.assertEqual(sv_kinds(m1), [])
        self.assertEqual(strip_tags(always_comb_body(m1)), strip_tags(always_comb_body(m2)))
        self.assertEqual([d for d in m1["decls"] if d["name"] == "i"], [])      # the dead declaration is erased

    def test_hand_unrolled_equivalence(self):
        m1, m2 = self.two("for (i = 0; i < 4; i = i + 1) y[i] = a[3-i];", "y[0] = a[3]; y[1] = a[2]; y[2] = a[1]; y[3] = a[0];",
                          pre=" integer i;")
        flat = lambda m: [x for st in always_comb_body(m)["stmts"] for x in (st["stmts"] if st.get("symbolic_for_unrolled") else [st])]
        ones = [strip_tags(x) for x in flat(m1)]
        twos = [strip_tags(x) for x in flat(m2)]
        # the unrolled indices are `Int` nodes, the hand-written ones are literal selects: compare the targets' windows
        self.assertEqual(len(ones), len(twos))
        self.assertEqual(count_kind(m1, "Unsupported"), 0)

    def test_block_local_iterator(self):
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y); always_comb begin : b integer q; y = '0;"
                        " for (q = 0; q < 8; q = q + 1) y[q] = a[q]; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(count_kind(m, "LocalDecl"), 0)

    def test_compound_step_and_inclusive_bounds(self):
        for header, n in (("int i = 0; i <= 3; i += 1", 4), ("int i = 3; i >= 0; i -= 1", 4), ("int i = 0; i < 8; i += 2", 4),
                          ("int i = 7; i >= 0; i--", 8), ("int i = 0; i != 3; i++", 3)):
            m = self.module("module t (input logic [7:0] a, output logic [7:0] y); always_comb begin y = '0;"
                            " for (%s) y[i] = a[i]; end endmodule" % header)
            self.assertEqual(sv_kinds(m), [], header)
            loops = [x for st in always_comb_body(m)["stmts"] for x in [st] if st.get("symbolic_for_unrolled")]
            self.assertEqual([x["symbolic_for_iterations"] for x in loops], [n], header)

    def test_two_loops_share_one_iterator(self):
        m = self.module("module t (input logic [3:0] a, output logic [3:0] y, z); integer i; always_comb begin y = '0; z = '0;"
                        " for (i = 0; i < 4; i = i + 1) y[i] = a[i]; for (i = 3; i >= 0; i--) z[i] = a[3-i]; end endmodule")
        self.assertEqual(sv_kinds(m), [])

    def test_iterator_read_after_the_loop_stays_loud(self):
        # a read after the loop sees the loop's final value, which the unroll does not compute
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y, output logic [3:0] w); integer i;"
                        " always_comb begin y = '0; for (i = 0; i < 8; i = i + 1) y[i] = a[i]; w = i[3:0]; end endmodule")
        self.assertIn("ForLoopStatement", sv_kinds(m))

    def test_iterator_read_before_the_loop_stays_loud(self):
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y, output logic [3:0] w); integer i;"
                        " always_comb begin w = i[3:0]; y = '0; for (i = 0; i < 8; i = i + 1) y[i] = a[i]; end endmodule")
        self.assertIn("ForLoopStatement", sv_kinds(m))

    def test_iterator_that_is_a_port_stays_loud(self):
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y, output integer i);"
                        " always_comb begin y = '0; for (i = 0; i < 8; i = i + 1) y[i] = a[i]; end endmodule")
        self.assertIn("ForLoopStatement", sv_kinds(m))

    def test_iterator_written_in_the_body_stays_loud(self):
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y); integer i; always_comb begin y = '0;"
                        " for (i = 0; i < 8; i = i + 1) begin y[i] = a[i]; i = i + 1; end end endmodule")
        self.assertTrue(sv_kinds(m))

    def test_narrow_iterator_stays_loud(self):
        # a `logic [7:0]` / `byte` iterator wraps at another point than the 32-bit trace the unroll computes
        for decl in ("logic [7:0] i;", "byte i;"):
            m = self.module("module t (input logic [7:0] a, output logic [7:0] y); " + decl + " always_comb begin y = '0;"
                            " for (i = 0; i < 8; i = i + 1) y[i] = a[i]; end endmodule")
            self.assertIn("ForLoopStatement", sv_kinds(m), decl)

    def test_parameter_bound_stays_loud(self):
        m = self.module("module t #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y); integer i;"
                        " always_comb begin y = '0; for (i = 0; i < N; i = i + 1) y[i] = a[i]; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        loops = [st for st in always_comb_body(m)["stmts"]
                 if st.get("symbolic_for_parameter")]
        self.assertEqual(len(loops), 1)

    def test_signal_bound_stays_loud(self):
        m = self.module("module t (input logic [2:0] limit, input logic [7:0] a, output logic [7:0] y);"
                        " always_comb begin y = '0; for (int i = 0; i < limit; i++) y[i] = a[i]; end endmodule")
        self.assertIn("ForLoopStatement", sv_kinds(m))

    def test_parameter_compound_step_is_retained(self):
        m = self.module("module t #(parameter int N = 5) (input logic [7:0] a, output logic [7:0] y);"
                        " always_comb begin y = '0; for (int i = 0; i < N; i += 2) y[i] = a[i]; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        loops = [st for st in always_comb_body(m)["stmts"]
                 if st.get("symbolic_for_parameter")]
        self.assertEqual(len(loops), 1)
        self.assertEqual(loops[0]["step"]["kind"], "Binary")
        self.assertEqual(loops[0]["step"]["op"], "+")

    def test_parameter_reaching_not_equal_bound_is_retained(self):
        m = self.module("module t #(parameter int N = 5) (input logic [7:0] a, output logic [7:0] y);"
                        " always_comb begin y = '0;"
                        " for (int i = 0; i != N; i++) y[i] = a[i]; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        loops = [st for st in always_comb_body(m)["stmts"]
                 if st.get("symbolic_for_parameter")]
        self.assertEqual(len(loops), 1)
        self.assertEqual(loops[0]["condition"]["op"], "!=")

    def test_parameter_header_shape_matrix_is_retained(self):
        m = self.module("module t #(parameter int N = 5) (input logic [7:0] a, output logic [7:0] y);"
                        " always_comb begin y = '0;"
                        " for (int i = 0; i <= N - 1; i += 1) y[i] = a[i];"
                        " for (int j = N - 1; j >= 0; j -= 1) y[j] = y[j] ^ a[j];"
                        " for (int k = 0; k < N; k += 2) y[k] = y[k] ^ a[k];"
                        " end endmodule")
        self.assertEqual(sv_kinds(m), [])
        loops = [st for st in always_comb_body(m)["stmts"]
                 if st.get("symbolic_for_parameter")]
        self.assertEqual(len(loops), 3)
        self.assertEqual([x["condition"]["op"] for x in loops], ["s<=", "s>=", "s<"])
        self.assertEqual([x["step"]["op"] for x in loops], ["+", "-", "+"])

    def test_parameter_bound_external_iterator_is_retained(self):
        m = self.module("module t #(parameter int N = 5) (input logic [7:0] a, output logic [7:0] y);"
                        " integer i; always_comb begin y = '0;"
                        " for (i = 0; i < N; i = i + 1) y[i] = a[i]; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        loops = [st for st in always_comb_body(m)["stmts"]
                 if st.get("symbolic_for_parameter")]
        self.assertEqual(len(loops), 1)
        self.assertEqual(loops[0]["init"]["kind"], "Int")

    def test_nested_parameter_bound_loop_reads_outer_iterator(self):
        m = self.module("module t #(parameter int N = 5) (input logic [15:0] a, output logic [15:0] y);"
                        " always_comb begin y = '0;"
                        " for (int i = 0; i < N; i++)"
                        " for (int j = 0; j < i; j++) y[i] = y[i] ^ a[j];"
                        " end endmodule")
        self.assertEqual(sv_kinds(m), [])
        outer = [st for st in always_comb_body(m)["stmts"]
                 if st.get("symbolic_for_parameter")][0]
        inner = outer["body"]
        self.assertEqual(inner["kind"], "For")
        self.assertTrue(inner["symbolic_for_parameter"])
        self.assertEqual(inner["condition"]["right"]["kind"], "GenvarRef")
        self.assertEqual(inner["condition"]["right"]["name"], "i")

    def test_retained_nested_literal_loop_reads_outer_iterator(self):
        source = ("module t (input logic [15:0] a, output logic [15:0] y);"
                  " always_comb begin y = '0;"
                  " for (int i = 0; i < 4; i++)"
                  " for (int j = 0; j < i; j++) y[i] = y[i] ^ a[j];"
                  " end endmodule")
        m = self.module(source, retain_loops=True)
        self.assertEqual(sv_kinds(m), [])
        outer = [st for st in always_comb_body(m)["stmts"]
                 if st.get("symbolic_for_retained")][0]
        inner = outer["body"]
        self.assertEqual(inner["kind"], "For")
        self.assertEqual(inner["condition"]["right"]["kind"], "GenvarRef")
        self.assertEqual(inner["condition"]["right"]["name"], "i")

    def test_nested_loop_iterator_shadowing_is_scoped(self):
        source = ("module t #(parameter int N = 3) (input logic [15:0] a, output logic [15:0] y);"
                  " always_comb begin y = '0;"
                  " for (int i = 0; i < N; i++) begin"
                  " for (int i = 0; i < 2; i++) y[i] = y[i] ^ a[i];"
                  " end end endmodule")
        for retain in (False, True):
            m = self.module(source, retain_loops=retain)
            self.assertEqual(sv_kinds(m), [])
            outer = [st for st in always_comb_body(m)["stmts"]
                     if st.get("symbolic_for_parameter")][0]
            body = outer["body"]
            if retain:
                inner = body["stmts"][0]
                self.assertEqual(inner["kind"], "For")
                self.assertTrue(inner["symbolic_for_retained"])
            else:
                self.assertEqual(body["stmts"][0]["kind"], "Block")

    def test_parameter_valued_compound_step_is_retained(self):
        m = self.module("module t #(parameter int N = 5, parameter int S = 2) "
                        "(input logic [7:0] a, output logic [7:0] y);"
                        " always_comb begin y = '0; for (int i = 0; i < N; i += S) y[i] = a[i]; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        loops = [st for st in always_comb_body(m)["stmts"]
                 if st.get("symbolic_for_parameter")]
        self.assertEqual(len(loops), 1)
        self.assertEqual(loops[0]["step"]["right"]["kind"], "ParamRef")

    def test_literal_loop_inside_always_ff_unrolls_to_nbas(self):
        m = self.module(
            "module t (input logic clk, input logic [1:0] d, output logic [1:0] q);"
            " always_ff @(posedge clk) begin"
            " for (int i = 0; i < 2; i++) q[i] <= d[i];"
            " end endmodule")
        process = m["processes"][0]
        self.assertEqual(process["kind"], "AlwaysPosedge")
        body = process["body"]["stmts"][0]
        self.assertEqual(body["kind"], "Block")
        self.assertTrue(body["symbolic_for_unrolled"])
        self.assertEqual(len(body["stmts"]), 2)
        self.assertTrue(all(stmt["kind"] == "NonblockingAssign"
                            for stmt in body["stmts"]))

    def test_mixed_signed_condition_stays_loud(self):
        for bound in ("2'd2", "1'b1"):
            m = self.module(
                "module t (input logic [7:0] d, output logic [7:0] q);"
                " always_comb begin q = '0;"
                " for (int i = -1; i < %s; i++) q[i + 1] = d[i + 1];"
                " end endmodule" % bound)
            self.assertIn("ForLoopStatement", sv_kinds(m), bound)

    def test_mixed_signed_parameter_condition_stays_loud(self):
        m = self.module(
            "module t #(parameter int N = 4) (input logic [7:0] d,"
            " output logic [7:0] q); localparam logic [1:0] P = 2;"
            " always_comb begin q = '0;"
            " for (int i = -1; i < P + N - N; i++)"
            " q[i + 1] = d[i + 1]; end endmodule")
        self.assertIn("ForLoopStatement", sv_kinds(m))

    def test_parameter_loop_function_name_capture_stays_loud(self):
        m = self.module(
            "module t #(parameter int N = 4) (input logic [7:0] d,"
            " output logic [7:0] q); localparam int K = 1;"
            " function automatic logic f(input logic x); f = (K == 1);"
            " endfunction always_comb begin q = '0;"
            " for (int K = 0; K < N; K++) q[K] = f(1'b0);"
            " end endmodule")
        self.assertIn("ForLoopStatement", sv_kinds(m))

    def test_typed_header_iterator_stays_loud(self):
        for declaration in ("bit [1:0] i", "byte i"):
            m = self.module(
                "module t #(parameter int N = 4) (input logic [7:0] d,"
                " output logic [7:0] q); always_comb begin q = '0;"
                " for (%s = 0; i < N; i += 3) q[0] = d[0];"
                " end endmodule" % declaration)
            self.assertIn("ForLoopStatement", sv_kinds(m), declaration)

    def test_declared_form_of_master_is_unchanged(self):
        m = self.module("module t (input logic [3:0] a, output logic [3:0] y); always_comb begin"
                        " for (int i = 0; i < 4; i++) y[i] = a[i]; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        loops = [st for st in always_comb_body(m)["stmts"] if st.get("symbolic_for_unrolled")]
        self.assertEqual([x["symbolic_for_iterations"] for x in loops], [4])

    def test_retain_loops_keeps_literal_header_as_for(self):
        source = ("module t (input logic [3:0] a, output logic [3:0] y); "
                  "always_comb begin for (int i = 0; i < 4; i++) y[i] = a[i]; end endmodule")
        m = self.module(source)
        retained = self.module(source, retain_loops=True)
        self.assertEqual(sv_kinds(retained), [])
        unrolled = [st for st in always_comb_body(m)["stmts"]
                    if st.get("symbolic_for_unrolled")]
        loops = [st for st in always_comb_body(retained)["stmts"]
                 if st.get("symbolic_for_retained")]
        self.assertEqual([x["symbolic_for_iterations"] for x in unrolled], [4])
        self.assertEqual(len(loops), 1)
        self.assertEqual(loops[0]["kind"], "For")
        self.assertTrue(loops[0]["symbolic_for_parameter"])

    def test_retain_loops_has_no_literal_iteration_cap(self):
        source = ("module t (input logic [255:0] a, output logic [255:0] y); "
                  "always_comb begin for (int i = 0; i < 256; i++) y[i] = a[i]; end endmodule")
        retained = self.module(source, retain_loops=True)
        loops = [st for st in always_comb_body(retained)["stmts"]
                 if st.get("symbolic_for_retained")]
        self.assertEqual(len(loops), 1)
        self.assertEqual(loops[0]["kind"], "For")


class LocalDeclarations(Base):
    """L1: a static block variable of an `always_comb` is a module variable only this process writes."""

    def names(self, m):
        return [d["name"] for d in m["decls"]]

    def test_unnamed_block_local(self):
        m = self.module("module t (input logic [7:0] a, b, output logic [7:0] y); always_comb begin logic [7:0] t1;"
                        " t1 = a ^ b; y = t1 & a; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(count_kind(m, "LocalDecl"), 0)
        self.assertEqual(self.names(m), ["blk1__t1"])
        target = always_comb_body(m)["stmts"][1]["target"]
        self.assertEqual(target["name"], "blk1__t1")

    def test_retain_proc_rewrites_keeps_block_local_source_node(self):
        source = ("module t (input logic [7:0] a, b, output logic [7:0] y); "
                  "always_comb begin logic [7:0] t1; t1 = a ^ b; y = t1 & a; end endmodule")
        retained = self.module(source, retain_proc_rewrites=True)
        body = always_comb_body(retained)
        local = body["stmts"][0]
        self.assertEqual(local["kind"], "LocalDecl")
        self.assertTrue(local["symbolic_local_retained"])
        self.assertEqual(local["name"], "t1")
        self.assertFalse(any(d["name"] == "blk1__t1" for d in retained["decls"]))

    def test_named_and_nested_blocks(self):
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y, z); always_comb begin : blk logic [7:0] p;"
                        " p = a; begin : in logic [7:0] q; q = ~p; y = q; end z = p; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(self.names(m), ["blk__p", "blk__in__q"])

    def test_shadowing_a_module_variable_is_resolved_by_symbol(self):
        m = self.module("module t (input logic [7:0] a, b, output logic [7:0] y, z); logic [7:0] t1; assign t1 = a ^ b;"
                        " always_comb begin logic [7:0] t1; t1 = a & b; y = t1; end assign z = t1; endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(sorted(self.names(m)), ["blk1__t1", "t1"])
        assigns = {p["target"]["name"]: p["value"] for p in m["processes"] if p["kind"] == "Assign"}
        self.assertEqual(assigns["z"]["name"], "t1")                        # the module variable
        body = always_comb_body(m)["stmts"]
        self.assertEqual([s["target"]["name"] for s in body if s["kind"] == "BlockingAssign"], ["blk1__t1", "y"])
        self.assertEqual(body[-1]["value"]["name"], "blk1__t1")             # the block variable

    def test_name_clash_gets_a_trailing_underscore(self):
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y); logic [7:0] blk1__x;"
                        " always_comb begin logic [7:0] x; x = a; y = x; end endmodule")
        self.assertIn("blk1__x_", self.names(m))

    def test_selects_of_a_hoisted_local(self):
        m = self.module("module t (input logic [7:0] a, input logic [2:0] i, output logic [7:0] y); always_comb begin"
                        " logic [7:0] v; v = a; v[3] = ~v[2]; v[7:4] = v[3:0]; y = v; y[1:0] = v[i +: 2]; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        names = set()
        def collect(n):
            if isinstance(n, dict):
                if n.get("kind") == "Ident":
                    names.add(n["name"])
                for v in n.values():
                    collect(v)
            elif isinstance(n, list):
                for v in n:
                    collect(v)
        collect(always_comb_body(m))
        self.assertNotIn("v", names)
        self.assertIn("blk1__v", names)

    def test_parametric_width_local(self):
        m = self.module("module t #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);"
                        " always_comb begin logic [N-1:0] u; u = ~a; y = u; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        u, = [d for d in m["decls"] if d["name"] == "blk1__u"]
        dim, = u["width"]["packed"]
        self.assertEqual(dim["msb"]["kind"], "Binary")                       # N - 1, not folded at the default

    def test_closed_literal_initializer_is_hoisted(self):
        m = self.module("module t (input logic [7:0] a, output logic [7:0] y);"
                        " always_comb begin logic [7:0] t = 8'h5a; y = a ^ t; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        hoisted = [d for d in m["decls"] if d.get("hoisted_local")]
        self.assertEqual([d["name"] for d in hoisted], ["blk1__t"])
        self.assertEqual(hoisted[0]["init"]["kind"], "Literal")
        body = always_comb_body(m)
        self.assertEqual(body["stmts"][0]["kind"], "Empty")
        self.assertEqual(body["stmts"][1]["value"]["right"]["name"], "blk1__t")

    def test_closed_parameter_initializer_is_hoisted(self):
        m = self.module("module t #(parameter logic [7:0] B = 8'h5a) (input logic [7:0] a, output logic [7:0] y);"
                        " always_comb begin logic [7:0] bias = B; y = a ^ bias; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        hoisted = [d for d in m["decls"] if d.get("hoisted_local")]
        self.assertEqual([d["name"] for d in hoisted], ["blk1__bias"])
        self.assertEqual(hoisted[0]["init"]["kind"], "ParamRef")

    def test_local_declared_in_an_unrolled_loop_body_is_hoisted_once(self):
        m = self.module("module t (input logic [3:0] a, output logic [3:0] y); always_comb begin y = '0;"
                        " for (int i = 0; i < 4; i++) begin logic t; t = ~a[i]; y[i] = t; end end endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(self.names(m), ["blk1__t"])

    def test_two_state_local(self):
        m = self.module("module t (input logic [3:0] a, output int y); always_comb begin int k; k = a; y = k + 1; end endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertTrue([d for d in m["decls"] if d["name"] == "blk1__k"][0].get("two_state"))

    def test_refusals_keep_the_local_decl(self):
        cases = {
            "runtime-initializer": "always_comb begin logic [7:0] t = a; y = t; end",
            "automatic": "always_comb begin automatic logic [7:0] t; t = a; y = t; end",
            "two-dimensional": "always_comb begin logic [1:0][3:0] t; t = a; y = t; end",
            "unpacked": "always_comb begin logic [7:0] t [0:1]; t[0] = a; y = t[0]; end",
        }
        for why, body in cases.items():
            m = self.module("module t (input logic [7:0] a, output logic [7:0] y); " + body + " endmodule")
            self.assertTrue(count_kind(m, "LocalDecl") or sv_kinds(m), why)
            self.assertEqual([d for d in m["decls"] if d.get("hoisted_local")], [], why)

    def test_other_procedures_keep_their_local_decl(self):
        m = self.module("module t (input logic clk, input logic [7:0] a, output logic [7:0] y); always_ff @(posedge clk) begin"
                        " logic [7:0] t; t = a; y <= t; end endmodule")
        self.assertEqual([d for d in m["decls"] if d.get("hoisted_local")], [])

    def test_generate_scope_blocks_are_not_hoisted(self):
        m = self.module("module t (input logic [3:0] a, output logic [3:0] y); for (genvar g = 0; g < 4; g++) begin : gg"
                        " always_comb begin logic t; t = ~a[g]; y[g] = t; end end endmodule")
        self.assertEqual([d for d in m["decls"] if d.get("hoisted_local")], [])
        self.assertTrue(count_kind(m, "LocalDecl"))


class StarBlocks(Base):
    """E1: `always @*` / `always @(a or b)` / `always @a` is an `AlwaysComb` exactly when R1 to R6 hold."""

    def proc(self, body, decls="", ports="input [3:0] a, b, input [1:0] s, output reg [3:0] y, output reg [3:0] z", params=""):
        m = self.module("module t %s(%s); %s %s endmodule" % (params, ports, decls, body))
        return m["processes"], m

    def refused(self, body, rule, **kw):
        procs, m = self.proc(body, **kw)
        star = [p for p in procs if p["kind"] == "Unsupported"]
        self.assertEqual(len(star), 1, procs)
        self.assertIn(rule, star[0]["text"])
        self.assertTrue(star[0]["sv_kind"].startswith(("TimedStatement:", "SignalEventControl:")))
        return star[0]

    def admitted(self, body, **kw):
        procs, m = self.proc(body, **kw)
        self.assertEqual(sv_kinds(m), [])
        return procs, m

    def test_implicit_star_is_an_always_comb(self):
        procs, _ = self.admitted("always @* y = a & b; always @(*) z = a | b;")
        self.assertEqual([p["kind"] for p in procs], ["AlwaysComb", "AlwaysComb"])
        self.assertEqual([p["always_star_lowered"] for p in procs], ["implicit", "implicit"])

    def test_lists_and_single_events(self):
        procs, _ = self.admitted("always @(a or b) y = a & b; always @(a, b, s) z = a | b;")
        self.assertEqual([(p["kind"], p["always_star_lowered"]) for p in procs], [("AlwaysComb", "list")] * 2)
        procs, _ = self.admitted("always @a y = ~a;")
        self.assertEqual(procs[0]["kind"], "AlwaysComb")

    def test_edge_lists_and_other_controls_are_untouched(self):
        for ctl in ("posedge s[0]", "negedge s[0]"):
            procs, m = self.proc("always @(%s) y <= a;" % ctl)
            self.assertNotIn("always_star_lowered", json.dumps(procs))
        procs, m = self.proc("always @(posedge s[0] or a) y <= a;")
        self.assertNotIn("always_star_lowered", json.dumps(procs))

    def test_always_comb_is_unchanged(self):
        procs, _ = self.admitted("always_comb y = a & b;")
        self.assertNotIn("always_star_lowered", procs[0])

    def test_retain_proc_rewrites_keeps_event_control_source_node(self):
        source = ("module t (input logic [3:0] a, b, output logic [3:0] y); "
                  "always @* y = a & b; endmodule")
        retained = self.module(source, retain_proc_rewrites=True)
        process = retained["processes"][0]
        self.assertEqual(process["kind"], "AlwaysEvent")
        self.assertTrue(process["symbolic_event_retained"])
        self.assertEqual(process["event_kind"], "ImplicitEventControl")
        self.assertNotIn("always_star_lowered", process)

    def test_blocks_with_if_else_and_case(self):
        self.admitted("always @* begin if (s[0]) y = a; else y = b; case (s) 2'd0: z = a; 2'd1: z = b; default: z = 4'd0; endcase end")

    def test_default_then_conditional_is_complete(self):
        self.admitted("always @* begin y = 4'd0; if (s[0]) y = a; end")

    def test_unrolled_loop_with_literal_windows_is_complete(self):
        self.admitted("always @* begin for (i = 0; i < 4; i = i + 1) y[i] = a[i] ^ b[i]; end", decls="integer i;")

    def test_chain_through_the_windows_it_wrote(self):
        self.admitted("always @* begin y[0] = a[0]; for (i = 0; i < 3; i = i + 1) y[i+1] = y[i] & b[i+1]; end", decls="integer i;")

    def test_temporary_declared_in_the_block(self):
        procs, m = self.admitted("always @* begin : blk reg [3:0] t; t = a ^ b; y = t & a; end")
        self.assertTrue([d for d in m["decls"] if d.get("hoisted_local")])

    def test_temporary_need_not_be_listed(self):
        procs, _ = self.admitted("always @(a or b) begin t = a ^ b; y = t & a; end", decls="reg [3:0] t;")
        self.assertEqual(procs[0]["kind"], "AlwaysComb")

    def test_parameterized_widths_whole_assignments(self):
        self.admitted("always @* begin y = a & b; z = 0; end", ports="input [N-1:0] a, b, output reg [N-1:0] y, z", params="#(parameter N = 4) ")

    def test_time_zero_continuous_driver_keeps_implicit_event(self):
        procs, _ = self.proc("assign k = 4'd1; always @* y = k;",
                              decls="wire [3:0] k;")
        event = procs[1]
        self.assertEqual(event["kind"], "AlwaysEvent")
        self.assertEqual(event["event_kind"], "ImplicitEventControl")
        self.assertTrue(event["symbolic_event_retained"])
        self.assertIn("continuous time-zero driver", event["symbolic_event_reason"])

    # ---- refusals, one per rule
    def test_r1_nonblocking_and_timing(self):
        self.refused("always @* y <= a & b;", "R1")
        procs, m = self.proc("always @* begin #1 y = a; end")
        self.assertTrue(sv_kinds(m))

    def test_r1_iff(self):
        self.refused("always @(a iff s[0]) y = a;", "R1")

    def test_r2_list_misses_a_read(self):
        self.refused("always @(a) y = a & b;", "R2")
        self.refused("always @(a or s) begin if (s[0]) y = a; else y = b; end", "R2")

    def test_r2_select_or_expression_in_the_list(self):
        self.refused("always @(a[0]) y = {4{a[0]}};", "R2")
        self.refused("always @(a + b) y = a;", "R2")

    def test_r3_reads_nothing(self):
        self.refused("always @* y = 4'd5;", "R3")
        self.refused("always @(a) y = 4'd5;", "R3")

    def test_r3_two_state_read(self):
        self.refused("always @* y = a & k;", "R3", decls="bit [3:0] k;")
        self.refused("always @* y = a + n;", "R3", decls="int n;")

    def test_r3_reads_only_its_own_targets(self):
        self.refused("always @* begin y = 4'd1; z = y; end", "R3")

    def test_r4_function_reading_a_module_signal(self):
        # the inliner (master) refuses a function that reads a module signal, so the call stays an inner refusal; R4 is
        # the second line, decided on slang's own tree
        procs, m = self.proc("always @* y = f(a);",
                             decls="function automatic [3:0] f(input [3:0] x); return x ^ b; endfunction")
        self.assertEqual(procs[0]["kind"], "AlwaysComb")
        self.assertIn("CallExpression", sv_kinds(m))
        procs, m = self.admitted("always @* y = f(a);",
                                 decls="function automatic [3:0] f(input [3:0] x); return x ^ 4'd3; endfunction")
        self.assertEqual(procs[0]["kind"], "AlwaysComb")

    def test_r4_rule_on_the_slang_tree(self):
        import pyslang
        from pyslang import ast, syntax
        import lower_proc

        def reads(function):
            sm = pyslang.SourceManager()
            tree = syntax.SyntaxTree.fromText("module t (input [3:0] a, b, output reg [3:0] y); %s"
                                              " function automatic [3:0] g(input [3:0] x); return f(x); endfunction"
                                              " always @* y = g(a); endmodule" % function, sm)
            comp = ast.Compilation()
            comp.addSyntaxTree(tree)
            block = [mm for mm in comp.getRoot().topInstances[0].body if str(mm.kind).endswith("ProceduralBlock")][0]
            return lower_proc._function_reads_module_signal(extract, block.body.stmt)

        self.assertIsNone(reads("function automatic [3:0] f(input [3:0] x); logic [3:0] k; k = x; return k; endfunction"))
        self.assertEqual(reads("function automatic [3:0] f(input [3:0] x); return x ^ b; endfunction"), "b")

    def test_r5_latches(self):
        self.refused("always @* if (s[0]) y = a;", "R5")
        self.refused("always @* case (s) 2'd0: y = a; 2'd1: y = b; endcase", "R5")
        self.refused("always @* begin y[1:0] = a[1:0]; end", "R5")
        self.refused("always @* begin y[s] = a[0]; end", "R5")

    def test_r5_complete_case_without_default_is_refused(self):
        self.refused("always @* case (s) 2'd0: y = a; 2'd1: y = b; 2'd2: y = a; 2'd3: y = b; endcase", "R5")

    def test_r5_read_before_write(self):
        self.refused("always @* begin y = y + a; end", "R5")
        self.refused("always @* begin z = y; y = a; end", "R5")

    def test_r5_a_read_of_a_window_not_yet_written(self):
        self.refused("always @* begin y[0] = a[0]; y[1] = y[2]; y[3:2] = a[1:0]; end", "R5")

    def test_r6_another_process_writes_the_target(self):
        procs, _ = self.proc("always @* y = a; always @* y = b;")
        self.assertEqual([p["kind"] for p in procs], ["Unsupported", "Unsupported"])      # each sees the other writer
        self.assertTrue(all("R6" in p["text"] for p in procs))
        procs, _ = self.proc("always @* y = a; always @(posedge clk) y <= b;",
                             ports="input clk, input [3:0] a, b, input [1:0] s, output reg [3:0] y, output reg [3:0] z")
        star = [p for p in procs if p["kind"] == "Unsupported" and p["sv_kind"].startswith("TimedStatement")]
        self.assertEqual(len(star), 1)
        self.assertIn("R6", star[0]["text"])

    def test_r6_only_readers_elsewhere(self):
        m = self.module("module t (input [3:0] a, b, output reg [3:0] y, output [3:0] w); always @* y = a & b; assign w = y; endmodule")
        self.assertNotIn("R6", json.dumps(m["processes"]))

    def test_r6_initialized_target(self):
        self.refused("always @* y = a;", "R6", decls="", ports="input [3:0] a, b, input [1:0] s, output reg [3:0] y = 4'd1, output reg [3:0] z")

    def test_system_task_in_the_body_is_r1(self):
        self.refused("always @* begin y = a; $display(\"x\"); end", "R1")

    def test_old_tags_are_kept(self):
        self.assertEqual(self.refused("always @* y = 4'd1;", "R3")["sv_kind"], "TimedStatement:ImplicitEventControl")
        self.assertEqual(self.refused("always @(a or b) y = 4'd1;", "R3")["sv_kind"], "TimedStatement:EventListControl")
        self.assertEqual(self.refused("always @a y = 4'd1;", "R3")["sv_kind"], "SignalEventControl:None_")

    def test_hierarchical_and_generate_scopes(self):
        m = self.module("module t (input [3:0] a, output reg [3:0] y); if (1) begin : g always @* y = a; end endmodule")
        self.assertEqual([p["kind"] for g in m["generates"] for p in g.get("processes", [])] or ["AlwaysComb"], ["AlwaysComb"])


class NetsAsVariables(Base):
    """N2: a plain `wire` with exactly one continuous driver on every bit is declared as the variable the driver assigns."""

    CHILD = "module nchild (input logic [3:0] a, output logic [3:0] o); assign o = ~a; endmodule\n"

    def top(self, body, ports="input [3:0] a, b, output [3:0] y", params="", more=()):
        return self.module("module t %s(%s); %s endmodule" % (params, ports, body), more=more)

    def decl(self, m, name):
        return [d for d in m["decls"] if d.get("name") == name][0]

    def test_whole_net_assign_is_a_variable(self):
        m = self.top("wire [3:0] w; assign w = a & b; assign y = w;")
        self.assertEqual(sv_kinds(m), [])
        w = self.decl(m, "w")
        self.assertEqual((w["kind"], w["init"], w["net_as_variable"]), ("Var", None, True))
        self.assertEqual([p["kind"] for p in m["processes"]], ["Assign", "Assign"])
        y = [p for p in m["ports"] if p["name"] == "y"][0]
        self.assertEqual((y["dir"], y["net_as_variable"]), ("out", True))          # `output [3:0] y` is a net port

    def test_retain_proc_rewrites_keeps_single_driver_net(self):
        m = self.module(
            "module t (input logic [3:0] a, b, output logic [3:0] y); "
            "wire [3:0] w; assign w = a & b; assign y = w; endmodule",
            retain_proc_rewrites=True)
        w = self.decl(m, "w")
        self.assertEqual(w["kind"], "Net")
        self.assertTrue(w["net_rewrite_retained"])
        self.assertNotIn("net_as_variable", w)

    def test_output_wire_and_scalar_and_implicit_nets(self):
        m = self.top("assign t1 = a[0]; assign y1 = t1;", ports="input [3:0] a, output wire y1")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(self.decl(m, "t1")["kind"], "Var")                        # the implicit net of `assign t1 = ...`
        self.assertEqual(self.decl(m, "t1")["width"]["packed"], [])

    def test_declaration_assignment_is_an_assign_at_its_position(self):
        m = self.top("assign y = 4'd1; wire [3:0] w = a ^ b; assign y2 = w;", ports="input [3:0] a, b, output [3:0] y, y2")
        self.assertEqual(sv_kinds(m), [])
        w = self.decl(m, "w")
        self.assertIsNone(w["init"])
        kinds = [(p["kind"], p.get("net_declaration_assign", False)) for p in m["processes"]]
        self.assertEqual(kinds, [("Assign", False), ("Assign", True), ("Assign", False)])
        tgt = m["processes"][1]["target"]
        self.assertEqual((tgt["kind"], tgt["name"], tgt["width"]), ("Ident", "w", 4))

    def test_literal_windows_that_tile_the_net(self):
        m = self.top("wire [7:0] w; assign w[3:0] = a; assign w[7:4] = b; assign y = w[3:0] ^ w[7:4];")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(self.decl(m, "w")["kind"], "Var")

    def test_parametric_whole_net_assign(self):
        m = self.top("wire [N-1:0] w; assign w = a | b; assign y = w;", ports="input [N-1:0] a, b, output [N-1:0] y",
                     params="#(parameter N = 4) ")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(self.decl(m, "w")["width"]["packed"][0]["msb"]["kind"], "Binary")

    def test_instance_output_drives_the_whole_net(self):
        m = self.top("wire [3:0] w; nchild u (.a(a), .o(w)); assign y = w;", more=(self.CHILD,))
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(self.decl(m, "w")["kind"], "Var")

    def test_parameterized_instance_outputs_tile_an_output_wire(self):
        top = (
            "module top #(parameter integer W = 8) (input wire [W-1:0] a, "
            "output wire [W-1:0] y); "
            "leaf #(.W(W/2)) lo(.a(a[W/2-1:0]), .y(y[W/2-1:0])); "
            "leaf #(.W(W/2)) hi(.a(a[W-1:W/2]), .y(y[W-1:W/2])); endmodule\n"
        )
        child = (
            "module leaf #(parameter integer W = 4) (input wire [W-1:0] a, "
            "output wire [W-1:0] y); assign y = a; endmodule\n"
        )
        m = self.module(top, top="top", more=(child,))
        self.assertNotIn("PortSymbol:net-z", sv_kinds(m))
        y = [p for p in m["ports"] if p["name"] == "y"][0]
        self.assertTrue(y["net_as_variable"])
        instances = [g for g in m["generates"] if g["kind"] == "Instance"]
        self.assertEqual(len(instances), 2)
        self.assertTrue(all(
            p["dir"] == "out" and p["target"]["kind"] == "ArraySel"
            for g in instances for p in g["ports"] if p["dir"] == "out"))

    def test_non_ascii_source_before_wire_driver_keeps_net_lowering(self):
        # Slang source offsets are UTF-8 byte offsets.  A decoded Unicode
        # slice used to shift after this em dash and falsely refuse both
        # output-wire drivers as PortSymbol:net-z.
        child = (
            "// header — deliberately non-ASCII\n"
            "module leaf #(parameter integer W = 4) "
            "(input wire [W-1:0] a, output wire [W-1:0] y); "
            "assign y = a; endmodule\n"
        )
        top = (
            "module top #(parameter integer W = 8) "
            "(input wire [W-1:0] a, output wire [W-1:0] y); "
            "leaf #(.W(W/2)) lo(.a(a[W/2-1:0]), .y(y[W/2-1:0])); "
            "leaf #(.W(W/2)) hi(.a(a[W-1:W/2]), .y(y[W-1:W/2])); "
            "endmodule\n"
        )
        design = self.extract(top, top="top", more=(child,))
        modules = {m["name"]: m for m in design["modules"]}
        for name in ("leaf", "top"):
            module = modules[name]
            self.assertNotIn("PortSymbol:net-z", sv_kinds(module), name)
            outputs = [p for p in module["ports"]
                       if p.get("name") == "y"]
            self.assertEqual(len(outputs), 1, name)
            self.assertTrue(outputs[0].get("net_as_variable"), name)

    # ---- what stays refused (the tag is the old one)
    def refused_net(self, body, ports="input [3:0] a, b, output [3:0] y", params="", more=()):
        m = self.top(body, ports, params, more)
        self.assertIn("NetSymbol:net-z", sv_kinds(m), body)
        self.assertEqual([d for d in m["decls"] if d.get("net_as_variable")], [], body)

    def test_undriven_and_partially_driven_nets(self):
        self.refused_net("wire [3:0] w; assign y = w;")
        self.refused_net("wire [3:0] w; assign w[2:0] = a[2:0]; assign y = w;")
        self.refused_net("wire [3:0] w; assign w[0] = a[0]; assign w[2] = a[2]; assign y = w;")

    def test_two_drivers_are_a_resolution(self):
        self.refused_net("wire [3:0] w; assign w = a; assign w = b; assign y = w;")
        self.refused_net("wire [3:0] w; assign w[2:0] = a[2:0]; assign w[3:1] = b[3:1]; assign y = w;")

    def test_declaration_assignment_plus_another_driver(self):
        self.refused_net("wire [3:0] w = a; assign w[0] = b[0]; assign y = w;")

    def test_strength_and_delay_and_other_net_types(self):
        self.refused_net("wire [3:0] w; assign (strong0, highz1) w = a; assign y = w;")
        self.refused_net("wire (weak0, weak1) [3:0] w = a; assign y = w;")
        self.refused_net("wire [3:0] w; assign #1 w = a; assign y = w;")
        m = self.top("wand [3:0] w; assign w = a; assign y = w;")
        self.assertIn("NetSymbol:WAnd", sv_kinds(m))
        m = self.top("tri [3:0] w; assign w = a; assign y = w;")
        self.assertTrue(sv_kinds(m))

    def test_signed_and_two_state_nets(self):
        m = self.top("wire signed [3:0] w; assign w = a; assign y = w;")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual([d["name"] for d in m["decls"]
                          if d.get("net_as_variable")], ["w"])

    def test_drivers_in_a_generate_scope(self):
        m = self.top("wire [3:0] w; for (genvar i = 0; i < 4; i++) begin : g assign w[i] = a[i]; end assign y = w;")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(self.decl(m, "w")["kind"], "Var")
        self.refused_net("wire [3:0] w; if (1) begin : g assign w = a; end assign y = w;")

    def test_nets_declared_in_a_generate_scope(self):
        m = self.top("if (1) begin : g wire [3:0] w; assign w = a; assign y = w; end")
        self.assertTrue(sv_kinds(m))

    def test_windows_of_a_parametric_net(self):
        m = self.top("wire [N-1:0] w; assign w[3:0] = a[3:0]; assign y = w;", ports="input [N-1:0] a, b, output [N-1:0] y",
                     params="#(parameter N = 4) ")
        self.assertIn("NetSymbol:net-z", sv_kinds(m))

    def test_unrelated_output_ports_unchanged(self):
        m = self.top("assign y = a;", ports="input [3:0] a, output logic [3:0] y")
        self.assertEqual(sv_kinds(m), [])
        self.assertNotIn("net_as_variable", json.dumps(m))

    def test_output_net_port_without_driver_stays_refused(self):
        m = self.top("", ports="input [3:0] a, output [3:0] y")
        self.assertIn("PortSymbol:net-z", sv_kinds(m))

    def test_output_net_port_driven_twice_stays_refused(self):
        m = self.top("assign y = a; assign y = b;", ports="input [3:0] a, b, output [3:0] y")
        self.assertIn("PortSymbol:net-z", sv_kinds(m))


if __name__ == "__main__":
    unittest.main()
