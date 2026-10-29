"""Round 6, lane A (sv-0.2 symbolic mode, 2026-10-29): two refusals the Xcelium
audit (docs/sv-xcelium-audit.md) asks for, at the extractor.

H1 -- a NET formal fed by a bare, narrower NET actual. IEEE 1800-2023 23.3.3 /
10.7 zero-extend the actual (Icarus 12.0, Verilator 5.042, Yosys 0.53, slang);
Xcelium 24.03-s004 binds the nets bit for bit and leaves the formal's high bits
undriven (z). The extractor does not know the widths at every point, so it only
MARKS the shape on the connection (`"net": true` on a CONNECTED input port
connection); `Hier2.lean` `connProcs` is loud (`PortConn:net-width`) where the
actual is narrower than the port. Marked: a net formal (no `var`, 4-state)
and a bare reference to a net (a `wire`, an `input`/`inout` port without
`var`, an `output wire` or implicit-type `output`) whose declared widths are
not both fixed with the formal not wider. Not marked: variable actuals
(`logic`, and an `output logic` / `output reg` / `output var logic` port: an
output with an explicit data type is a VARIABLE, 23.2.2.3), part-/bit-selects,
constants and expressions, `var` formals, 2-state formals, fixed widths with
the formal at most as wide as the actual.

T1 -- a bit-select INDEX wider than 32 bits. IEEE 1800-2023 11.5.1 takes the
index whole; Xcelium (BIGWBS), Icarus and Verilator truncate it to 32 bits.
`ElementSelectExpression:wide-index` for a run-time index wider than 32 bits
and for a constant index of 2^32 or more; a parametric index that is 32 bits at
the default point is left to Lean's per-point `Select:wide-index` guard.
"""
import json
import tempfile
import unittest
from pathlib import Path

import extract


def extract_sym(source, top):
    with tempfile.TemporaryDirectory() as directory:
        src = Path(directory) / "fixture.sv"
        src.write_text(source)
        out = Path(directory) / "fixture.sv.json"
        extract.process_symbolic(top, [str(src)], [], str(out))
        return json.loads(out.read_text())


def walk(node, found=None):
    found = [] if found is None else found
    if isinstance(node, dict):
        found.append(node)
        for value in node.values():
            walk(value, found)
    elif isinstance(node, list):
        for value in node:
            walk(value, found)
    return found


def sv_kinds(env):
    return [n.get("sv_kind") for n in walk(env) if n.get("kind") == "Unsupported"]


def input_conns(env):
    """{instance name: {port: PortConn node}} of the connected inputs."""
    out = {}
    for n in walk(env):
        if n.get("kind") == "Instance":
            out[n["name"]] = {p["port"]: p for p in n["ports"]
                              if p.get("kind") == "PortConn" and p.get("dir") == "in"}
    return out


CHILD = """
module child #(parameter int W = 6) (input logic [W-1:0] i, output logic [W-1:0] p);
  assign p = i;
endmodule
module child_fixed (input logic [5:0] i, output logic [5:0] p);
  assign p = i;
endmodule
module child_var (input var logic [5:0] i, output logic [5:0] p);
  assign p = i;
endmodule
module child_eq (input logic [1:0] i, output logic [1:0] p);
  assign p = i;
endmodule
"""


class NetBoundActual(unittest.TestCase):
    def conn(self, body, inst="u", port="i", decls=""):
        src = CHILD + """
module top (input logic [1:0] s, input wire [5:0] w6, output logic [5:0] p);
  %s
  %s
endmodule
""" % (decls, body)
        return input_conns(extract_sym(src, "top"))[inst][port]

    def test_bare_input_port_into_parametric_net_formal_is_marked(self):
        self.assertIs(self.conn("child #(.W(6)) u (.i(s), .p(p));").get("net"), True)

    def test_bare_input_port_into_fixed_wider_net_formal_is_marked(self):
        self.assertIs(self.conn("child_fixed u (.i(s), .p(p));").get("net"), True)

    def test_a_wire_actual_is_a_net_too(self):
        c = self.conn("child_fixed u (.i(w), .p(p));", decls="wire [1:0] w; assign w = s;")
        self.assertIs(c.get("net"), True)

    def test_variable_actual_is_not_marked(self):
        c = self.conn("child_fixed u (.i(v), .p(p));", decls="logic [1:0] v; assign v = s;")
        self.assertNotIn("net", c)

    def test_expression_actuals_are_not_marked(self):
        for actual in ("{s}", "s ^ 2'b10", "6'd3"):
            with self.subTest(actual=actual):
                self.assertNotIn("net", self.conn("child_fixed u (.i(%s), .p(p));" % actual))

    def test_selects_are_not_marked(self):
        # Xcelium z-fills a full-range part select and a constant bit select
        # too (audit H1 matrix); not marked yet -- a recorded gap.
        for actual in ("s[1:0]", "s[1]"):
            with self.subTest(actual=actual):
                self.assertNotIn("net", self.conn("child_fixed u (.i(%s), .p(p));" % actual))

    def test_var_formal_is_not_marked(self):
        self.assertNotIn("net", self.conn("child_var u (.i(s), .p(p));"))

    def test_fixed_equal_or_wider_actual_is_not_marked(self):
        # both widths fixed, formal not wider than the actual: unchanged envelope
        self.assertNotIn("net", self.conn("child_fixed u (.i(w6), .p(p));"))
        self.assertNotIn("net", self.conn("child_eq u (.i(s), .p());"))

    def test_marked_connection_keeps_its_expression(self):
        # slang binds the actual under its implicit width conversion; the
        # envelope keeps it as a `Resize` marker over the bare reference
        c = self.conn("child_fixed u (.i(s), .p(p));")
        idents = [n["name"] for n in walk(c["expr"]) if n.get("kind") == "Ident"]
        self.assertEqual(idents, ["s"])
        self.assertIn(c["expr"]["kind"], ("Resize", "Ident"))


class NetBoundOutputActual(unittest.TestCase):
    """Round 6 repair: an OUTPUT port of the instantiating module is a NET
    only without an explicit data type (`output wire`, an implicit-type
    `output`) -- IEEE 1800-2023 23.2.2.3. `output logic` / `output reg` /
    `output var logic` are VARIABLES, which every tool zero-extends; slang
    reports them with the same `VariablePortHeader` and empty `var` as an
    `input logic`, so only the direction token tells them apart."""

    def conn(self, port_decl, body_decl="", ansi=True):
        if ansi:
            src = CHILD + """
module top (input logic [1:0] s, %s, output logic [5:0] p);
  %s
  child_fixed u (.i(o), .p(p));
endmodule
""" % (port_decl, body_decl)
        else:
            src = CHILD + """
module top (s, o, p);
  input [1:0] s;
  %s
  output [5:0] p;
  %s
  child_fixed u (.i(o), .p(p));
endmodule
""" % (port_decl, body_decl)
        return input_conns(extract_sym(src, "top"))["u"]["i"]

    def test_output_logic_is_a_variable(self):
        self.assertNotIn("net", self.conn("output logic [1:0] o", "assign o = s;"))

    def test_output_reg_is_a_variable(self):
        self.assertNotIn("net", self.conn("output reg [1:0] o", "always_comb o = s;"))

    def test_output_var_logic_is_a_variable(self):
        self.assertNotIn("net", self.conn("output var logic [1:0] o", "assign o = s;"))

    def test_output_wire_is_a_net(self):
        self.assertIs(self.conn("output wire [1:0] o", "assign o = s;").get("net"), True)

    def test_implicit_type_output_is_a_net(self):
        self.assertIs(self.conn("output [1:0] o", "assign o = s;").get("net"), True)

    def test_non_ansi_output_reg_is_a_variable(self):
        c = self.conn("output reg [1:0] o;", "always @* o = s;", ansi=False)
        self.assertNotIn("net", c)

    def test_non_ansi_output_wire_is_a_net(self):
        c = self.conn("output [1:0] o;", "assign o = s;", ansi=False)
        self.assertIs(c.get("net"), True)

    def test_inout_wire_is_a_net(self):
        src = CHILD + """
module top (input logic [1:0] s, inout wire [1:0] o, output logic [5:0] p);
  assign o = s;
  child_fixed u (.i(o), .p(p));
endmodule
"""
        self.assertIs(input_conns(extract_sym(src, "top"))["u"]["i"].get("net"), True)

    def test_comments_before_the_direction_keyword_do_not_hide_it(self):
        # `str(token)` of the direction keyword carries the comments before it
        # ("\n  // clk\n  input"); the decision reads the token's own text.
        src = CHILD + """
module top (
  // the narrow net input
  input /* inline */ logic [1:0] s,
  /* a variable output */ output
  logic [1:0] o,
  output logic [5:0] p);
  assign o = s;
  child_fixed u (.i(s), .p(p));
  child_fixed v (.i(o), .p());
endmodule
"""
        conns = input_conns(extract_sym(src, "top"))
        self.assertIs(conns["u"]["i"].get("net"), True)
        self.assertNotIn("net", conns["v"]["i"])

    def test_input_var_logic_is_a_variable(self):
        src = CHILD + """
module top (input var logic [1:0] o, output logic [5:0] p);
  child_fixed u (.i(o), .p(p));
endmodule
"""
        self.assertNotIn("net", input_conns(extract_sym(src, "top"))["u"]["i"])


class WideIndex(unittest.TestCase):
    def kinds(self, decls, body, params=""):
        src = """
module top %s (%s);
%s
endmodule
""" % (params, decls, body)
        return sv_kinds(extract_sym(src, "top"))

    def test_runtime_index_wider_than_32_bits_is_refused(self):
        k = self.kinds("input logic [32:0] a, input logic [7:0] v, output logic o",
                       "assign o = v[a];")
        self.assertEqual(k, ["ElementSelectExpression:wide-index"])

    def test_expression_index_wider_than_32_bits_is_refused(self):
        k = self.kinds("input logic [41:0] a, input logic [7:0] v, output logic o",
                       "assign o = v[a - 3];")
        self.assertEqual(k, ["ElementSelectExpression:wide-index"])

    def test_wide_index_target_at_the_default_point_is_the_assignment_tag(self):
        # A refused select leaves no usable target: the Unsupported node that
        # reaches the envelope is the assignment's, not the read tag
        # (fixture sem2/wide_index_wr, row wide_index_wr).
        k = self.kinds("input logic [39:0] a, input logic b, output logic [7:0] w",
                       "always_comb begin w = '0; w[a] = b; end")
        self.assertEqual(k, ["AssignmentExpression:target"])

    def test_wide_index_as_a_target_is_refused(self):
        # a refused select leaves no usable target: the assignment is loud
        # (`AssignmentExpression:target`), as a 4-bit index is not
        k = self.kinds("input logic [39:0] a, input logic b, output logic [7:0] w",
                       "always_comb begin w = '0; w[a] = b; end")
        self.assertTrue(k and all(x in ("ElementSelectExpression:wide-index",
                                        "AssignmentExpression:target") for x in k), k)
        self.assertEqual(self.kinds("input logic [3:0] a, input logic b, output logic [7:0] w",
                                    "always_comb begin w = '0; w[a] = b; end"), [])

    def test_index_of_at_most_32_bits_is_admitted(self):
        for decls, body in (
                ("input logic [31:0] a, input logic [7:0] v, output logic o", "assign o = v[a];"),
                ("input logic [3:0] a, input logic [7:0] v, output logic o", "assign o = v[a];"),
                ("input logic [9:0] a, input logic [7:0] v, output logic o", "assign o = v[a - 3];")):
            with self.subTest(decls=decls):
                self.assertEqual(self.kinds(decls, body), [])

    def test_constant_index_of_2_32_or_more_is_refused(self):
        k = self.kinds("input logic [7:0] v, output logic o", "assign o = v[40'h1_0000_0002];")
        self.assertEqual(k, ["ElementSelectExpression:wide-index"])

    def test_wide_constant_that_fits_is_admitted(self):
        k = self.kinds("input logic [7:0] v, output logic o", "assign o = v[40'd2];")
        self.assertEqual(k, [])

    def test_parametric_width_is_left_to_the_lean_guard(self):
        # 10 bits at the default point: the envelope carries the dynamic select,
        # Lean's `Select:wide-index` refuses N = 40.
        k = self.kinds("input logic [N+1:0] a, input logic [7:0] v, output logic o",
                       "assign o = v[a];", "#(parameter int N = 8)")
        self.assertEqual(k, [])


if __name__ == "__main__":
    unittest.main()
