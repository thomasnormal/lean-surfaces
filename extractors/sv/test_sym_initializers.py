"""Declaration initializers in symbolic mode (sv-0.2, 2026-10-28, round 3 CX
repair of the round-2 WP2 verifier's two majors).

(A) An OUTPUT variable port's initializer (`output logic [1:0] y = 2'b10`)
sits on the PORT symbol, not on its internal variable; `convert_port_sym`
dropped it silently, so `name.sem` read x where every simulator reads the
initial value (verifier probe `vg_initq`). It is now emitted as the Port's
`init`, exactly as a `Var`'s; an output NET port with one (illegal, slang
`DisallowedPortDefault`) is loud; ports without one are unchanged (no key).

(B) A continuous driver of any bit of a declaration with an initializer is
refused: for a variable the initializer is a procedural write (§10.5) the
one-driver rule never sees (slang -Wmixed-var-assigns, Icarus "Unable to
assign to unresolved wires", Yosys a conflicting constant driver; verifier
probes `vg_init`, `vg_initp`, `vh_init`), for a net it is a second
continuous driver the model does not resolve. Both an `assign` and an
instance output connection are continuous drivers.

Round 4 (Lane A, 2026-10-28):

(C) Every output-port initializer form slang accepts is emitted: ANSI
(`output logic|reg|var logic|var`, shared declarations, packed structs) on
the port symbol; non-ANSI with the variable declared separately
(`logic`/`reg`/`var logic`) on the internal variable; non-ANSI single
declarations (`output reg|logic|var logic [1:0] y = ...;`) on the port
symbol. A port with an EXPLICIT port expression (`.q(y)`, `y[1:0]`) is
loud: its name is not its internal signal's.

(D) A width- or sign-converted literal initializer (`Resize`/`SignedResize`
of a `Literal`) is lowered exactly: a 0/1 literal to the `Int` of its value
(exact at every parameter point through `instDecl`'s `LVec.ofInt`), an x/z
literal to the `Literal` of the declared width only when that width is
fixed; anything else keeps the conversion (loud).

(E) An `always_comb` / `always_ff` writer of a module-level variable with a
declaration initializer is refused (`ProceduralBlockSymbol:initialized-
variable`): Xcelium 24.03 rejects it (MULAXX) where Icarus 12.0, Yosys 0.53
and slang run it. A plain `always` writer stays admitted.

(F) `_sym_initialized_target_info` fails CLOSED: an unknown target shape or
an exception while inspecting gives `"unknown"`, which the callers refuse.

Round 4 repair (INIT verifier, 2026-10-28):

(G) An UNSIZED unsigned literal whose high-order bit is x/z is extended with
that bit (IEEE 1800-2023 §5.7.1), in a declaration initializer at a fixed
width (`[39:0] y = 'hz1` -> 36 z then 0001; Icarus 12, Xcelium 24.03 and
Yosys 0.53 agree) where the round-4 lowering padded 0; in an expression it
is padded in a one-point module and loud in a family
(`ConversionExpression:unsized-xz`).

(H) A PLAIN literal initializer at a width that is not fixed is a
default-point value: a 0/1 literal becomes its `Int`, a one-bit-repeated
unsized x/z literal `Fill`, anything else is loud
(`Initializer:x-literal-parametric-width`, `Initializer:default-point-
literal`).

(I) A non-ANSI input whose separately declared internal symbol carries an
initializer is loud (`PortSymbol:initialized-input`).
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


def kinds(nodes):
    return [n.get("sv_kind") or n.get("kind") for n in nodes]


class PortInitializer(unittest.TestCase):
    def test_output_variable_port_initializer_is_emitted(self):
        env = extract_sym(
            "module top (input logic clk, input logic a, "
            "output logic [1:0] y = 2'b10); "
            "always_ff @(posedge clk) y[0] <= a; endmodule\n", "top")
        ports = env["design"]["modules"][0]["ports"]
        self.assertEqual([p["name"] for p in ports], ["clk", "a", "y"])
        self.assertNotIn("init", ports[0])
        self.assertNotIn("init", ports[1])
        self.assertEqual(ports[2]["init"]["kind"], "Literal")

    def test_parametric_fill_initializer_stays_symbolic(self):
        env = extract_sym(
            "module top #(parameter int N = 4) (input logic clk, input logic a, "
            "output logic [N-1:0] y = '1); "
            "always_ff @(posedge clk) y[0] <= a; endmodule\n", "top")
        y = env["design"]["modules"][0]["ports"][2]
        self.assertEqual(y["init"]["kind"], "Fill")

    def test_output_net_port_initializer_is_loud(self):
        env = extract_sym(
            "module top (input logic a, output wire [1:0] y = 2'b10); "
            "endmodule\n", "top")
        y = env["design"]["modules"][0]["ports"][1]
        self.assertEqual(y["kind"], "Unsupported")
        self.assertEqual(y["sv_kind"], "PortSymbol:initializer")


class InitializedContinuousTargets(unittest.TestCase):
    def test_assign_to_initialized_variable_bit_is_loud(self):
        env = extract_sym(
            "module top (input logic a, output logic [1:0] y); "
            "logic [1:0] t = 2'b10; assign t[0] = a; assign y = t; endmodule\n",
            "top")
        self.assertEqual(kinds(env["design"]["modules"][0]["processes"]),
                         ["ContinuousAssignSymbol:initialized-variable", "Assign"])

    def test_assign_to_initialized_output_port_is_loud(self):
        env = extract_sym(
            "module top (input logic a, output logic [1:0] y = 2'b10); "
            "assign y[0] = a; endmodule\n", "top")
        self.assertEqual(kinds(env["design"]["modules"][0]["processes"]),
                         ["ContinuousAssignSymbol:initialized-variable"])

    def test_assign_to_initialized_net_is_loud(self):
        env = extract_sym(
            "module top (input logic a, output logic [1:0] y); "
            "wire [1:0] w = 2'b01; assign w[0] = a; assign y = w; endmodule\n",
            "top")
        self.assertEqual(kinds(env["design"]["modules"][0]["processes"]),
                         ["ContinuousAssignSymbol:initialized-net", "Assign"])

    def test_concatenation_target_with_an_initialized_part_is_loud(self):
        env = extract_sym(
            "module top (input logic a, b, output logic [2:0] y); "
            "logic [1:0] t = 2'b10; logic u; assign {u, t[1]} = {a, b}; "
            "assign y = {u, t}; endmodule\n", "top")
        self.assertEqual(kinds(env["design"]["modules"][0]["processes"])[0],
                         "ContinuousAssignSymbol:initialized-variable")

    def test_index_expression_is_read_not_written(self):
        # `t[k]` writes `t`, reads `k`: an initialized INDEX is no driver.
        env = extract_sym(
            "module top (input logic a, output logic [1:0] y); "
            "logic k = 1'b0; logic [1:0] t; assign t[k] = a; "
            "assign t[~k] = 1'b0; assign y = t; endmodule\n", "top")
        self.assertNotIn("ContinuousAssignSymbol:initialized-variable",
                         kinds(env["design"]["modules"][0]["processes"]))

    def test_plain_always_writer_of_initialized_variable_stays_admitted(self):
        # A plain `always` is not exclusive (§9.2.2.1): every tool, Xcelium
        # 24.03 included, runs it (round 4 Lane A, fixtures `pi_*_forms`).
        env = extract_sym(
            "module top (input logic clk, a, output logic [1:0] y); "
            "logic [1:0] t = 2'b10; always @(posedge clk) t[0] <= a; "
            "assign y = t; endmodule\n", "top")
        self.assertEqual(kinds(env["design"]["modules"][0]["processes"]),
                         ["AlwaysPosedge", "Assign"])

    def test_instance_output_into_initialized_variable_is_loud(self):
        env = extract_sym(
            "module ch (input logic a, output logic o); assign o = ~a; endmodule\n"
            "module top (input logic a, output logic [1:0] y); "
            "logic [1:0] t = 2'b10; ch u (.a(a), .o(t[0])); assign y = t; "
            "endmodule\n", "top")
        inst = env["design"]["modules"][0]["generates"][0]
        self.assertEqual(kinds(inst["ports"]),
                         ["PortConn", "PortConnection:initialized-variable"])

    def test_uninitialized_targets_are_unchanged(self):
        env = extract_sym(
            "module ch (input logic a, output logic o); assign o = ~a; endmodule\n"
            "module top (input logic a, output logic [1:0] y); "
            "logic [1:0] t; ch u (.a(a), .o(t[0])); assign t[1] = a; "
            "assign y = t; endmodule\n", "top")
        top = env["design"]["modules"][0]
        self.assertEqual(kinds(top["generates"][0]["ports"]), ["PortConn", "PortConn"])
        self.assertEqual(kinds(top["processes"]), ["Assign", "Assign"])


def ports_of(env, module=0):
    return env["design"]["modules"][module]["ports"]


class PortInitializerForms(unittest.TestCase):
    """(C): every output-port initializer form slang accepts."""

    def assert_inits(self, env, want):
        got = {p["name"]: (p.get("init", {}).get("bits")
                           if p.get("init", {}).get("kind") != "Int"
                           else ("Int", p["init"]["value"]))
               for p in ports_of(env)
               if p.get("kind") == "Port" and p.get("dir") == "out"}
        self.assertEqual(got, want)

    def test_ansi_forms(self):
        env = extract_sym(
            "module top (input logic clk, output logic [1:0] y1 = 2'b10, "
            "output reg [1:0] y2 = 2'b01, output var logic [1:0] y3 = 2'b11, "
            "output var [1:0] y4 = 2'b10, output logic [1:0] y5 = 2'b01, "
            "y6 = 2'b10); endmodule\n", "top")
        # y4's implicit-type dimensions are not recovered (`packed: null`),
        # so its width is not known to be fixed: the literal is its value
        # (round 4 repair (H)), exact at any width.
        self.assert_inits(env, {"y1": "10", "y2": "01", "y3": "11",
                                "y4": ("Int", 2), "y5": "01", "y6": "10"})

    def test_nonansi_forms(self):
        env = extract_sym(
            "module top (z1, z2, z3, z4, z5, z6, z7, z8, z9);\n"
            "output [1:0] z1; logic [1:0] z1 = 2'b10;\n"
            "output [1:0] z2; reg [1:0] z2 = 2'b01;\n"
            "output [1:0] z3; var logic [1:0] z3 = 2'b11;\n"
            "output reg [1:0] z4 = 2'b10;\n"
            "output logic [1:0] z5 = 2'b01;\n"
            "output var logic [1:0] z6 = 2'b11;\n"
            "output reg [1:0] z7 = 2'b10, z8 = 2'b01;\n"
            "output z9; reg z9 = 1'b1;\n"
            "endmodule\n", "top")
        self.assert_inits(env, {"z1": "10", "z2": "01", "z3": "11", "z4": "10",
                                "z5": "01", "z6": "11", "z7": "10", "z8": "01",
                                "z9": "1"})
        # The separately declared variables are the ports' storage, not
        # extra declarations.
        self.assertEqual(env["design"]["modules"][0]["decls"], [])

    def test_explicit_port_expressions_are_loud(self):
        for header, decl in (("module top (a, .q(y));", "output [1:0] y; logic [1:0] y = 2'b10;"),
                             ("module top (a, .q(y));", "output [1:0] y; logic [1:0] y;"),
                             ("module top (a, y[1:0]);", "output [3:0] y; logic [3:0] y;")):
            with self.subTest(header=header, decl=decl):
                env = extract_sym("%s input a; %s endmodule\n" % (header, decl), "top")
                self.assertEqual(kinds(ports_of(env)),
                                 ["Port", "PortSymbol:explicit-expression"])

    def test_explicit_port_with_its_own_name_is_ordinary(self):
        env = extract_sym(
            "module top (a, .y(y)); input a; output [1:0] y; "
            "logic [1:0] y = 2'b10; endmodule\n", "top")
        self.assertEqual(ports_of(env)[1]["init"]["bits"], "10")


class ConvertedInitializers(unittest.TestCase):
    """(D): `Resize`/`SignedResize` of a literal, lowered exactly."""

    def init_of(self, decl, params=""):
        env = extract_sym("module top %s(output logic %s); endmodule\n"
                          % (params, decl), "top")
        return ports_of(env)[0]["init"]

    def test_binary_literals_become_their_value(self):
        for decl, value in (("[3:0] y = 2'b10", 2), ("[1:0] y = 4'b1110", 14),
                            ("[3:0] y = 2'sb10", -2), ("[3:0] y = 2'sb01", 1),
                            ("[3:0] y = 'b10", 2), ("[39:0] y = 'h3", 3)):
            with self.subTest(decl=decl):
                init = self.init_of(decl)
                self.assertEqual((init["kind"], init["value"]), ("Int", value))

    def test_parametric_width_uses_the_value_too(self):
        init = self.init_of("[N-1:0] y = 2'sb10", "#(parameter int N = 4) ")
        self.assertEqual((init["kind"], init["value"]), ("Int", -2))

    def test_x_literal_at_a_fixed_width_is_extended(self):
        for decl, bits in (("[3:0] y = 2'bx1", "00x1"), ("[1:0] y = 4'bx1z0", "z0"),
                           ("[3:0] y = 2'sb1x", "111x")):
            with self.subTest(decl=decl):
                init = self.init_of(decl)
                self.assertEqual((init["kind"], init["width"], init["bits"]),
                                 ("Literal", 4 if "[3:0]" in decl else 2, bits))

    def test_unrepresentable_conversions_stay_loud(self):
        # A parametric width with an x bit, and a signed x sign bit, keep the
        # conversion (Lean's `instDecl` refuses them).
        self.assertEqual(self.init_of("[N-1:0] y = 2'bx1",
                                      "#(parameter int N = 4) ")["kind"], "Resize")
        self.assertEqual(self.init_of("[3:0] y = 2'sbx0")["kind"], "SignedResize")

    def test_variable_initializer_is_lowered_too(self):
        env = extract_sym("module top (output logic [3:0] y); "
                          "logic [3:0] t = 2'b10; assign y = t; endmodule\n", "top")
        init = env["design"]["modules"][0]["decls"][0]["init"]
        self.assertEqual((init["kind"], init["value"]), ("Int", 2))


class InitializedProceduralWriters(unittest.TestCase):
    """(E): an always_comb / always_ff writer of an initialized variable."""

    def procs(self, source):
        env = extract_sym(source, "top")
        return kinds(env["design"]["modules"][0]["processes"])

    def test_exclusive_writers_are_refused(self):
        for decl, proc in (
                ("logic [1:0] t = 2'b10;", "always_comb t[0] = a;"),
                ("logic [1:0] t = 2'b10;", "always_comb t = {a, a};"),
                ("logic [1:0] t = 2'b10;", "always_ff @(posedge clk) t[0] <= a;"),
                ("logic [1:0] t = 2'b10;", "always_ff @(posedge clk) {t[1], t[0]} <= {a, a};"),
                ("logic [1:0] t = 2'b10;",
                 "always_comb begin if (a) t[0] = 1'b1; else t[0] = 1'b0; end")):
            with self.subTest(proc=proc):
                ks = self.procs(
                    "module top (input logic clk, a, output logic [1:0] y); "
                    "%s %s assign y = t; endmodule\n" % (decl, proc))
                self.assertEqual(ks, ["ProceduralBlockSymbol:initialized-variable", "Assign"])

    def test_initialized_output_ports_are_refused(self):
        for module in (
                "module top (input logic clk, a, output logic [1:0] y = 2'b10); "
                "always_ff @(posedge clk) y[0] <= a; endmodule\n",
                "module top (clk, a, y); input clk, a; output [1:0] y; "
                "logic [1:0] y = 2'b10; always_ff @(posedge clk) y[0] <= a; endmodule\n",
                "module top (input logic a, output logic [1:0] y = 2'b10); "
                "always_comb y[0] = a; endmodule\n"):
            with self.subTest(module=module):
                self.assertEqual(self.procs(module),
                                 ["ProceduralBlockSymbol:initialized-variable"])

    def test_uninitialized_and_block_local_targets_are_unchanged(self):
        # An index expression is read; a variable declared inside the block
        # (static or automatic) is the block's own.
        for body in ("always_comb t[k] = a;",
                     "always_comb begin : b logic [1:0] u = 2'b10; u[0] = a; t = u; end",
                     "always_comb begin : b automatic logic [1:0] u = 2'b10; u[0] = a; t = u; end"):
            with self.subTest(body=body):
                ks = self.procs(
                    "module top (input logic a, output logic [1:0] y); "
                    "logic k = 1'b0; logic [1:0] t; %s assign y = t; endmodule\n" % body)
                self.assertNotIn("ProceduralBlockSymbol:initialized-variable", ks)


class FailsClosed(unittest.TestCase):
    """(F): `_sym_initialized_target_info` never admits what it cannot see."""

    def test_unknown_target_shape(self):
        class Opaque:
            pass
        self.assertEqual(extract._sym_initialized_target_info(Opaque()),
                         ("unknown", "Opaque"))
        self.assertEqual(extract._sym_initialized_target(Opaque()), "unknown")

    def test_exception_while_inspecting(self):
        class NamedValueExpression:
            @property
            def symbol(self):
                raise RuntimeError("boom")
        info = extract._sym_initialized_target_info(NamedValueExpression())
        self.assertEqual(info[0], "unknown")
        self.assertIn("RuntimeError", info[1])

    def test_procedural_walker_fails_closed(self):
        class Body:
            def visit(self, callback):
                raise RuntimeError("boom")
        self.assertEqual(extract._sym_proc_initialized_write(Body())[0], "unknown")


class UnsizedXZInitializers(unittest.TestCase):
    """(G): §5.7.1 extension of an unsized x/z literal initializer."""

    def init_of(self, decl, params=""):
        env = extract_sym("module top %s(output logic %s); endmodule\n"
                          % (params, decl), "top")
        return ports_of(env)[0]["init"]

    def test_fixed_widths_pad_with_the_high_order_bit(self):
        for decl, bits in (("[39:0] y = 'bx", "x" * 40),
                           ("[39:0] y = 'hz1", "z" * 36 + "0001"),
                           ("[39:0] y = 'hx0", "x" * 36 + "0000"),
                           ("[35:0] y = 'bz", "z" * 36),
                           ("[39:0] y = 'hx", "x" * 40),
                           ("[39:0] y = 'dz", "z" * 40),
                           # truncation keeps the low bits; a 0 high-order
                           # bit zero-extends
                           ("[3:0] y = 'hz1", "0001"),
                           ("[31:0] y = 'hz1", "z" * 28 + "0001"),
                           ("[39:0] y = 'h0x", "0" * 36 + "xxxx")):
            with self.subTest(decl=decl):
                init = self.init_of(decl)
                self.assertEqual((init["kind"], init["width"], init["bits"]),
                                 ("Literal", len(bits), bits))

    def test_fixed_width_in_a_family_too(self):
        init = self.init_of("[39:0] y = 'hz1", "#(parameter int N = 4) ")
        self.assertEqual((init["kind"], init["bits"]), ("Literal", "z" * 36 + "0001"))

    def test_sized_and_signed_literals_are_unchanged(self):
        # A SIZED x literal zero-extends (§5.7.1 pads only within its own
        # size); a signed unsized x sign bit stays loud.
        init = self.init_of("[39:0] y = 32'hx")
        self.assertEqual(init["bits"], "0" * 8 + "x" * 32)
        # Round 5 (J): an unsized SIGNED based literal is refused outright.
        init = self.init_of("[39:0] y = 'sbx")
        self.assertEqual((init["kind"], init["sv_kind"]),
                         ("Unsupported", "Initializer:unsized-signed"))

    def test_variable_form(self):
        env = extract_sym("module top (output logic [39:0] y); "
                          "logic [39:0] s = 'hx5; assign y = s; endmodule\n", "top")
        init = env["design"]["modules"][0]["decls"][0]["init"]
        self.assertEqual(init["bits"], "x" * 36 + "0101")


class ParametricPlainLiterals(unittest.TestCase):
    """(H): a literal with no conversion at the default point, at a width
    that depends on a parameter."""

    def init_of(self, decl, default="4"):
        env = extract_sym("module top #(parameter int N = %s) (output logic %s); "
                          "endmodule\n" % (default, decl), "top")
        return ports_of(env)[0]["init"]

    def test_binary_literals_become_their_value(self):
        # (`[N-1:0] y = 'sb1`, admitted in round 4, is refused in round 5:
        # class UnsizedSignedLiterals.)
        for decl, value in (("[N-1:0] y = 4'b1010", 10), ("[N-1:0] y = 4'sb1010", -6),
                            ("[N+27:0] y = 'h5", 5)):
            with self.subTest(decl=decl):
                init = self.init_of(decl)
                self.assertEqual((init["kind"], init["value"]), ("Int", value))

    def test_one_repeated_xz_bit_is_a_fill(self):
        for decl, bit in (("[N-1:0] y = 'bx", "x"), ("[N-1:0] y = 'hz", "z"),
                          ("[N+39:0] y = 'bz", "z")):
            with self.subTest(decl=decl):
                init = self.init_of(decl)
                self.assertEqual((init["kind"], init["bit"]), ("Fill", bit))

    def test_other_xz_literals_are_loud(self):
        for decl in ("[N-1:0] y = 4'bx01x", "[N-1:0] y = 'hz1", "[N+39:0] y = 'hx0"):
            with self.subTest(decl=decl):
                init = self.init_of(decl)
                self.assertEqual((init["kind"], init["sv_kind"]),
                                 ("Unsupported", "Initializer:x-literal-parametric-width"))

    def test_child_variable_form(self):
        env = extract_sym(
            "module c #(parameter int W = 4) (output logic [W-1:0] o); "
            "logic [W-1:0] t = 4'sb1010; assign o = t; endmodule\n"
            "module top (output logic [7:0] z); c #(.W(8)) u (.o(z)); endmodule\n",
            "top")
        child = [mod for mod in env["design"]["modules"] if mod["name"] == "c"][0]
        init = child["decls"][0]["init"]
        self.assertEqual((init["kind"], init["value"]), ("Int", -6))

    def test_fixed_width_literals_are_unchanged(self):
        init = self.init_of("[3:0] y = 4'b1010")
        self.assertEqual((init["kind"], init["bits"]), ("Literal", "1010"))


class InitializedInputs(unittest.TestCase):
    """(I): an initializer on a non-ANSI input's internal symbol."""

    def test_separately_declared_initializers_are_loud(self):
        for decl in ("logic [1:0] a = 2'b01;", "reg [1:0] a = 2'b01;",
                     "var logic [1:0] a = 2'b01;", "wire [1:0] a = 2'b01;"):
            with self.subTest(decl=decl):
                env = extract_sym("module top (a, y); input [1:0] a; "
                                  "output logic [1:0] y; %s assign y = a; "
                                  "endmodule\n" % decl, "top")
                self.assertEqual(kinds(ports_of(env)),
                                 ["PortSymbol:initialized-input", "Port"])

    def test_child_form_is_loud(self):
        env = extract_sym(
            "module c (a, y); input [1:0] a; output logic [1:0] y; "
            "logic [1:0] a = 2'b01; assign y = a; endmodule\n"
            "module top (input logic [1:0] b, output logic [1:0] y); "
            "c u (.a(b), .y(y)); endmodule\n", "top")
        child = [mod for mod in env["design"]["modules"] if mod["name"] == "c"][0]
        self.assertEqual(kinds(child["ports"]), ["PortSymbol:initialized-input", "Port"])

    def test_ansi_port_default_and_plain_inputs_are_unchanged(self):
        for header in ("module top (input logic [1:0] a = 2'b01, output logic [1:0] y);",
                       "module top (a, y); input [1:0] a; output logic [1:0] y; "
                       "logic [1:0] a;"):
            with self.subTest(header=header):
                env = extract_sym("%s assign y = a; endmodule\n" % header, "top")
                ports = ports_of(env)
                self.assertEqual(kinds(ports), ["Port", "Port"])
                self.assertNotIn("init", ports[0])


class UnsizedXZExpressions(unittest.TestCase):
    """(G): the expression-context twin (`_sym_unsized_xz_widening`)."""

    def values(self, source, top="top"):
        env = extract_sym(source, top)
        procs = env["design"]["modules"][0]["processes"]
        return [p["value"] for p in procs if p.get("kind") == "Assign"]

    def test_one_point_module_pads(self):
        (v1, v2) = self.values(
            "module top (output logic [39:0] y, z); assign y = 'bx; "
            "assign z = 'hz1; endmodule\n")
        self.assertEqual((v1["kind"], v1["bits"]), ("Literal", "x" * 40))
        self.assertEqual((v2["kind"], v2["bits"]), ("Literal", "z" * 36 + "0001"))

    def test_family_is_loud(self):
        for rhs in ("'bx", "'hz1"):
            with self.subTest(rhs=rhs):
                (v,) = self.values(
                    "module top #(parameter int N = 40) (output logic [N-1:0] y); "
                    "assign y = %s; endmodule\n" % rhs)
                self.assertEqual((v["kind"], v["sv_kind"]),
                                 ("Unsupported", "ConversionExpression:unsized-xz"))

    def test_uninspectable_literal_fails_closed(self):
        class IntegerLiteral:
            sourceRange = None
            @property
            def isDeclaredUnsized(self):
                raise RuntimeError("boom")
        saved = extract._SYM
        extract._SYM = object()
        try:
            node = extract._sym_unsized_xz_widening(None, IntegerLiteral(),
                                                    IntegerLiteral(), 40)
        finally:
            extract._SYM = saved
        self.assertEqual((node["kind"], node["sv_kind"]),
                         ("Unsupported", "ConversionExpression:unsized-xz"))

    def test_other_literals_are_unchanged(self):
        # A sized x literal and a 0 high-order bit zero-extend (Resize); a
        # narrowing context is not a widening. (Round 5 repair: in a family
        # the module is refused anyway — `XZLiteralScan` below.)
        source = ("module top #(parameter int N = 40) (output logic [N-1:0] y, z, "
                  "output logic [3:0] w); assign y = 8'bx; assign z = 'h0x; "
                  "assign w = 'hz1; endmodule\n")
        (v1, v2, v3) = self.values(source)
        self.assertEqual(v1["kind"], "Resize")
        self.assertEqual(v2["kind"], "Resize")
        self.assertNotEqual(v3["kind"], "Unsupported")
        others = kinds(extract_sym(source, "top")["design"]["modules"][0]["others"])
        self.assertIn("ConversionExpression:xz-literal-parametric", others)
        self.assertIn("IntegerLiteral:unsized-xz-parametric", others)


if __name__ == "__main__":
    unittest.main()


# Round 5 (Lane A, 2026-10-29), refusal-only:
#
# (J) An UNSIZED SIGNED BASED literal (`'sb1`, `'sh8`, `'sd5`) is loud: as a
# declaration or port initializer (`Initializer:unsized-signed`, loud at
# 2e8c8b28 as a `SignedResize` `instDecl` refused) and ANYWHERE in the
# compiled sources (`IntegerLiteral:unsized-signed` in the top's `others`,
# `_sym_unsized_signed_scan`). Icarus 12.0 sizes the literal to its digits
# and sign-extends (`'sb1` reads -1 in every context measured); Verilator
# 5.042, Yosys 0.53, Xcelium 24.03 and §5.7.1 read the digits zero-padded.
#
# (K) An unsized x/z literal widened inside an INPUT PORT ACTUAL
# (`PortConnection:unsized-xz`; Icarus zero-pads the port, Xcelium and Yosys
# extend the x), a CONSTANT position (`ConversionExpression:unsized-xz-
# constant`; a `case` item is x-padded by Icarus but read as a don't-care
# by the Yosys netlist, and a typed localparam or an override is x-padded by
# Icarus and zero-padded by Yosys and slang — those two were already loud in
# the Lean constant tier) or an unpacked-array pattern element (no
# Icarus/Yosys oracle; loud at 2e8c8b28) is loud.


def others_of(env, module=0):
    return env["design"]["modules"][module]["others"]


class UnsizedSignedLiterals(unittest.TestCase):
    """(J)."""

    def test_initializers_are_loud(self):
        for decl in ("[7:0] y = 'sb1", "[7:0] y = 'sh8", "[39:0] y = 'shF",
                     "[31:0] y = 'sb1", "[7:0] y = 'sd5", "[7:0] y = 'Sb01"):
            with self.subTest(decl=decl):
                env = extract_sym("module top (output logic %s); endmodule\n"
                                  % decl, "top")
                init = ports_of(env)[0]["init"]
                self.assertEqual((init["kind"], init["sv_kind"]),
                                 ("Unsupported", "Initializer:unsized-signed"))
                self.assertEqual(kinds(others_of(env)),
                                 ["IntegerLiteral:unsized-signed"])

    def test_parametric_and_variable_forms_are_loud(self):
        env = extract_sym("module top #(parameter int N = 8) "
                          "(output logic [N-1:0] y); logic [N-1:0] t = 'sb1; "
                          "assign y = t; endmodule\n", "top")
        init = env["design"]["modules"][0]["decls"][0]["init"]
        self.assertEqual(init["sv_kind"], "Initializer:unsized-signed")

    def test_every_context_is_loud(self):
        for body in ("assign y = 'sb1;", "assign y = a + 'sh8;",
                     "localparam P = 'sh8; assign y = P;",
                     "assign y = {7'b0, a['sb1]};",
                     "always_comb case (a) 'sb1: y = 1; default: y = 2; endcase",
                     "assign y = -'so7;"):
            with self.subTest(body=body):
                env = extract_sym("module top (input logic [7:0] a, "
                                  "output logic [7:0] y); %s endmodule\n"
                                  % body, "top")
                self.assertIn("IntegerLiteral:unsized-signed",
                              kinds(others_of(env)))

    def test_child_module_and_package_are_loud(self):
        env = extract_sym(
            "package p; localparam int Q = 'sh8; endpackage\n"
            "module c (output logic [7:0] o); assign o = p::Q; endmodule\n"
            "module top (output logic [7:0] y); c u (.o(y)); endmodule\n", "top")
        self.assertIn("IntegerLiteral:unsized-signed", kinds(others_of(env)))

    def test_sized_signed_unsized_unsigned_and_decimals_are_unchanged(self):
        env = extract_sym("module top (output logic [7:0] y, z, w, v); "
                          "assign y = 8'sb1; assign z = 'b1; assign w = 5; "
                          "assign v = -5; endmodule\n", "top")
        self.assertNotIn("IntegerLiteral:unsized-signed", kinds(others_of(env)))
        procs = env["design"]["modules"][0]["processes"]
        self.assertFalse(any(p.get("kind") == "Unsupported" for p in procs))


class UnsizedXZRefusals(unittest.TestCase):
    """(K)."""

    def test_input_port_actuals_are_loud(self):
        child = ("module c #(parameter int W = 40) (input logic [W-1:0] i, "
                 "output logic [W-1:0] o); assign o = i; endmodule\n")
        for actual in ("'hx0", "'bz", "s ? 'hx0 : 'h5", "s ? 'hx0 : 40'd5",
                       "'hx0 | a"):
            with self.subTest(actual=actual):
                env = extract_sym(
                    child + "module top (input logic s, input logic [7:0] a, "
                    "output logic [39:0] y); c u (.i(%s), .o(y)); endmodule\n"
                    % actual, "top")
                inst = env["design"]["modules"][0]["generates"][0]
                self.assertIn("PortConnection:unsized-xz",
                              json.dumps(inst["ports"][0]))

    def test_narrowing_and_equal_width_actuals_are_loud_too(self):
        # Round 5 repair: an actual HOLDING an unsized x/z-top literal is
        # loud whatever the port width at the bound point (the port can be
        # wider at another point: verifier `vp1`, `vp2`, `vp7`). At these
        # fixed widths the tools agree: a recorded over-refusal.
        child = ("module c #(parameter int W = 8) (input logic [W-1:0] i, "
                 "output logic [W-1:0] o); assign o = i; endmodule\n")
        for width in (8, 32):
            with self.subTest(width=width):
                env = extract_sym(
                    child + "module top (output logic [%d:0] y); "
                    "c #(.W(%d)) u (.i('hx0), .o(y)); endmodule\n"
                    % (width - 1, width), "top")
                inst = env["design"]["modules"][0]["generates"][0]
                self.assertEqual(kinds(inst["ports"]), ["PortConn", "PortConn"])
                self.assertEqual(inst["ports"][0]["expr"]["sv_kind"],
                                 "PortConnection:unsized-xz")

    def test_sized_and_zero_top_actuals_are_unchanged(self):
        child = ("module c #(parameter int W = 8) (input logic [W-1:0] i, "
                 "output logic [W-1:0] o); assign o = i; endmodule\n")
        for actual in ("8'hx0", "'h0x"):
            with self.subTest(actual=actual):
                env = extract_sym(
                    child + "module top (output logic [7:0] y); "
                    "c #(.W(8)) u (.i(%s), .o(y)); endmodule\n" % actual, "top")
                inst = env["design"]["modules"][0]["generates"][0]
                self.assertNotEqual(inst["ports"][0]["expr"]["kind"],
                                    "Unsupported")

    def test_constant_positions_are_loud(self):
        env = extract_sym(
            "module c #(parameter logic [39:0] P = 40'd0) (output logic [39:0] o); "
            "assign o = P; endmodule\n"
            "module top (input logic [39:0] b, output logic [39:0] y, z, "
            "output logic [7:0] k); localparam logic [39:0] LP = 'hx0; "
            "assign y = LP; always_comb case (b) 'hx0: k = 1; default: k = 2; "
            "endcase c #(.P('hz1)) u (.o(z)); endmodule\n", "top")
        top = env["design"]["modules"][0]
        self.assertEqual(top["params"][0]["expr"]["sv_kind"],
                         "ConversionExpression:unsized-xz-constant")
        self.assertEqual(top["generates"][0]["params"][0]["expr"]["sv_kind"],
                         "ConversionExpression:unsized-xz-constant")
        self.assertIn("ConversionExpression:unsized-xz-constant",
                      json.dumps(top["processes"]))

    def test_array_pattern_elements_are_loud(self):
        env = extract_sym("module top (output logic [39:0] y); "
                          "logic [39:0] m [0:1] = '{'hx0, 'hz1}; "
                          "assign y = m[0]; endmodule\n", "top")
        decl = env["design"]["modules"][0]["decls"][0]
        self.assertEqual((decl["kind"], decl["sv_kind"]),
                         ("Unsupported", "Initializer:unsized-xz-element"))

    def test_assignments_and_declarations_still_pad(self):
        env = extract_sym("module top (input logic s, output logic [39:0] y, z); "
                          "logic [39:0] t = 'hx0; wire [39:0] w = 'hz1; "
                          "assign y = s ? 'hx0 : t; assign z = w; endmodule\n",
                          "top")
        top = env["design"]["modules"][0]
        self.assertEqual(top["decls"][0]["init"]["bits"], "x" * 36 + "0000")
        self.assertEqual(top["decls"][1]["init"]["bits"], "z" * 36 + "0001")
        self.assertEqual(top["processes"][0]["value"]["then"]["bits"],
                         "x" * 36 + "0000")


# Round 5 repair (Lane A, 2026-10-29; verifier of the round-5 INIT repair):
#
# (L) THE x/z LITERAL CHOKE POINT (`_sym_xz_literal_scan`, one bound-tree
# walk per converted module, findings in its `others`). In a scope whose
# context widths differ between points (a module with an overridable
# parameter, a generate-for body) every unsized x/z-top literal is loud
# (`IntegerLiteral:unsized-xz-parametric`) and so is every x/z-bearing
# literal under an implicit conversion that changes its width
# (`ConversionExpression:xz-literal-parametric`): the envelope fixed its
# value at the default point (no conversion at a 32-bit default, a folded
# `Literal` at a narrower one) and Lean zero-extended it elsewhere. A
# declaration initializer `_sym_decl_init` decides from the literal is the
# exception. In any scope, `$unsigned` of an unsized x/z-top literal widened
# by its context is loud (`CallExpression:unsized-xz-cast`: Icarus
# zero-extends, the Yosys netlist extends the x/z). An input port actual
# holding an unsized x/z-top literal is `PortConnection:unsized-xz` at any
# width.


def module_others(env, module=0):
    return kinds(env["design"]["modules"][module]["others"])


class XZLiteralScan(unittest.TestCase):
    """(L)."""

    def test_family_literals_are_loud_at_any_default(self):
        for n, rhs, kind in (
                (32, "'hx0", "IntegerLiteral:unsized-xz-parametric"),
                (32, "'bx", "IntegerLiteral:unsized-xz-parametric"),
                (8, "'hz1", "ConversionExpression:xz-literal-parametric"),
                (8, "12'hxF0", "ConversionExpression:xz-literal-parametric"),
                (40, "12'hxF0", "ConversionExpression:xz-literal-parametric")):
            with self.subTest(n=n, rhs=rhs):
                env = extract_sym(
                    "module top #(parameter int N = %d) (output logic [N-1:0] y); "
                    "assign y = %s; endmodule\n" % (n, rhs), "top")
                self.assertIn(kind, module_others(env))

    def test_family_case_item_is_loud(self):
        env = extract_sym(
            "module top #(parameter int N = 32) (input logic [N-1:0] b, "
            "output logic [7:0] y); always_comb case (b) 'hz1: y = 1; "
            "default: y = 2; endcase endmodule\n", "top")
        self.assertIn("IntegerLiteral:unsized-xz-parametric", module_others(env))

    def test_child_definition_is_loud(self):
        env = extract_sym(
            "module c #(parameter int W = 32) (output logic [W-1:0] o); "
            "assign o = 'hx0; endmodule\n"
            "module top (output logic [39:0] y); c #(.W(40)) u (.o(y)); "
            "endmodule\n", "top")
        self.assertEqual(module_others(env, 0), [])
        self.assertIn("IntegerLiteral:unsized-xz-parametric",
                      module_others(env, 1))

    def test_generate_for_body_is_loud_and_the_rest_is_not(self):
        env = extract_sym(
            "module top (output logic [39:0] y, output logic [1:0][39:0] v); "
            "assign y = 'hx0; "
            "for (genvar g = 0; g < 2; g++) begin : G assign v[g] = 'hz1; end "
            "endmodule\n", "top")
        found = [o for o in env["design"]["modules"][0]["others"]
                 if o.get("sv_kind") == "IntegerLiteral:unsized-xz-parametric"]
        self.assertEqual([o["span"]["line"] for o in found], [1])
        self.assertEqual(len(found), 1)
        procs = env["design"]["modules"][0]["processes"]
        self.assertEqual(procs[0]["value"]["bits"], "x" * 36 + "0000")

    def test_declaration_literals_stay_with_sym_decl_init(self):
        env = extract_sym(
            "module top #(parameter int N = 32) (output logic [N-1:0] y, z); "
            "logic [N-1:0] t = 'bx; logic [N-1:0] u = 'hz; "
            "assign y = t; assign z = u; endmodule\n", "top")
        top = env["design"]["modules"][0]
        self.assertEqual([d["init"]["kind"] for d in top["decls"]],
                         ["Fill", "Fill"])
        self.assertEqual(module_others(env), [])

    def test_non_literal_declaration_initializer_is_not_exempt(self):
        env = extract_sym(
            "module top #(parameter int N = 32) (output logic [N-1:0] y); "
            "logic [N-1:0] t = 'hx0 | 8'd1; assign y = t; endmodule\n", "top")
        self.assertIn("IntegerLiteral:unsized-xz-parametric", module_others(env))

    def test_zero_one_and_own_width_literals_are_unchanged(self):
        env = extract_sym(
            "module top #(parameter int N = 8) (output logic [N-1:0] y, z, w); "
            "assign y = 'h1FF; assign z = 12'hFFF; assign w = 8'hx0; "
            "endmodule\n", "top")
        self.assertEqual(module_others(env), [])

    def test_one_point_module_is_unchanged(self):
        env = extract_sym(
            "module top (input logic s, output logic [39:0] y, output logic [7:0] k); "
            "assign y = s ? 'hx0 : 'h5; assign k = 12'hxF0; endmodule\n", "top")
        self.assertEqual(module_others(env), [])

    def test_unsigned_cast_widened_is_loud(self):
        for rhs, loud in (("$unsigned('hz1)", True),
                          ("$unsigned('hz1) | a", True),
                          ("$unsigned('hx0 | a)", True),
                          ("$signed('hz1)", False),
                          ("$unsigned(8'hx0)", False)):
            with self.subTest(rhs=rhs):
                env = extract_sym(
                    "module top (input logic [7:0] a, output logic [39:0] y); "
                    "assign y = %s; endmodule\n" % rhs, "top")
                self.assertEqual("CallExpression:unsized-xz-cast"
                                 in module_others(env), loud)

    def test_unsigned_cast_not_widened_is_unchanged(self):
        env = extract_sym(
            "module top (output logic [31:0] y, output logic [7:0] z); "
            "assign y = $unsigned('hz1); assign z = $unsigned('hx0); "
            "endmodule\n", "top")
        self.assertEqual(module_others(env), [])

    def test_scan_fails_closed(self):
        class Body:
            def visit(self, callback):
                raise RuntimeError("boom")

        class Bad:
            def visit(self, callback):
                raise RuntimeError("boom")

        found = extract._sym_xz_literal_scan(None, Body())
        self.assertEqual(kinds(found), ["ExtractorInternal:RuntimeError"])
        self.assertTrue(extract._sym_contains_unsized_xz(Bad()))
