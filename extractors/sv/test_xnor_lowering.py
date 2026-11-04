"""The binary XNOR `~^` / `^~` in signal expressions of the symbolic tier (WP-L2).

`a ~^ b` and `a ^~ b` are ONE slang operator (BinaryXnor). The symbolic lowering used to refuse it
(`BinaryExpression:BinaryXnor`); in a SIGNAL expression it is now `~(a ^ b)`, a `Unary` `~` over the
`Binary` `^` the tier already has: slang has converted both operands to the expression's own type, so
the inner `^` and the outer `~` carry exactly the xnor's context width and signedness, and the
4-state table (any x/z operand bit gives x, equal known bits give 1) is the product of the two
pinned ones. In a symbolic-CONSTANT position (parameter default, localparam, generate condition)
the operator stays the loud `BinaryExpression:BinaryXnor`. The reduction `~^a` was already admitted
and is unchanged.
"""
import json
import re
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


def unspanned(node):
    return re.sub(r'"span": (\{[^}]*\}|null)', '"span": 0', json.dumps(node, sort_keys=True))


def assigns(module):
    return {p["target"]["name"]: p["value"] for p in module["processes"]
            if p["kind"] == "Assign" and p["target"]["kind"] == "Ident"}


class XnorLowering(unittest.TestCase):
    def extract(self, source, top="t"):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic(top, [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    def test_binary_is_not_of_a_and_b(self):
        m = self.extract("module t (input logic [3:0] a, b, output logic [3:0] y);"
                         " assign y = a ~^ b; endmodule")
        self.assertEqual(sv_kinds(m), [])
        v = assigns(m)["y"]
        self.assertEqual((v["kind"], v["op"], v["width"]), ("Unary", "~", 4))
        inner = v["operand"]
        self.assertEqual((inner["kind"], inner["op"], inner["width"]), ("Binary", "^", 4))
        self.assertEqual([inner["left"]["name"], inner["right"]["name"]], ["a", "b"])

    def test_both_spellings_are_the_same_node(self):
        def node(op):
            m = self.extract("module t (input logic [3:0] a, b, output logic [3:0] y);"
                             " assign y = a %s b; endmodule" % op)
            return unspanned(assigns(m)["y"])
        self.assertEqual(node("~^"), node("^~"))

    def test_equal_to_the_hand_written_complement(self):
        # the lowering IS what a golfer would write by hand
        def node(expr):
            m = self.extract("module t (input logic [7:0] a, b, output logic [15:0] y);"
                             " assign y = %s; endmodule" % expr)
            return unspanned(assigns(m)["y"])
        self.assertEqual(node("a ~^ b"), node("~(a ^ b)"))

    def test_context_widening_extends_operands_before_the_operator(self):
        m = self.extract("module t (input logic [7:0] a, b, output logic [15:0] y);"
                         " assign y = a ~^ b; endmodule")
        self.assertEqual(sv_kinds(m), [])
        v = assigns(m)["y"]
        self.assertEqual((v["op"], v["width"]), ("~", 16))
        inner = v["operand"]
        self.assertEqual((inner["op"], inner["width"]), ("^", 16))
        for side in ("left", "right"):
            self.assertEqual((inner[side]["kind"], inner[side]["width"]), ("Resize", 16))
            self.assertEqual(inner[side]["operand"]["width"], 8)

    def test_chain_is_left_associative(self):
        m = self.extract("module t (input logic [3:0] a, b, c, output logic [3:0] y);"
                         " assign y = a ~^ b ~^ c; endmodule")
        self.assertEqual(sv_kinds(m), [])
        outer = assigns(m)["y"]["operand"]
        self.assertEqual(outer["op"], "^")
        self.assertEqual(outer["right"]["name"], "c")
        left = outer["left"]
        self.assertEqual((left["kind"], left["op"]), ("Unary", "~"))
        self.assertEqual([left["operand"]["left"]["name"], left["operand"]["right"]["name"]], ["a", "b"])

    def test_operand_that_is_an_expression_and_one_bit_operands(self):
        m = self.extract("module t (input logic [3:0] a, b, c, input logic p, q,"
                         " output logic [3:0] y, output logic z); assign y = (a & b) ~^ c;"
                         " assign z = p ^~ q; endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(assigns(m)["y"]["operand"]["left"]["op"], "&")
        self.assertEqual(assigns(m)["z"]["width"], 1)

    def test_procedural_positions(self):
        m = self.extract(
            "module t (input logic clk, input logic [3:0] a, b, output logic [3:0] q, m);"
            " always_ff @(posedge clk) q <= q ~^ a; always_comb m = a ^~ b; endmodule")
        self.assertEqual(sv_kinds(m), [])

    def test_same_width_signed_pair_is_the_plain_table(self):
        m = self.extract("module t (input logic [3:0] a, b, output logic [3:0] y);"
                         " assign y = $signed(a) ~^ $signed(b); endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual(assigns(m)["y"]["op"], "~")

    def test_signed_pair_into_a_wider_target_is_loud_like_xor(self):
        # sign extension of the operands: the tier has none, and `^` refuses the same text
        for op in ("~^", "^~", "^"):
            with self.subTest(op=op):
                m = self.extract("module t (input logic [3:0] a, b, output logic [7:0] y);"
                                 " assign y = $signed(a) %s $signed(b); endmodule" % op)
                # one refusal per operand (each sign-extends)
                self.assertEqual(set(sv_kinds(m)), {"ConversionExpression:width"})
                self.assertGreaterEqual(len(sv_kinds(m)), 1)

    def test_constant_positions_stay_loud(self):
        m = self.extract("module t #(parameter int Q = (6 ~^ 3)) (input logic [3:0] a,"
                         " output logic [3:0] y); localparam logic [3:0] M = 4'b1010 ~^ 4'b0110;"
                         " assign y = a ^ M; endmodule")
        self.assertEqual(sorted(sv_kinds(m)), ["BinaryExpression:BinaryXnor"] * 2)
        g = self.extract("module t #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);"
                         " for (genvar i = 0; i < N; i++) begin : g if ((i ~^ 1) != 0) begin : u"
                         " assign y[i] = a[i]; end else begin : e assign y[i] = ~a[i]; end end endmodule")
        self.assertEqual(sv_kinds(g), ["BinaryExpression:BinaryXnor"])

    def test_reduction_is_unchanged(self):
        m = self.extract("module t (input logic [3:0] a, output logic r, s);"
                         " assign r = ~^a; assign s = ^~a; endmodule")
        self.assertEqual(sv_kinds(m), [])
        for name in ("r", "s"):
            v = assigns(m)[name]
            self.assertEqual((v["kind"], v["op"], v["width"]), ("Reduce", "~^", 1))

    def test_other_binary_operators_unchanged(self):
        m = self.extract("module t (input logic [3:0] a, b, output logic [3:0] y, z);"
                         " assign y = a ^ b; assign z = a & b; endmodule")
        self.assertEqual(sv_kinds(m), [])
        self.assertEqual((assigns(m)["y"]["kind"], assigns(m)["y"]["op"]), ("Binary", "^"))


if __name__ == "__main__":
    unittest.main()
