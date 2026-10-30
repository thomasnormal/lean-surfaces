"""Assignment spellings of the generate-for step (WP-L1).

IEEE 1800-2023 27.4 lets a genvar step be `g++`, `++g`, `g--`, `--g` or an
assignment (`g = g + 1`, `g += 1`). The symbolic lowering used to keep every
assignment step as an `Unsupported` `AssignmentExpression`, so the adder
`for (i = 0; i < N; i = i + 1)` was refused although `i++` was fine (the
svGolf READMEs called it "an ls-sv gap, not a rule"). The plus-or-minus-1
assignment forms (`g = g + 1`, `g = 1 + g`, `g += 1`, `g = g - 1`, `g -= 1`,
parenthesised or not, with the plain signed integer literal 1) now lower to
THE SAME `Unary` `++` / `--` node as `g++` / `g--`; every other assignment
step is the loud `GenerateFor:step`.
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


def generate_fors(node, out=None):
    out = [] if out is None else out
    if isinstance(node, dict):
        if node.get("kind") == "GenerateFor":
            out.append(node)
        for value in node.values():
            generate_fors(value, out)
    elif isinstance(node, list):
        for value in node:
            generate_fors(value, out)
    return out


def unspanned(node):
    """The node without any `span` (the spelling moves the columns)."""
    return re.sub(r'"span": (\{[^}]*\}|null)', '"span": 0',
                  json.dumps(node, sort_keys=True))


class GenerateSteps(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("t", [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    def loop(self, init, cond, step, params="parameter int N = 4, parameter int K = 1"):
        source = (
            "module t #(%s) (input logic [N-1:0] a, b, output logic [N-1:0] y);"
            " genvar i; generate for (i = %s; %s; %s) begin : g"
            " assign y[i] = a[i] ^ b[i]; end endgenerate endmodule" % (params, init, cond, step))
        fors = generate_fors(self.extract(source))
        self.assertEqual(len(fors), 1)
        return fors[0]

    def test_increasing_spellings_equal_postincrement(self):
        base = self.loop("0", "i < N", "i++")
        self.assertEqual(base["step"]["kind"], "Unary")
        self.assertEqual(base["step"]["op"], "++")
        for step in ("++i", "i = i + 1", "i += 1", "i = 1 + i", "i = (i + 1)",
                     "i = i + 32'sd1", "i = i + (1)"):
            with self.subTest(step=step):
                got = self.loop("0", "i < N", step)
                self.assertEqual(sv_kinds(got), [])
                self.assertEqual(got["step"]["kind"], "Unary")
                self.assertEqual(got["step"]["op"], "++")
                self.assertEqual(got["step"]["operand"]["kind"], "GenvarRef")
                self.assertEqual(unspanned(got), unspanned(base))

    def test_decreasing_spellings_equal_postdecrement(self):
        base = self.loop("N-1", "i >= 0", "i--")
        self.assertEqual(base["step"]["op"], "--")
        for step in ("--i", "i = i - 1", "i -= 1", "i = (i - 1)"):
            with self.subTest(step=step):
                got = self.loop("N-1", "i >= 0", step)
                self.assertEqual(sv_kinds(got), [])
                self.assertEqual(got["step"]["op"], "--")
                self.assertEqual(unspanned(got), unspanned(base))

    def test_other_assignment_steps_stay_loud(self):
        # not +/-1, not the genvar, a parameter amount, a narrower or unsigned
        # amount (it changes the arithmetic type), a mixed compound operator.
        for step in ("i += 2", "i = i + 2", "i -= 2", "i = i * 2", "i = i + K",
                     "i = 1 - i", "i = i + 0", "i = i + 1'b1", "i = N - 1 - i",
                     "i = i", "i = 0", "i = i + 1 + 0", "i = i + 'd1"):
            with self.subTest(step=step):
                got = self.loop("0", "i < N", step)
                self.assertEqual(got["step"]["kind"], "Unsupported")
                self.assertEqual(got["step"]["sv_kind"], "GenerateFor:step")
                self.assertIn("is not a +/-1 step", got["step"]["text"])
                self.assertIn(step, got["step"]["text"])

    def test_parameter_amount_is_not_folded_to_one(self):
        # K = 1 at the defaults: still never read as `i++` (folded at one point only)
        got = self.loop("0", "i < N", "i = i + K")
        self.assertEqual(got["step"]["sv_kind"], "GenerateFor:step")

    def test_nested_loops_and_inline_genvars(self):
        source = (
            "module t #(parameter int N = 3, parameter int M = 2) (input logic [N-1:0] a,"
            " input logic [M-1:0] b, output logic [N*M-1:0] p);"
            " generate for (genvar i = 0; i < N; i = i + 1) begin : r"
            " for (genvar j = 0; j < M; j += 1) begin : c"
            " assign p[i*M+j] = a[i] & b[j]; end end endgenerate endmodule")
        module = self.extract(source)
        self.assertEqual(sv_kinds(module), [])
        steps = [(g["genvar"], g["step"]["op"]) for g in generate_fors(module)]
        self.assertEqual(sorted(steps), [("i", "++"), ("j", "++")])

    def test_assignment_step_on_another_genvar_is_loud(self):
        source = (
            "module t #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);"
            " genvar i, j; generate for (i = 0; i < N; j = j + 1) begin : g"
            " assign y[i] = a[i]; end endgenerate endmodule")
        module = self.extract(source)
        self.assertNotEqual(sv_kinds(module), [])


if __name__ == "__main__":
    unittest.main()
