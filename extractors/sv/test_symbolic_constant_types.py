"""Constant-expression typing metadata in sv-0.2 symbolic mode (2026-10-28).

The Lean constant tier evaluates parameter and select-label arithmetic at
each operand's self-determined width and signedness (IEEE 1800-2023 11.6,
11.8; Param.lean `evalSized`). Two facts it needs are not otherwise in the
envelope:

* a DECLARED parameter type's signedness where it departs from the default
  (signed exactly when 32 bits wide): `int unsigned` and `logic [31:0]` get
  `signed: false`, `byte` gets `signed: true`; `int`, `integer`, narrow
  `logic` vectors and untyped parameters carry nothing (so envelopes of
  `parameter int N` designs are unchanged);
* a SIGNED literal in a symbolic constant position (`4'sd3`, or a constant
  slang typed `int` and folded to 32 bits) carries `signed: true`; value
  positions are unchanged (their operators carry signedness).
"""
import json
import tempfile
import unittest
from pathlib import Path

import extract


def find(node, pred, found=None):
    found = [] if found is None else found
    if isinstance(node, dict):
        if pred(node):
            found.append(node)
        for value in node.values():
            find(value, pred, found)
    elif isinstance(node, list):
        for value in node:
            find(value, pred, found)
    return found


class SymbolicConstantTypes(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    def test_parameter_signedness_marks_only_departures(self):
        module = self.extract(
            "module top #(parameter int A = 1, parameter int unsigned B = 2,"
            " parameter logic [31:0] C = 3, parameter logic [2:0] D = 3'd4,"
            " parameter integer E = 5, parameter byte F = 6, parameter G = 7)"
            " (input logic [15:0] v, output logic o);"
            " localparam int unsigned L = B + 1; localparam M = A;"
            " assign o = v[A]; endmodule")
        signed = {p["name"]: p.get("signed", "absent") for p in module["params"]}
        self.assertEqual(signed, {"A": "absent", "B": False, "C": False, "D": "absent",
                                  "E": "absent", "F": True, "G": "absent",
                                  "L": False, "M": "absent"})

    def test_signed_literal_in_constant_positions(self):
        module = self.extract(
            "module top #(parameter int N = 3) (input logic [15:0] v,"
            " input logic [3:0] a, output logic o, output logic [3:0] y);"
            " localparam L = 4'sd3; assign o = v[N + 4'sd3];"
            " assign y = a + 4'sd1; endmodule")
        local = [p for p in module["params"] if p["name"] == "L"][0]
        self.assertEqual(local["expr"]["kind"], "Literal")
        self.assertIs(local["expr"].get("signed"), True)
        label = module["processes"][0]["value"]["index"]
        self.assertEqual([n.get("signed") for n in find(label, lambda n: n.get("kind") == "Literal")],
                         [True])
        # A value position is unchanged: no `signed` on its literal.
        value = module["processes"][1]["value"]
        self.assertEqual([n.get("signed") for n in find(value, lambda n: n.get("kind") == "Literal")],
                         [None])

    def test_unsigned_literal_stays_unmarked(self):
        module = self.extract(
            "module top #(parameter logic [2:0] K = 3'd5) (input logic [15:0] v,"
            " output logic [1:0] o); assign o = v[K + 3'd4 +: 2]; endmodule")
        lits = find(module["processes"][0], lambda n: n.get("kind") == "Literal")
        self.assertTrue(lits)
        self.assertTrue(all("signed" not in n for n in lits))


if __name__ == "__main__":
    unittest.main()
