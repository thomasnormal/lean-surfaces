"""WP-PROC follow-up 1 (2026-11-01): a drive strength on a continuous assignment is refused loudly in symbolic mode.

`_continuous_assignment_has_strength` reads source bytes that only the M0 path loads, so the symbolic extractor read
`assign (strong0, highz1) y = a;` as a plain assignment. No reading of the text is shared by the tools: Yosys cannot
read a strength on `assign` (syntax error), Verilator calls it unsupported, Icarus applies it (z where a highz term is
driven) and Xcelium ignores it on a variable (CAVSTR). The node is `ContinuousAssignSymbol:strength`, decided from the
syntax tree (`lower_proc.has_strength`); the M0 path keeps its own handling.
"""
import json
import tempfile
import unittest
from pathlib import Path

import extract


def envelope(source, top="t"):
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "f.sv"
        path.write_text(source)
        out = Path(directory) / "out.json"
        extract.process_symbolic(top, [str(path)], [], str(out))
        return json.loads(out.read_text())["design"]


def kinds(node, found=None):
    found = [] if found is None else found
    if isinstance(node, dict):
        if node.get("kind") == "Unsupported":
            found.append(node.get("sv_kind"))
        for value in node.values():
            kinds(value, found)
    elif isinstance(node, list):
        for value in node:
            kinds(value, found)
    return found


class ContinuousStrength(unittest.TestCase):
    def module(self, body, ports="input logic a, output logic y"):
        return envelope("module t (%s); %s endmodule" % (ports, body))["modules"][0]

    def test_strength_on_a_variable_assign_is_refused(self):
        for strength in ("strong0, highz1", "highz0, strong1", "weak0, weak1", "supply0, supply1", "pull1, pull0"):
            m = self.module("assign (%s) y = a;" % strength)
            self.assertEqual(kinds(m), ["ContinuousAssignSymbol:strength"], strength)
            self.assertEqual([p["kind"] for p in m["processes"]], ["Unsupported"], strength)

    def test_the_same_assign_without_strength_is_admitted(self):
        m = self.module("assign y = a;")
        self.assertEqual(kinds(m), [])
        self.assertEqual([p["kind"] for p in m["processes"]], ["Assign"])

    def test_strength_on_a_window_and_in_a_generate_scope(self):
        m = self.module("assign (weak0, weak1) y[0] = a; assign y[1] = ~a;", ports="input logic a, output logic [1:0] y")
        self.assertEqual(kinds(m), ["ContinuousAssignSymbol:strength"])
        m = self.module("for (genvar g = 0; g < 1; g++) begin : gg assign (strong0, highz1) y = a; end")
        self.assertEqual(kinds(m), ["ContinuousAssignSymbol:strength"])

    def test_strength_on_a_net_keeps_both_refusals(self):
        # the assign is refused here, the net declaration by its own rule (net-z: N2 admits no strength either)
        m = self.module("wire w; assign (strong0, highz1) w = a; assign y = w;")
        self.assertIn("ContinuousAssignSymbol:strength", kinds(m))
        self.assertIn("NetSymbol:net-z", kinds(m))
        m = self.module("wire (weak0, weak1) w = a; assign y = w;")
        self.assertIn("NetSymbol:net-z", kinds(m))

    def test_a_delay_is_still_the_delay_refusal(self):
        self.assertEqual(kinds(self.module("assign #1 y = a;")), ["ContinuousAssignSymbol:delay"])


if __name__ == "__main__":
    unittest.main()
