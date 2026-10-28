"""Symbolic sv-0.2 admission for integral 2-state declarations."""

import unittest

from test_division import symbolic


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


class SymbolicTwoState(unittest.TestCase):
    def test_bit_ports_and_squash_boundary_are_admitted(self):
        design = symbolic(
            "module divider(input bit a, output bit y); assign y = a; endmodule"
        )
        module = design["modules"][0]
        self.assertTrue(all(port.get("two_state") for port in module["ports"]))
        value = module["processes"][0]["value"]
        self.assertEqual(value["kind"], "Squash2")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in walk(design)))

    def test_bit_variable_and_named_value_are_admitted(self):
        design = symbolic(
            "module divider; bit a; logic b; assign a = b; endmodule"
        )
        module = design["modules"][0]
        self.assertTrue(module["decls"][0]["two_state"])
        self.assertEqual(module["processes"][0]["value"]["kind"], "Squash2")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in walk(design)))

    def test_signed_bit_scalar_and_packed_declarations_are_admitted(self):
        design = symbolic(
            "module divider #(parameter W = 4) ("
            "input bit signed [W-1:0] a, "
            "output bit signed [W-1:0] y); "
            "assign y = a; endmodule"
        )
        module = design["modules"][0]
        self.assertTrue(all(port.get("signed") and port.get("two_state")
                            for port in module["ports"]))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in walk(design)))

    def test_signed_four_state_declarations_remain_loud(self):
        design = symbolic(
            "module divider(input logic signed [3:0] a, "
            "output logic signed [3:0] y); assign y = a; endmodule"
        )
        self.assertTrue(any(node.get("sv_kind") == "PortSymbol:signed"
                            for node in walk(design)))


if __name__ == "__main__":
    unittest.main()
