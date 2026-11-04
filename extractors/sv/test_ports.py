"""Port-shape admission for the legacy/self-check envelope."""

import unittest

import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


def lower(source):
    extract._SYM = None
    extract._SOURCE_BYTES = source.encode()
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class Ports(unittest.TestCase):
    def test_signed_four_state_ports_are_admitted_with_metadata(self):
        design = lower(
            'module e(input logic signed [7:0] a, output logic signed [7:0] b); '
            'assign b = a; endmodule'
        )
        ports = design["modules"][0]["ports"]
        self.assertEqual([port.get("signed", False) for port in ports], [True, True])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_signed_relational_operator_keeps_signed_tag(self):
        design = lower(
            'module e(input logic signed [7:0] a, b, output logic lt); '
            'assign lt = a < b; endmodule'
        )
        binary = next(node for node in nodes(design) if node.get("kind") == "Binary")
        self.assertEqual(binary["op"], "s<")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_two_state_output_port_is_admitted(self):
        design = lower(
            'module e(output bit a); initial begin if (a == 1\'b0) $finish; end endmodule'
        )
        port = design["modules"][0]["ports"][0]
        self.assertEqual(port["width"], 1)
        self.assertTrue(port["two_state"])

    def test_signed_two_state_output_port_is_admitted(self):
        design = lower(
            'module e(output bit signed [3:0] a); '
            'initial begin if (a == 4\'b0000) $finish; end endmodule'
        )
        port = design["modules"][0]["ports"][0]
        self.assertEqual(port["width"], 4)
        self.assertTrue(port["two_state"])
        self.assertTrue(port["signed"])

    def test_two_state_input_port_is_admitted(self):
        design = lower(
            'module e(input bit a); initial begin if (a == 1\'b0) $finish; end endmodule'
        )
        port = design["modules"][0]["ports"][0]
        self.assertTrue(port["two_state"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_signed_two_state_input_port_is_admitted(self):
        design = lower(
            'module e(input bit signed [3:0] a); initial $finish; endmodule'
        )
        port = design["modules"][0]["ports"][0]
        self.assertTrue(port["two_state"])
        self.assertTrue(port["signed"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_predefined_integral_variable_ports(self):
        for spelling, width, signed, two_state in [
            ("byte", 8, True, True), ("shortint", 16, True, True),
            ("int", 32, True, True), ("longint", 64, True, True),
            ("integer", 32, True, False), ("time", 64, False, False),
        ]:
            for direction in ("input", "output"):
                with self.subTest(spelling=spelling, direction=direction):
                    design = lower(f"module e({direction} {spelling} value); endmodule")
                    port = design["modules"][0]["ports"][0]
                    self.assertEqual(port["width"], width)
                    self.assertEqual(port.get("signed", False), signed)
                    self.assertEqual(port.get("two_state", False), two_state)
                    self.assertFalse(any(node.get("kind") == "Unsupported"
                                         for node in nodes(design)))

    def test_two_state_net_input_remains_loud(self):
        design = lower("module e(input wire bit a); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "PortSymbol:2state"
                            for node in nodes(design)))

    def test_port_initializers_are_not_dropped(self):
        for declaration in ("input bit value = 1", "output bit value = 1",
                            "input int value = 7", "output integer value = 7"):
            with self.subTest(declaration=declaration):
                design = lower(f"module sample({declaration}); endmodule")
                port = design["modules"][0]["ports"][0]
                self.assertIn("init", port)
                self.assertFalse(any(node.get("kind") == "Unsupported"
                                     for node in nodes(design)))

    def test_output_net_initializer_remains_loud(self):
        design = lower("module sample(output wire value = 1'b1); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "PortSymbol:net-initializer"
                            for node in nodes(design)))

    def test_non_ansi_variable_port_initializer_is_retained(self):
        design = lower("module sample(value); output value; bit value = 1; endmodule")
        port = design["modules"][0]["ports"][0]
        self.assertTrue(port["two_state"])
        self.assertIn("init", port)
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_two_state_net_output_remains_loud(self):
        design = lower(
            'module e(output wire bit a); initial begin $finish; end endmodule'
        )
        self.assertTrue(any(
            node.get("sv_kind") == "PortSymbol:2state" for node in nodes(design)
        ))
