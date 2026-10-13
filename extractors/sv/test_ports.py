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

    def test_two_state_input_port_remains_loud(self):
        design = lower(
            'module e(input bit a); initial begin if (a == 1\'b0) $finish; end endmodule'
        )
        self.assertTrue(any(
            node.get("sv_kind") == "PortSymbol:2state" for node in nodes(design)
        ))

    def test_two_state_net_output_remains_loud(self):
        design = lower(
            'module e(output wire bit a); initial begin $finish; end endmodule'
        )
        self.assertTrue(any(
            node.get("sv_kind") == "PortSymbol:2state" for node in nodes(design)
        ))
