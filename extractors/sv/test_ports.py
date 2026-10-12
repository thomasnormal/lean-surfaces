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
