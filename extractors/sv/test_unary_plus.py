"""Unary-plus identity admission for the legacy/self-check envelope."""

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


class UnaryPlus(unittest.TestCase):
    def test_unary_plus_erases_to_the_operand(self):
        design = lower(
            'module e(input logic [3:0] a, output logic [3:0] b); '
            'assign b = +a; endmodule'
        )
        assignment = design["modules"][0]["processes"][0]
        self.assertEqual(assignment["value"]["kind"], "Ident")
        self.assertEqual(assignment["value"]["name"], "a")
        self.assertFalse(any(
            node.get("sv_kind") == "UnaryExpression:Plus"
            for node in nodes(design)
        ))

    def test_unary_plus_keeps_unknown_operand_values(self):
        design = lower(
            'module e(input logic [3:0] a, output logic [3:0] b); '
            'assign b = +(a); endmodule'
        )
        assignment = design["modules"][0]["processes"][0]
        self.assertEqual(assignment["value"], {
            "kind": "Ident",
            "span": assignment["value"]["span"],
            "width": 4,
            "name": "a",
        })

