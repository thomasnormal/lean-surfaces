"""Constant procedural delay admission for the retained scheduler tier."""

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


def first_statement(source):
    design = lower(source)
    return design["modules"][0]["processes"][0]["body"]["stmts"][0]


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class ProceduralDelay(unittest.TestCase):
    def test_constant_delay_is_a_scheduler_node(self):
        stmt = first_statement(
            'module d; initial begin #3; $finish; end endmodule')
        self.assertEqual(stmt["kind"], "Delay")
        self.assertEqual(stmt["amount"], 3)

    def test_zero_delay_remains_represented_for_runtime_refusal(self):
        stmt = first_statement(
            'module d; initial begin #0; $finish; end endmodule')
        self.assertEqual(stmt, {
            "kind": "Delay",
            "span": stmt["span"],
            "amount": 0,
            "body": stmt["body"],
        })

    def test_delayed_body_is_retained(self):
        stmt = first_statement(
            'module d; initial begin #3 $finish; end endmodule')
        self.assertEqual(stmt["kind"], "Delay")
        self.assertEqual(stmt["body"]["name"], "$finish")

    def test_dynamic_delay_stays_loud(self):
        dynamic = lower(
            'module d; integer n; initial begin #n; $finish; end endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(dynamic)))

    def test_ambiguous_conversions_stay_loud(self):
        for expression in ("(1+2)", "(-1)", "3.2", "3ns", "4'hx", "65'd18446744073709551616"):
            with self.subTest(expression=expression):
                design = lower(
                    'module d; initial begin #' + expression + '; end endmodule')
                self.assertTrue(any(node.get("kind") == "Unsupported"
                                    for node in nodes(design)))
