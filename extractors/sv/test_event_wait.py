"""Simple nested posedge waits for the retained scheduler tier."""

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


def first_body(source):
    return lower(source)["modules"][0]["processes"][0]["body"]


class EventWait(unittest.TestCase):
    def test_posedge_wait_is_retained(self):
        body = first_body(
            'module e; logic clk; initial begin @(posedge clk); $finish; end endmodule'
        )
        self.assertEqual(body["stmts"][0], {
            "kind": "WaitEvent",
            "span": body["stmts"][0]["span"],
            "signal": "clk",
            "edge": "posedge",
        })

    def test_posedge_wait_body_is_retained_after_checkpoint(self):
        body = first_body(
            'module e; logic clk; initial @(posedge clk) $finish; endmodule'
        )
        self.assertEqual(body["kind"], "Block")
        self.assertEqual(body["stmts"][0]["kind"], "WaitEvent")
        self.assertEqual(body["stmts"][1]["name"], "$finish")

    def test_negedge_wait_is_retained(self):
        body = first_body(
            'module e; logic clk; initial begin @(negedge clk); $finish; end endmodule'
        )
        self.assertEqual(body["stmts"][0]["kind"], "WaitEvent")
        self.assertEqual(body["stmts"][0]["edge"], "negedge")

    def test_negedge_wait_body_is_retained_after_checkpoint(self):
        body = first_body(
            'module e; logic clk; initial @(negedge clk) $finish; endmodule'
        )
        self.assertEqual(body["kind"], "Block")
        self.assertEqual(body["stmts"][0]["edge"], "negedge")
        self.assertEqual(body["stmts"][1]["name"], "$finish")

    def test_any_edge_wait_is_retained(self):
        body = first_body(
            'module e; logic clk; initial begin @(clk); $finish; end endmodule'
        )
        self.assertEqual(body["stmts"][0]["kind"], "WaitEvent")
        self.assertEqual(body["stmts"][0]["edge"], "any")

    def test_other_event_controls_remain_loud(self):
        for source in (
            'module e; logic a,b; initial begin @(posedge a or posedge b); $finish; end endmodule',
        ):
            with self.subTest(source=source):
                self.assertTrue(any(
                    node.get("kind") == "Unsupported"
                    for node in _nodes(lower(source))
                ))

def _nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from _nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from _nodes(child)
