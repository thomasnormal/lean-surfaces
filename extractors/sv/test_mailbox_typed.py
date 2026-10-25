"""Parameterized mailbox handles reuse the scalar FIFO lowering."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def lower(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class TypedMailbox(unittest.TestCase):
    def test_typed_mailbox_local_constructor_is_metadata(self):
        design = lower(
            """module top;
               initial begin
                 mailbox #(int) mbx = new();
                 int value;
                 mbx.put(42);
                 mbx.get(value);
                 if (value == 42) $display("PASS");
               end
               endmodule""")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("mailbox_literal_put")
                            for node in nodes(design)))
        self.assertTrue(any(node.get("mailbox_literal_get")
                            for node in nodes(design)))

    def test_typed_mailbox_nonempty_constructor_stays_loud(self):
        design = lower(
            """module top;
               initial begin
                 mailbox #(int) mbx = new(2);
                 $display("PASS");
               end
               endmodule""")
        self.assertIn("VariableSymbol:2state",
                      [node.get("sv_kind") for node in nodes(design)])

