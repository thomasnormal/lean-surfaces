"""Mailbox FIFO snapshots may replay one pure literal scalar write."""

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


class VariableMailbox(unittest.TestCase):
    def test_pure_literal_scalar_write_can_feed_put(self):
        design = lower(
            """module top;
               mailbox box;
               int value, result;
               initial begin
                 box = new();
                 value = 100;
                 box.put(value);
                 box.get(result);
                 if (result == 100) $display("PASS");
               end
               endmodule""")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        gets = [node for node in nodes(design)
                if node.get("mailbox_literal_get")]
        self.assertEqual(len(gets), 1)
        self.assertEqual(gets[0]["value"]["bits"], "0" * 24 + "01100100")

    def test_control_dependent_scalar_write_stays_loud(self):
        design = lower(
            """module top;
               mailbox box;
               int value, result;
               initial begin
                 box = new();
                 if (1) value = 100;
                 box.put(value);
                 box.get(result);
               end
               endmodule""")
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_nonliteral_reassignment_stays_loud(self):
        design = lower(
            """module top;
               mailbox box;
               int value, result;
               initial begin
                 box = new();
                 value = 100;
                 value = result;
                 box.put(value);
                 box.get(result);
               end
               endmodule""")
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

