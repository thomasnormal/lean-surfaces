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
    def test_finite_literal_for_loops_replay_fifo_history(self):
        design = lower(
            """module top;
               mailbox #(int) box = new();
               int value, result, ok = 1;
               initial begin
                 for (int i = 0; i < 4; i++) begin
                   value = i * 3;
                   box.put(value);
                 end
                 for (int i = 0; i < 4; i++) begin
                   box.get(result);
                   if (result != i * 3) ok = 0;
                 end
               end
               endmodule""")
        self.assertTrue(any(node.get("mailbox_literal_loop_lowered")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_dynamic_mailbox_loop_bounds_stay_loud(self):
        design = lower(
            """module top;
               mailbox box;
               int n, value;
               initial begin
                 box = new();
                 for (int i = 0; i < n; i++) box.put(i);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

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

