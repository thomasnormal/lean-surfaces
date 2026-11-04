"""Mailbox ``num()`` is exact before and after linear FIFO activity."""

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


class MailboxNumLifetime(unittest.TestCase):
    def test_num_before_first_put_is_zero(self):
        design = lower(
            """module top;
               initial begin
                 mailbox mbx;
                 int cnt0, cnt1;
                 mbx = new();
                 cnt0 = mbx.num();
                 mbx.put(10);
                 cnt1 = mbx.num();
                 if (cnt0 == 0 && cnt1 == 1) $display("PASS");
               end
               endmodule""")
        unsupported = [node for node in nodes(design)
                       if node.get("kind") == "Unsupported"]
        self.assertFalse(unsupported, unsupported)
        nums = [node for node in nodes(design)
                if node.get("mailbox_literal_num")]
        self.assertEqual([node["bits"] for node in nums],
                         ["0" * 32, "0" * 31 + "1"])

    def test_num_without_constructor_stays_loud(self):
        design = lower(
            """module top;
               initial begin
                 mailbox mbx;
                 int count;
                 count = mbx.num();
               end
               endmodule""")
        self.assertIn("CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

