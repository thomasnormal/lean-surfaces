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

    def test_parameterized_packed_try_fifo_updates_output_argument(self):
        design = lower(
            """module top;
               initial begin
                 mailbox #(bit [7:0]) mbx;
                 bit [7:0] got;
                 int ok;
                 mbx = new();
                 ok = mbx.try_put(8'ha5);
                 ok = mbx.try_get(got);
                 if (ok > 0 && got === 8'ha5 && mbx.num() == 0)
                   $display("PASS");
               end
               endmodule""")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        blocks = [node for node in nodes(design)
                  if node.get("mailbox_literal_try_get_assignment")]
        self.assertEqual(len(blocks), 1)
        stores = blocks[0]["stmts"]
        self.assertEqual([store["target"]["name"] for store in stores],
                         ["got", "ok"])
        self.assertEqual(stores[0]["value"]["bits"], "10100101")
        self.assertTrue(any(node.get("mailbox_literal_num")
                            for node in nodes(design)))

    def test_parameterized_packed_try_width_mismatch_stays_loud(self):
        for source in (
                """module top; mailbox #(bit [7:0]) mbx; int ok;
                   initial begin mbx = new(); ok = mbx.try_put(16'ha5); end
                   endmodule""",
                """module top; mailbox #(bit [7:0]) mbx; bit [15:0] got; int ok;
                   initial begin mbx = new(); mbx.try_put(8'ha5);
                   ok = mbx.try_get(got); end endmodule"""):
            design = lower(source)
            self.assertTrue(any(node.get("kind") == "Unsupported"
                                for node in nodes(design)))

    def test_parameterized_packed_try_dynamic_and_other_methods_stay_loud(self):
        for source in (
                """module top; mailbox #(bit [7:0]) mbx; bit [7:0] value;
                   initial begin mbx = new(); mbx.try_put(value); end
                   endmodule""",
                """module top; mailbox #(bit [7:0]) mbx; bit [7:0] value;
                   initial begin mbx = new(); mbx.try_put(8'ha5);
                   mbx.peek(value); end endmodule"""):
            design = lower(source)
            self.assertTrue(any(node.get("kind") == "Unsupported"
                                for node in nodes(design)))

