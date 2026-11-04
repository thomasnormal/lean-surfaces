"""The pinned negative-literal semaphore ``try_get`` compatibility slice."""

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


class NegativeSemaphoreTryGet(unittest.TestCase):
    def test_negative_try_get_is_normalized_to_one(self):
        design = lower(
            """module top;
               initial begin
                 semaphore sem = new(5);
                 int result;
                 result = sem.try_get(-1);
                 if (result == 1) $display("PASS");
               end
               endmodule""")
        unsupported = [node for node in nodes(design)
                       if node.get("kind") == "Unsupported"]
        self.assertFalse(unsupported, unsupported)
        values = [node for node in nodes(design)
                  if node.get("semaphore_literal_try_get")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["semaphore_request"], 1)
        self.assertTrue(values[0]["semaphore_negative_key_normalized"])

    def test_negative_put_stays_loud(self):
        design = lower(
            """module top;
               initial begin
                 semaphore sem = new(5);
                 sem.put(-1);
               end
               endmodule""")
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

