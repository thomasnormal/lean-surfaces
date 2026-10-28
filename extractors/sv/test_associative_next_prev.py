"""Finite integral associative-array next / prev history."""
import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def lower(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


class AssociativeNextPrev(unittest.TestCase):
    def test_next_and_prev_replay_literal_keys(self):
        design = lower("""module top;
  int values[int]; int key; int result;
  initial begin
    values[1] = 10; values[3] = 30; values[5] = 50;
    key = 1; result = values.next(key); result = values.prev(key);
  end
endmodule""")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in walk(design)))

    def test_dynamic_next_key_stays_loud(self):
        design = lower("""module top;
  int values[int]; int key; int result;
  initial begin
    values[key] = 10; result = values.next(key);
  end
endmodule""")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") ==
                            "AssignmentExpression:target"
                            for node in walk(design)))


if __name__ == "__main__":
    unittest.main()
