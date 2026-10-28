"""Finite literal associative arrays stream in ascending key order."""
import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def convert(source):
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


class StreamingAssociativeSorted(unittest.TestCase):
    def test_integral_keys_are_packed_in_sorted_order(self):
        design = convert("""module top;
  int values[int];
  bit [95:0] stream;
  initial begin
    values[3] = 32'hc;
    values[1] = 32'ha;
    values[2] = 32'hb;
    stream = {>> {values}};
  end
endmodule""")
        unsupported = [node for node in walk(design)
                       if node.get("kind") == "Unsupported"]
        self.assertFalse(unsupported)
        assigns = [node for node in walk(design)
                   if node.get("kind") == "BlockingAssign"
                   and node.get("target", {}).get("name") == "stream"]
        self.assertEqual(len(assigns), 1)
        self.assertEqual(
            [part["name"].rsplit("values", 1)[-1]
             for part in assigns[0]["value"]["operand"]["parts"]],
            ["[int:1]", "[int:2]", "[int:3]"])

    def test_dynamic_key_history_stays_loud(self):
        design = convert("""module top;
  int values[int];
  int key;
  bit [63:0] stream;
  initial begin
    values[key] = 1;
    stream = {>> {values}};
  end
endmodule""")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") ==
                            "AssignmentExpression:target"
                            for node in walk(design)))


if __name__ == "__main__":
    unittest.main()
