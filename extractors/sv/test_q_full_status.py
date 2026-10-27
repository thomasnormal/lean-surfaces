"""Source-pure ``$q_full`` scalar status results."""

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


class QFullStatus(unittest.TestCase):
    def test_not_full_query_publishes_zero(self):
        design = lower(
            """module top;
               integer status, full;
               initial begin
                 $q_initialize(3, 1, 5, status);
                 $q_add(3, 1, 100, status);
                 $q_full(3, status);
                 full = status;
               end
               endmodule""")
        self.assertEqual(
            [node["q_full_status_lowered"] for node in nodes(design)
             if node.get("q_full_status_lowered") is not None], [0])

    def test_full_query_counts_literal_adds(self):
        design = lower(
            """module top;
               integer status, full;
               initial begin
                 $q_initialize(2, 1, 2, status);
                 $q_add(2, 10, 0, status);
                 $q_add(2, 20, 0, status);
                 $q_full(2, status);
                 full = status;
               end
               endmodule""")
        self.assertEqual(
            [node["q_full_status_lowered"] for node in nodes(design)
             if node.get("q_full_status_lowered") is not None], [1])

    def test_value_position_query_is_source_pure(self):
        design = lower(
            """module top;
               integer status, full;
               initial begin
                 $q_initialize(2, 1, 2, status);
                 full = $q_full(2, status);
               end
               endmodule""")
        values = [node.get("value", {}).get("q_full_value")
                  for node in nodes(design)
                  if node.get("kind") == "BlockingAssign"]
        self.assertIn(0, values)

    def test_dynamic_id_remains_loud(self):
        design = lower(
            """module top;
               integer q_id, status;
               initial begin
                 q_id = 2;
                 $q_initialize(q_id, 1, 2, status);
                 $q_full(q_id, status);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
