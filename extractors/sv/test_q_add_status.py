"""Source-pure ``$q_add`` scalar status results."""

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


class QAddStatus(unittest.TestCase):
    def test_successful_literal_add_publishes_zero(self):
        design = lower(
            """module top;
               integer status;
               initial begin
                 $q_initialize(5, 1, 10, status);
                 $q_add(5, 1, 100, status);
               end
               endmodule""")
        self.assertEqual(
            [node["q_add_status_lowered"] for node in nodes(design)
             if node.get("q_add_status_lowered") is not None], [0])

    def test_full_queue_publishes_one_after_capacity(self):
        design = lower(
            """module top;
               integer status;
               initial begin
                 $q_initialize(5, 1, 2, status);
                 $q_add(5, 1, 0, status);
                 $q_add(5, 2, 0, status);
                 $q_add(5, 3, 0, status);
               end
               endmodule""")
        self.assertEqual(
            [node["q_add_status_lowered"] for node in nodes(design)
             if node.get("q_add_status_lowered") is not None], [0, 0, 1])

    def test_named_queue_id_from_prior_literal_is_admitted(self):
        design = lower(
            """module top;
               integer q_id, status;
               initial begin
                 q_id = 5;
                 $q_initialize(q_id, 1, 2, status);
                 $q_add(q_id, 1, 0, status);
               end
               endmodule""")
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))
        self.assertEqual(
            [node["q_add_status_lowered"] for node in nodes(design)
             if node.get("q_add_status_lowered") is not None], [0])

    def test_unassigned_symbolic_queue_id_remains_loud(self):
        design = lower(
            """module top;
               integer q_id, status;
               initial begin
                 $q_initialize(q_id, 1, 2, status);
                 $q_add(q_id, 1, 0, status);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_payload_expression_remains_loud(self):
        design = lower(
            """module top;
               integer status, job;
               initial begin
                 $q_initialize(5, 1, 2, status);
                 $q_add(5, job, 0, status);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
