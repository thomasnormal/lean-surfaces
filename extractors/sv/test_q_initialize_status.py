"""State-free ``$q_initialize`` status results."""

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


class QInitializeStatus(unittest.TestCase):
    def test_unsupported_type_publishes_status_four(self):
        design = lower(
            """module top;
               integer status;
               initial $q_initialize(20, 99, 10, status);
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("q_initialize_status_lowered") is not None]
        self.assertEqual(len(lowered), 1)
        self.assertEqual(lowered[0]["q_initialize_status_lowered"], 4)
        self.assertEqual(lowered[0]["value"]["bits"],
                         "0" * 29 + "100")

    def test_zero_capacity_publishes_status_five(self):
        design = lower(
            """module top;
               integer status;
               initial $q_initialize(20, 1, 0, status);
               endmodule""")
        self.assertEqual(
            [node["q_initialize_status_lowered"] for node in nodes(design)
             if node.get("q_initialize_status_lowered") is not None], [5])

    def test_valid_sole_creation_publishes_status_zero(self):
        design = lower(
            """module top;
               integer status;
               initial $q_initialize(20, 1, 10, status);
               endmodule""")
        self.assertEqual(
            [node["q_initialize_status_lowered"] for node in nodes(design)
             if node.get("q_initialize_status_lowered") is not None], [0])

    def test_queue_operations_remain_loud(self):
        design = lower(
            """module top;
               integer status;
               initial begin
                 $q_initialize(20, 1, 10, status);
                 $q_add(20, 1, 1, status);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("q_initialize_status_lowered") is not None
                             for node in nodes(design)))

    def test_duplicate_literal_id_publishes_status_six(self):
        design = lower(
            """module top;
               integer q_id, status;
               initial begin
                 q_id = 1;
                 $q_initialize(q_id, 1, 10, status);
                 $q_initialize(q_id, 1, 10, status);
                 if (status === 6) $display("PASS");
                 $finish;
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("q_initialize_status_lowered") is not None]
        self.assertEqual([node["q_initialize_status_lowered"] for node in lowered],
                         [0, 6])

    def test_duplicate_id_requires_valid_first_creation(self):
        design = lower(
            """module top;
               integer status;
               initial begin
                 $q_initialize(1, 99, 10, status);
                 $q_initialize(1, 99, 10, status);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
