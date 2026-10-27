"""Source-pure ``$q_exam`` queue length statistics."""

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


class QExamStatus(unittest.TestCase):
    def test_current_length_writes_statistic_then_status(self):
        design = lower(
            """module top;
               integer status, stat_value;
               initial begin
                 $q_initialize(1, 1, 10, status);
                 $q_add(1, 10, 0, status);
                 $q_add(1, 20, 0, status);
                 $q_exam(1, 1, stat_value, status);
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("q_exam_stat_value_lowered") is not None]
        self.assertEqual([node["q_exam_stat_value_lowered"] for node in lowered], [2])
        statuses = [node["q_exam_status_lowered"] for node in nodes(design)
                    if node.get("q_exam_status_lowered") is not None]
        self.assertEqual(statuses, [0])

    def test_max_length_uses_successful_adds(self):
        design = lower(
            """module top;
               integer status, max_value;
               initial begin
                 $q_initialize(2, 1, 2, status);
                 $q_add(2, 10, 0, status);
                 $q_add(2, 20, 0, status);
                 $q_exam(2, 3, max_value, status);
               end
               endmodule""")
        values = [node["q_exam_stat_value_lowered"] for node in nodes(design)
                  if node.get("q_exam_stat_value_lowered") is not None]
        self.assertEqual(values, [2])

    def test_adds_beyond_capacity_are_clamped(self):
        design = lower(
            """module top;
               integer status, stat_value;
               initial begin
                 $q_initialize(3, 1, 1, status);
                 $q_add(3, 10, 0, status);
                 $q_add(3, 20, 0, status);
                 $q_exam(3, 1, stat_value, status);
               end
               endmodule""")
        values = [node["q_exam_stat_value_lowered"] for node in nodes(design)
                  if node.get("q_exam_stat_value_lowered") is not None]
        self.assertEqual(values, [1])

    def test_removed_history_remains_loud(self):
        design = lower(
            """module top;
               integer status, stat_value, job, info;
               initial begin
                 $q_initialize(4, 1, 10, status);
                 $q_add(4, 1, 0, status);
                 $q_remove(4, job, info, status);
                 $q_exam(4, 1, stat_value, status);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_symbolic_id_and_other_statistic_remain_loud(self):
        design = lower(
            """module top;
               integer q_id, status, stat_value;
               initial begin
                 q_id = 4;
                 $q_initialize(q_id, 1, 10, status);
                 $q_exam(q_id, 6, stat_value, status);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))

    def test_named_id_and_payload_history_are_admitted(self):
        design = lower(
            """module top;
               integer q_id, job_id, inform_id, stat_code, stat_value;
               initial begin
                 q_id = 1;
                 $q_initialize(q_id, 1, 10, stat_code);
                 job_id = 42;
                 inform_id = 0;
                 $q_add(q_id, job_id, inform_id, stat_code);
                 $q_exam(q_id, 1, stat_value, stat_code);
                 $q_exam(q_id, 3, stat_value, stat_code);
               end
               endmodule""")
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))
        self.assertEqual(
            [node["q_exam_stat_value_lowered"] for node in nodes(design)
             if node.get("q_exam_stat_value_lowered") is not None], [1, 1])

    def test_reassigned_named_id_remains_loud(self):
        design = lower(
            """module top;
               integer q_id, status, stat_value;
               initial begin
                 q_id = 1;
                 q_id = q_id + 1;
                 $q_initialize(q_id, 1, 10, status);
                 $q_exam(q_id, 1, stat_value, status);
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
