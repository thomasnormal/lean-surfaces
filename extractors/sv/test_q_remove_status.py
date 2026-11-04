"""State-free queue-removal status results."""

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


class QRemoveStatus(unittest.TestCase):
    def test_fifo_payload_is_lowered_to_scalar_outputs(self):
        design = lower(
            """module top;
               integer status, job, info;
               initial begin
                 $q_initialize(2, 1, 10, status);
                 $q_add(2, 42, 99, status);
                 $q_remove(2, job, info, status);
                 if (status === 0 && job === 42 && info === 99)
                   $display("PASS");
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("q_remove_payload_lowered")]
        self.assertEqual(len(lowered), 1)
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_lifo_payload_uses_last_added_entry(self):
        design = lower(
            """module top;
               integer status, job, info;
               initial begin
                 $q_initialize(2, 2, 10, status);
                 $q_add(2, 10, 100, status);
                 $q_add(2, 20, 200, status);
                 $q_remove(2, job, info, status);
                 if (status === 0 && job === 20 && info === 200)
                   $display("PASS");
               end
               endmodule""")
        blocks = [node for node in nodes(design)
                  if node.get("q_remove_payload_lowered")]
        self.assertEqual(len(blocks), 1)
        values = [node.get("q_remove_job")
                  for node in nodes(blocks[0])
                  if node.get("q_remove_job") is not None]
        self.assertEqual(values, [20])

    def test_undefined_id_publishes_status_two(self):
        design = lower(
            """module top;
               integer status, job, info;
               initial begin
                 $q_remove(999, job, info, status);
                 if (status === 2) $display("PASS");
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("q_remove_status_lowered") is not None]
        self.assertEqual([node["q_remove_status_lowered"] for node in lowered], [2])

    def test_empty_initialized_queue_publishes_status_three(self):
        design = lower(
            """module top;
               integer q_id, status, job, info;
               initial begin
                 q_id = 1;
                 $q_initialize(q_id, 1, 10, status);
                 $q_remove(q_id, job, info, status);
                 if (status === 3) $display("PASS");
               end
               endmodule""")
        lowered = [node for node in nodes(design)
                   if node.get("q_remove_status_lowered") is not None]
        self.assertEqual([node["q_remove_status_lowered"] for node in lowered], [3])

    def test_observed_payload_remains_loud(self):
        design = lower(
            """module top;
               integer status, job, info;
               initial begin
                 $q_remove(999, job, info, status);
                 if (job === 0) $display("PASS");
               end
               endmodule""")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
