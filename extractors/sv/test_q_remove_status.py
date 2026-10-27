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
