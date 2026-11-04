"""Discarded delete calls on source-pure empty aggregate storage."""
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic


class EmptyAggregateDelete(unittest.TestCase):
    def test_empty_queue_and_uninitialized_dynamic_delete_are_inert(self):
        design = lower(
            "module top; int q[$] = {}; int d[]; initial begin "
            "q.delete(); d.delete(); "
            "if (q.size() == 0 && d.size() == 0) $display(\"PASS\"); "
            "end endmodule")
        self.assertEqual(
            [node.get("empty_aggregate_delete_statement") for node in nodes(design)
             if node.get("empty_aggregate_delete_statement")],
            [True, True],
        )
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_initialized_or_mutated_storage_stays_loud(self):
        sources = (
            "module top; int q[$] = {1}; initial q.delete(); endmodule",
            "module top; int d[] = new[2]; initial d.delete(); endmodule",
            "module top; int q[$] = {}; initial begin q.delete(); "
            "q.push_back(1); end endmodule",
        )
        for source in sources:
            with self.subTest(source=source):
                design = lower(source, require_valid=False)
                self.assertTrue(any(node.get("sv_kind") ==
                                    "ExpressionStatement:CallExpression"
                                    for node in nodes(design)))

    def test_effectful_delete_argument_and_symbolic_mode_stay_loud(self):
        design = lower(
            "module top; int q[$] = {}; int index; initial "
            "q.delete(index++); endmodule", require_valid=False)
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))
        symbolic_design = symbolic(
            "module divider; int q[$] = {}; initial q.delete(); endmodule")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(symbolic_design)))


if __name__ == "__main__":
    unittest.main()
