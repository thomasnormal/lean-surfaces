"""Discarded delete calls on untouched associative arrays."""
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic


class EmptyAssociativeDelete(unittest.TestCase):
    def test_pure_key_and_whole_array_deletes_are_inert(self):
        design = lower(
            "module top; int by_name[string]; int by_number[int]; "
            "initial begin by_name.delete(\"missing\"); by_name.delete(); "
            "by_number.delete(7); if (by_name.num() == 0 && "
            "by_name.size() == 0 && by_number.num() == 0) $display(\"PASS\"); "
            "end endmodule")
        self.assertEqual(
            [node.get("associative_empty_delete_statement") for node in nodes(design)
             if node.get("associative_empty_delete_statement")],
            [True, True, True],
        )
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_initialized_mutated_effectful_and_four_state_forms_stay_loud(self):
        sources = (
            "module top; int a[int]; initial begin a[1] = 2; "
            "a.delete(1); end endmodule",
            "module top; int a[int]; int key; initial a.delete(key++); endmodule",
            "module top; logic [3:0] a[int]; initial a.delete(1); endmodule",
        )
        for source in sources:
            with self.subTest(source=source):
                design = lower(source, require_valid=False)
                self.assertTrue(any(node.get("sv_kind") ==
                                    "ExpressionStatement:CallExpression"
                                    for node in nodes(design)))

    def test_symbolic_mode_stays_loud(self):
        design = symbolic(
            "module divider; int a[int]; initial a.delete(1); endmodule")
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
