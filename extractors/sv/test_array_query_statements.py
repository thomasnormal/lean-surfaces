"""Discarded pure locator queries are admitted only for flat integral arrays."""
from pathlib import Path
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic


REPO = Path(__file__).resolve().parents[2]


def fixture():
    return lower((REPO / "Examples/system-verilog/array_query_statements/"
                  "array_query_statements.sv").read_text())


def with_fixture():
    return lower((REPO / "Examples/system-verilog/array_query_with_statements/"
                  "array_query_with_statements.sv").read_text())


class ArrayQueryStatements(unittest.TestCase):
    def test_discarded_fixed_integral_queries_are_inert(self):
        design = fixture()
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertEqual(
            [node.get("array_query_statement") for node in nodes(design)
             if node.get("array_query_statement")],
            ["min", "max", "unique", "unique_index",
             "min", "max", "unique", "unique_index"],
        )

    def test_source_pure_with_queries_are_discarded(self):
        design = with_fixture()
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertEqual(
            [node.get("array_query_statement") for node in nodes(design)
             if node.get("array_query_statement")],
            ["min", "max", "unique", "unique_index"],
        )

    def test_dynamic_with_and_aggregate_forms_stay_loud(self):
        sources = (
            'module top; logic [7:0] a[]; initial a.unique(); endmodule',
            'module top; logic [7:0] a[2]; initial a.min with ($urandom()); endmodule',
            'module top; typedef struct packed {logic [7:0] x;} cell_t; '
            'cell_t a[2]; initial a.max(); endmodule',
        )
        for source in sources:
            with self.subTest(source=source):
                design = lower(source, require_valid=False)
                self.assertTrue(any(node.get("sv_kind") ==
                                    "ExpressionStatement:CallExpression"
                                    for node in nodes(design)
                                    if node.get("kind") == "Unsupported"))

    def test_symbolic_mode_stays_loud(self):
        design = symbolic(
            'module divider; logic [7:0] a[2]; '
            'initial begin a.min(); a.unique_index(); end endmodule'
        )
        walls = [node.get("sv_kind") for node in nodes(design)
                 if node.get("kind") == "Unsupported"]
        self.assertGreaterEqual(walls.count("ExpressionStatement:CallExpression"), 2)


if __name__ == "__main__":
    unittest.main()
