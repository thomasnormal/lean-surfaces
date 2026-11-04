"""Literal-only IEEE coverage query calls in the empty coverage database."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def extract_source(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()
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


class CoverageCalls(unittest.TestCase):
    def test_literal_queries_lower_to_zero(self):
        design = extract_source(
            'module top; int a, b, c, d, e; initial begin '
            'a = $coverage_control(3, 23, 11, "top"); '
            'b = $coverage_get(22, 11, "top"); '
            'c = $coverage_get_max(22, 11, "top"); '
            'd = $coverage_merge(23, "db"); '
            'e = $coverage_save(23, "db"); end endmodule')
        literals = [node for node in nodes(design)
                    if node.get("kind") == "Literal"
                    and node.get("coverage_nocov")]
        self.assertEqual(len(literals), 5)
        self.assertEqual({(node["width"], node["bits"])
                          for node in literals}, {(32, "0" * 32)})
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_discarded_literal_query_is_inert(self):
        design = extract_source(
            'module top; initial begin '
            '$coverage_merge(23, "db"); $coverage_save(23, "db"); '
            'end endmodule')
        statements = list(nodes(design))
        self.assertEqual(
            [node.get("coverage_nocov_statement") for node in statements
             if node.get("kind") == "Empty"],
            [True, True])

    def test_dynamic_argument_stays_loud(self):
        design = extract_source(
            'module top; int scope, rc; initial '
            'rc = $coverage_get(22, 11, scope); endmodule')
        self.assertIn("InvalidStatement",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_coverage_construct_stays_loud(self):
        design = extract_source(
            'module top; int value, rc; '
            'covergroup cg; coverpoint value; endgroup '
            'initial rc = $coverage_get(22, 11, "top"); endmodule')
        self.assertIn("CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
