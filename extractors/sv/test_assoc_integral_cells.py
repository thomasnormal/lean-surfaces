"""Finite literal integral-key associative arrays use flat scalar cells."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def extract_source(source):
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


class AssocIntegralCells(unittest.TestCase):
    def test_literal_bound_key_is_admitted(self):
        design = extract_source(
            'module top; initial begin int score[int]; '
            'int key = 7; score[key] = 15; '
            'if (score[key] == 15) $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_rebound_key_stays_loud(self):
        design = extract_source(
            'module top; initial begin int score[int]; '
            'int key = 7; key = 8; score[key] = 15; '
            'end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_literal_keys_flatten_static_cells_and_reads(self):
        design = extract_source(
            'module top; initial begin logic [7:0] score[int]; '
            'score[-1] = 8\'h5a; score[2] = 8\'hA5; '
            'if (score[-1] === 8\'h5a && score[2] === 8\'hA5) '
            '$display("PASS"); end endmodule')
        module = design["modules"][0]
        self.assertEqual([decl["kind"] for decl in module["decls"]],
                         ["Var", "Var", "Var", "Var"])
        self.assertEqual(sum(decl.get("assoc_presence", False)
                             for decl in module["decls"]), 2)
        names = [decl["name"] for decl in module["decls"]]
        self.assertTrue(any("[int:-1]" in name for name in names))
        self.assertTrue(any("[int:2]" in name for name in names))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             and node.get("sv_kind") == "AssignmentExpression:target"
                             for node in module["processes"]))

    def test_dynamic_key_stays_loud(self):
        design = extract_source(
            'module top; initial begin int score[int]; int key; '
            'key = 1; score[key] = 95; end endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in design["modules"][0]["processes"][0]["body"]["stmts"]))

    def test_whole_array_use_stays_loud(self):
        design = extract_source(
            'module top; initial begin int score[int]; '
            'score = score; end endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in design["modules"][0]["processes"][0]["body"]["stmts"]))


if __name__ == "__main__":
    unittest.main()
