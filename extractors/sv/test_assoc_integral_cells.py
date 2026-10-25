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


class AssocIntegralCells(unittest.TestCase):
    def test_literal_keys_flatten_static_cells_and_reads(self):
        design = extract_source(
            'module top; initial begin logic [7:0] score[int]; '
            'score[-1] = 8\'h5a; score[2] = 8\'hA5; '
            'if (score[-1] === 8\'h5a && score[2] === 8\'hA5) '
            '$display("PASS"); end endmodule')
        module = design["modules"][0]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var", "Var"])
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
