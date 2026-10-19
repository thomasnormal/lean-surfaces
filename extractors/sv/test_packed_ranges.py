"""Whole-vector operations over one-dimensional noncanonical packed ranges."""
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


class PackedRanges(unittest.TestCase):
    def test_whole_ascending_vector_is_admitted(self):
        design = extract_source(
            "module top; logic [0:7] value; "
            "initial begin value = 8'hA5; "
            "if (value === 8'hA5) $display(\"PASS\"); end endmodule")
        kinds = [node.get("sv_kind") for node in nodes(design)]
        self.assertNotIn("VariableSymbol:range", kinds)
        decls = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertEqual([(decl["name"], decl["width"]) for decl in decls],
                         [("value", 8)])

    def test_selected_ascending_vector_remains_loud(self):
        design = extract_source(
            "module top; logic [0:7] value; integer index; "
            "initial value[index] = 1'b1; endmodule")
        kinds = [node.get("sv_kind") for node in nodes(design)]
        self.assertIn("AssignmentExpression:target", kinds)


if __name__ == "__main__":
    unittest.main()
