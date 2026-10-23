"""Pure severity diagnostics are erased; effectful tasks stay loud."""

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


class QuietSeverityTasks(unittest.TestCase):
    def test_literal_info_and_warning_are_empty(self):
        design = lower(
            'module top; initial begin $info("i"); $warning("w"); end endmodule')
        self.assertEqual(
            [node["kind"] for node in nodes(design) if node.get("kind") == "Empty"],
            ["Empty", "Empty"],
        )
        self.assertFalse(any(node.get("sv_kind") == "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_dynamic_argument_stays_loud(self):
        design = lower(
            'module top; logic [3:0] x; initial $info("x=%0d", x); endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_error_and_fatal_stay_loud(self):
        design = lower(
            'module top; initial begin $error("e"); $fatal(1, "f"); end endmodule')
        kinds = [node.get("sv_kind") for node in nodes(design)]
        self.assertEqual(kinds.count("ExpressionStatement:CallExpression"), 0)


if __name__ == "__main__":
    unittest.main()
