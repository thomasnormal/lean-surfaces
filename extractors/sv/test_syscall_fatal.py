"""Pure literal `$fatal` reuses the existing whole-run halt."""

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


class FatalTask(unittest.TestCase):
    def test_literal_fatal_lowers_to_finish(self):
        design = lower(
            'module top; initial $fatal(0, "done"); endmodule')
        calls = [node for node in nodes(design) if node.get("kind") == "SysCall"]
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]["name"], "$finish")
        self.assertTrue(calls[0]["fatal_task"])

    def test_dynamic_pure_fatal_arguments_are_evaluated(self):
        design = lower(
            'module top; logic [3:0] x; initial $fatal(1, "x=%0d", x); endmodule')
        calls = [node for node in nodes(design) if node.get("kind") == "SysCall"]
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]["name"], "$finish")
        self.assertTrue(calls[0]["fatal_task"])
        self.assertEqual(len(calls[0]["args"]), 3)

    def test_effectful_fatal_argument_stays_loud(self):
        design = lower(
            'module top; function int f(); return 1; endfunction '
            'initial $fatal(1, "x=%0d", f()); endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
