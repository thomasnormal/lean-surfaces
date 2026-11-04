"""VCD control tasks remain outside the self-check observable state."""

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


class VcdControlTasks(unittest.TestCase):
    def test_vcd_control_tasks_are_inert(self):
        design = lower(
            'module top; initial begin $dumpon; $dumpoff; $dumpall; '
            '$dumpflush; $dumplimit(1024); $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_dumpportsflush_is_inert(self):
        design = lower(
            'module top; initial begin $dumpportsflush(); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_dumpportsflush_arguments_stay_loud(self):
        design = lower(
            'module top; initial $dumpportsflush("x"); endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_dynamic_dump_limit_stays_loud(self):
        design = lower(
            'module top; int n; initial $dumplimit(n); endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
