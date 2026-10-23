"""VCD setup calls are inert outside the self-check observable state."""

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


class VcdTasks(unittest.TestCase):
    def test_literal_dumpfile_and_scoped_dumpvars_are_inert(self):
        design = lower(
            'module top; logic a; initial begin $dumpfile("x.vcd"); '
            '$dumpvars(0, top); $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_dumpfile_dynamic_argument_stays_loud(self):
        design = lower(
            'module top; string path; initial $dumpfile(path); endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
