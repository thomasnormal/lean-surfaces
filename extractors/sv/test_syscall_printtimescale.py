"""The no-argument `$printtimescale` task is an inert diagnostic."""

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


class PrintTimescaleTask(unittest.TestCase):
    def test_no_argument_printtimescale_is_inert(self):
        design = lower('module top; initial $printtimescale; endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_non_scope_printtimescale_stays_loud(self):
        design = lower('module top; initial $printtimescale(1); endmodule')
        kinds = [node.get("sv_kind") for node in nodes(design)]
        self.assertTrue(any(kind in ("ExpressionStatement:CallExpression",
                                     "InvalidStatement") for kind in kinds))

    def test_unit_and_root_scopes_are_inert(self):
        design = lower(
            'module top; initial begin $printtimescale($unit); '
            '$printtimescale($root); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
