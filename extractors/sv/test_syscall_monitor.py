"""Monitor toggles are inert when no monitor is registered."""

import unittest

import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


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


class MonitorControls(unittest.TestCase):
    def test_no_argument_toggles_without_registration_are_inert(self):
        design = lower(
            'module top; initial begin $monitoroff; $monitoron(); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))
        self.assertEqual(
            [node.get("pure_diagnostic") for node in nodes(design)
             if node.get("kind") == "Empty"],
            ["$monitoroff", "$monitoron"],
        )

    def test_registration_and_arguments_stay_loud(self):
        for source in (
            'module top; initial begin $monitor("x=%0d", 1); $monitoroff; end endmodule',
            'module top; initial $monitoron(1); endmodule',
        ):
            with self.subTest(source=source):
                design = lower(source)
                self.assertTrue(any(node.get("sv_kind") in (
                                    "ExpressionStatement:CallExpression",
                                    "InvalidStatement")
                                    for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
