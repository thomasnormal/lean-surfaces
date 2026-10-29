"""Admission checks for no-format severity-task arguments."""

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


class SeverityDefaultFormat(unittest.TestCase):
    def test_integral_and_source_string_defaults(self):
        module = lower(
            'module top; string text; initial begin text = "hello"; '
            '$info(7); $warning(text); $error(9, text); end endmodule'
        )["modules"][0]
        calls = [node for node in nodes(module) if node.get("kind") == "SysCall"]
        self.assertEqual([call["name"] for call in calls],
                         ["$info", "$warning", "$error"])
        self.assertEqual([call["format"] for call in calls],
                         ["%d", "%s", "%d%s"])
        self.assertTrue(all(call.get("default_format") for call in calls))
        self.assertEqual(len(calls[-1]["args"]), 2)

    def test_opaque_argument_stays_loud(self):
        module = lower(
            "module top; real value; initial begin $info(value); end endmodule"
        )["modules"][0]
        self.assertTrue(any(
            node.get("sv_kind") == "ExpressionStatement:CallExpression"
            for node in nodes(module)))


if __name__ == "__main__":
    unittest.main()
