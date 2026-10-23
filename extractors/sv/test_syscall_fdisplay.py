"""`$fdisplay` admits only the predefined standard-output descriptor."""

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


class FDisplay(unittest.TestCase):
    def test_predefined_stdout_is_display(self):
        design = lower(
            "module top; initial $fdisplay(32'h8000_0001, \"PASS\"); endmodule")
        calls = [node for node in nodes(design) if node.get("kind") == "SysCall"]
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]["name"], "$display")
        self.assertEqual(calls[0]["stdout_file_descriptor"], 0x80000001)

    def test_non_stdout_descriptor_stays_loud(self):
        design = lower(
            "module top; initial $fdisplay(32'h8000_0002, \"x\"); endmodule")
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
