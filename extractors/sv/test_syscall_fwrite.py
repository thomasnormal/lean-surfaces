"""`$fwrite` maps to the existing stdout `$write` state."""

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


class FWrite(unittest.TestCase):
    def test_predefined_stdout_is_write_without_newline(self):
        design = lower(
            'module top; initial begin '
            '$fwrite(32\'h8000_0001, "PASS"); $display(""); end endmodule')
        calls = [node for node in nodes(design) if node.get("kind") == "SysCall"]
        self.assertEqual([node["name"] for node in calls], ["$write", "$display"])
        self.assertEqual(calls[0]["stdout_file_descriptor"], 0x80000001)

    def test_non_stdout_descriptor_stays_loud(self):
        design = lower(
            'module top; initial $fwrite(32\'h8000_0002, "x"); endmodule')
        self.assertTrue(any(node.get("sv_kind") ==
                            "ExpressionStatement:CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
