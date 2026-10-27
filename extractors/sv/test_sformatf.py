"""Literal integral `$sformatf` expressions use the packed-string slice."""

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


class SFormatfCalls(unittest.TestCase):
    def test_literal_integral_formats_include_uppercase_aliases(self):
        design = lower(
            'module top; logic [7:0] v = 8\'hAB; '
            'initial if ($sformatf("%H", v) == $sformatf("%h", v) && '
            '$sformatf("%D", v) == $sformatf("%d", v) && '
            '$sformatf("%O", v) == $sformatf("%o", v) && '
            '$sformatf("%B", v) == $sformatf("%b", v)) '
            '$display("PASS"); endmodule')
        formatted = [node for node in nodes(design)
                     if node.get("kind") == "SFormatF"]
        self.assertEqual(len(formatted), 8)
        self.assertEqual({node["format"] for node in formatted},
                         {"%H", "%h", "%D", "%d", "%O", "%o", "%B", "%b"})
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_dynamic_format_stays_loud(self):
        design = lower(
            'module top; string fmt; logic [7:0] v; '
            'initial if ($sformatf(fmt, v) == "ab") $display("PASS"); '
            'endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_real_operand_stays_loud(self):
        design = lower(
            'module top; real value; '
            'initial if ($sformatf("%d", value) == "0") $display("PASS"); '
            'endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression:$sformatf:operand"
                            for node in nodes(design)))

    def test_unsupported_conversion_stays_loud(self):
        design = lower(
            'module top; logic [7:0] v; '
            'initial if ($sformatf("%q", v) == "ab") $display("PASS"); '
            'endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
