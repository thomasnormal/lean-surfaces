"""Literal string initialization of fixed unpacked byte arrays."""
import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def lower(source):
    extract._SYM = None
    extract._SOURCE_BYTES = source.encode()
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class FixedArrayStringInitializer(unittest.TestCase):
    def test_ascii_string_samples_declared_byte_order_and_zero_pads(self):
        design = lower(
            'module top; byte text[3:0] = "hi2"; '
            'initial begin if (text[3] != "h") $finish; '
            'if (text[2] != "i") $finish; if (text[1] != "2") $finish; '
            'if (text[0] != 0) $finish; $display("PASS"); end endmodule')
        declarations = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertEqual([node["name"] for node in declarations],
                         ["text[3]", "text[2]", "text[1]", "text[0]"])
        self.assertEqual([node["init"]["operand"]["bits"] for node in declarations],
                         ["01101000", "01101001", "00110010", "00000000"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_non_ascii_string_initializer_stays_loud(self):
        design = lower('module top; byte text[1:0] = "hé"; '
                       'initial begin end endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "VariableSymbol:2state"
                            for node in nodes(design)))

    def test_non_byte_fixed_array_string_initializer_stays_loud(self):
        design = lower('module top; bit [3:0] text[1:0] = "ab"; '
                       'initial begin end endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "VariableSymbol:2state"
                            for node in nodes(design)))

    def test_fixed_string_array_elements_drive_loops_and_display(self):
        design = lower(
            'module top; string text[4] = ' +
            "'{\"111\", \"222\", \"333\", \"444\"}; "
            'int i; initial begin while (text[i] != "222") i++; '
            'if (text[i] == "222") $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("fixed_string_array_dynamic")
                            for node in nodes(design)))

    def test_fixed_string_array_writes_stay_loud(self):
        design = lower(
            'module top; string text[2] = ' +
            "'{\"a\", \"b\"}; initial text[0] = \"c\"; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "VariableSymbol:2state"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
