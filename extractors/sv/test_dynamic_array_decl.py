"""Declaration-only 2-state dynamic arrays are inert."""

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


class DynamicArrayDeclarations(unittest.TestCase):
    def test_uninitialized_2state_dynamic_array_is_inert(self):
        design = lower(
            'module top; bit values[]; initial $display("PASS"); endmodule')
        self.assertFalse(any(node.get("sv_kind") == "VariableSymbol:2state"
                             for node in nodes(design)))

    def test_initialized_dynamic_array_stays_loud(self):
        design = lower(
            "module top; bit values[] = '{1, 2}; initial $finish; endmodule")
        self.assertIn("VariableSymbol:2state",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_4state_dynamic_array_stays_loud(self):
        design = lower(
            'module top; logic values[]; initial $finish; endmodule')
        self.assertIn("VariableSymbol:type",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
