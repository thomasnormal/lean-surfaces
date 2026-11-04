"""Invalid packed-dimension declarations are inert compile-time metadata."""

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


class InvalidPackedDimensionDeclarations(unittest.TestCase):
    def test_invalid_packed_dimensions_are_empty_declarations(self):
        design = lower(
            'module top; bit [3:x] bad_range; bit [3] bad_single; '
            'initial $display("PASS"); endmodule')
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertFalse(any(node.get("kind") == "Var"
                             and node.get("name") in ("bad_range", "bad_single")
                             for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") == "VariableSymbol:2state"
                             for node in nodes(design)))

    def test_valid_two_state_dimension_remains_a_variable(self):
        design = lower(
            'module top; bit [3:0] value; initial value = 4\'h1; endmodule')
        self.assertFalse(any(node.get("invalid_packed_dimension_decl")
                             for node in nodes(design)))
        self.assertTrue(any(node.get("kind") == "Var"
                            and node.get("name") == "value"
                            for node in nodes(design)))

    def test_literal_initializer_is_also_inert_after_rejection(self):
        design = lower(
            'module top; bit [3:x] bad_range = 1\'b0; endmodule')
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_effectful_initializer_is_not_erased(self):
        design = lower(
            'module top; bit [3:x] bad_range = f(); '
            'function bit f(); return 1\'b0; endfunction endmodule')
        self.assertTrue(any(node.get("sv_kind") == "VariableSymbol:2state"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
