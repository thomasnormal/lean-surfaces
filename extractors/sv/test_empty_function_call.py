"""Empty zero-argument functions produce their declared default value."""

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


class EmptyFunctionCalls(unittest.TestCase):
    def test_two_state_default_is_zero(self):
        design = lower(
            'module top; function bit [3:0] zero(); endfunction '
            'initial begin if (zero() == 4\'b0000) $display("PASS"); '
            'end endmodule')
        self.assertTrue(any(node.get("empty_function_default")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_four_state_default_is_unknown(self):
        design = lower(
            'module top; function logic [3:0] unknown(); endfunction '
            'initial begin if (unknown() === 4\'bxxxx) $display("PASS"); '
            'end endmodule')
        self.assertTrue(any(node.get("empty_function_default")
                            and set(node.get("bits", "")) == {"x"}
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
