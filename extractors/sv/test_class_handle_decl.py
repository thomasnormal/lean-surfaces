"""Uninitialized class handles are opaque declaration metadata."""

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


class ClassHandleDeclarations(unittest.TestCase):
    def test_uninitialized_mailbox_declarations_are_inert(self):
        design = lower(
            'module top; mailbox module_box; '
            'initial begin mailbox local_box; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "VariableSymbol:2state"
                             for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") == "VariableDeclStatement:2state"
                             for node in nodes(design)))

    def test_initialized_handle_stays_loud(self):
        design = lower(
            'module top; mailbox box = new(); '
            'initial $display("PASS"); endmodule')
        self.assertIn("VariableSymbol:2state",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_class_handle_read_stays_loud(self):
        design = lower(
            'module top; mailbox box; initial begin '
            'if (box == null) $display("PASS"); end endmodule')
        self.assertIn("NamedValueExpression:2state",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
