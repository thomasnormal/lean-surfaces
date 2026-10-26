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


class ContinuousBoundLiteral(unittest.TestCase):
    def test_declaration_literal_driver_is_lowered(self):
        design = lower(
            'module top; logic source = 1\'b1; wire driven; '
            'assign driven = source; initial $display("PASS"); endmodule')
        self.assertTrue(any(node.get("continuous_constant_lowered")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_procedural_rebind_stays_loud(self):
        design = lower(
            'module top; logic source = 1\'b1; wire driven; '
            'assign driven = source; initial source = 1\'b0; endmodule')
        self.assertFalse(any(node.get("continuous_constant_lowered")
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
