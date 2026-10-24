"""Uninitialized procedural floating declarations carry no self-check state."""

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


class FloatingLocalDeclarations(unittest.TestCase):
    def test_uninitialized_real_is_inert(self):
        design = lower(
            'module top; initial begin real unused; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "VariableSymbol:2state"
                             for node in nodes(design)))

    def test_initialized_real_stays_loud(self):
        design = lower(
            'module top; initial begin real value = 1.0; $display("PASS"); end endmodule')
        self.assertIn("VariableSymbol:2state",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_literal_blocking_write_is_inert(self):
        design = lower(
            'module top; real value; initial begin value = -3.5; '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("floating_literal_write_noop")
                            for node in nodes(design)))

    def test_nonliteral_write_stays_loud(self):
        design = lower(
            'module top; real value; real source; '
            'initial begin value = source; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_pure_math_call_write_is_inert(self):
        design = lower(
            'module top; real value; initial begin value = $sqrt(16.0); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("floating_pure_call_write_noop")
                            for node in nodes(design)))

    def test_effectful_math_operand_stays_loud(self):
        design = lower(
            'module top; real value; int index; initial begin '
            'value = $sqrt(index++); end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_time_zero_realtime_write_is_inert(self):
        design = lower(
            'module top; real value; initial begin value = $realtime; '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("realtime_write_noop")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_nonblocking_realtime_write_stays_loud(self):
        design = lower(
            'module top; real value; initial begin value <= $realtime; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
