"""Declaration-only literal queues are inert; dynamic values remain loud."""

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


class QueueDeclarations(unittest.TestCase):
    def test_uninitialized_2state_queue_is_empty(self):
        design = lower(
            'module top; bit values[$]; initial $display("PASS"); endmodule')
        self.assertFalse(any(node.get("sv_kind") == "VariableSymbol:2state"
                             for node in nodes(design)))
        self.assertFalse(any(node.get("kind") == "Var" and
                             node.get("name") == "values" for node in nodes(design)))

    def test_literal_initialized_queue_is_metadata(self):
        design = lower(
            "module top; bit values[$] = '{1, 2}; initial $finish; endmodule")
        self.assertFalse(any(node.get("sv_kind") == "VariableSymbol:2state"
                             for node in nodes(design)))
        self.assertFalse(any(node.get("kind") == "Var" and
                             node.get("name") == "values" for node in nodes(design)))

    def test_empty_queue_initializers_are_inert(self):
        for initializer in ("{}", "'{}"):
            design = lower(
                f"module top; bit values[$] = {initializer}; "
                'initial $display("PASS"); endmodule')
            self.assertFalse(any(node.get("sv_kind") == "VariableSymbol:2state"
                                 for node in nodes(design)))
            self.assertFalse(any(node.get("kind") == "Var" and
                                 node.get("name") == "values"
                                 for node in nodes(design)))

    def test_4state_queue_stays_loud(self):
        design = lower(
            'module top; logic values[$]; initial $finish; endmodule')
        self.assertIn("VariableSymbol:type",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_module_mailbox_new_initializer_is_metadata(self):
        design = lower(
            'module top; mailbox mbx = new(); int value, result; '
            'initial begin mbx.put(7); result = mbx.try_get(value); '
            'if (result > 0 && value == 7) $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "VariableSymbol:2state"
                             for node in nodes(design)))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
