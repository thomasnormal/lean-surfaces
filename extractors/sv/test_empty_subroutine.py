"""Empty zero-argument subroutine calls are inert statement nodes."""

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


class EmptySubroutineCalls(unittest.TestCase):
    def test_empty_task_and_function_call(self):
        design = lower(
            'module top; task automatic noop(); endtask '
            'function void done(); endfunction '
            'initial begin noop(); done(); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))
        self.assertEqual([], design["modules"][0]["others"])

    def test_nonempty_subroutine_stays_loud(self):
        design = lower(
            'module top; task automatic noisy(); $display("NO"); endtask '
            'initial noisy(); endmodule')
        self.assertIn("SubroutineSymbol:Subroutine",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_argumented_empty_subroutine_stays_loud(self):
        design = lower(
            'module top; task automatic noop(input logic x); endtask '
            'initial begin noop(1\'b0); end endmodule')
        self.assertIn("SubroutineSymbol:Subroutine",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
