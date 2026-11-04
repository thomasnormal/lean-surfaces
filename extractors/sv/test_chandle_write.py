"""Direct null writes to opaque chandle storage are inert."""

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


class ChandleWrites(unittest.TestCase):
    def test_direct_null_write_is_inert(self):
        design = lower(
            'module top; chandle handle; initial begin handle = null; '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("opaque_handle_null_write")
                            for node in nodes(design)))

    def test_nonblocking_null_write_stays_loud(self):
        design = lower(
            'module top; chandle handle; initial begin handle <= null; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_virtual_interface_null_write_is_inert(self):
        design = lower(
            'interface Bus; logic ready; endinterface '
            'module top; virtual Bus handle = null; initial begin '
            'handle = null; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("opaque_handle_null_write")
                            for node in nodes(design)))

    def test_event_null_write_is_inert(self):
        design = lower(
            'module top; event handle; initial begin handle = null; '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("opaque_handle_null_write")
                            for node in nodes(design)))

    def test_process_self_write_is_inert(self):
        design = lower(
            'module top; process handle; initial begin handle = process::self(); '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("opaque_process_self_write")
                            for node in nodes(design)))

    def test_nonblocking_process_self_write_stays_loud(self):
        design = lower(
            'module top; process handle; initial begin handle = process::self(); '
            'handle <= process::self(); end endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
