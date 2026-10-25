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

    def test_direct_null_write_is_inert(self):
        design = lower(
            'module top; mailbox box; initial begin box = null; '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("opaque_handle_null_write")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_nonblocking_null_write_stays_loud(self):
        design = lower(
            'module top; mailbox box; initial begin box <= null; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_bare_mailbox_construction_write_is_opaque(self):
        design = lower(
            'module top; mailbox box; initial begin box = new(); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("opaque_mailbox_new_write")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_explicit_zero_constructor_argument_stays_loud(self):
        design = lower(
            'module top; mailbox box; initial begin box = new(0); end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_zero_key_semaphore_construction_write_is_opaque(self):
        design = lower(
            'module top; semaphore sem; initial begin sem = new(0); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("opaque_semaphore_zero_write")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_literal_semaphore_constructor_is_opaque(self):
        design = lower(
            'module top; semaphore sem; initial begin sem = new(1); '
            '$display("PASS"); end endmodule')
        self.assertTrue(any(node.get("opaque_semaphore_literal_new_write")
                            for node in nodes(design)))
        self.assertFalse(any(node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_dynamic_semaphore_constructor_stays_loud(self):
        design = lower(
            'module top; semaphore sem; integer keys; '
            'initial begin sem = new(keys); end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_zero_key_semaphore_methods_are_inert_after_construction(self):
        design = lower(
            'module top; semaphore sem; initial begin '
            'sem = new(0); sem.put(0); sem.get(0); $display("PASS"); '
            'end endmodule')
        zero_methods = [node for node in nodes(design)
                        if node.get("semaphore_zero_method")]
        self.assertEqual([node["semaphore_zero_method"] for node in zero_methods],
                         ["put", "get"])
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_zero_key_semaphore_try_get_returns_success(self):
        design = lower(
            'module top; semaphore sem; int result; initial begin '
            'sem = new(1); result = sem.try_get(0); '
            'if (result > 0) $display("PASS"); else $display("FAIL"); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("semaphore_zero_try_get")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "0" * 31 + "1")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_empty_mailbox_num_returns_zero_after_construction(self):
        design = lower(
            'module top; mailbox box; int result; initial begin '
            'box = new(); result = box.num(); '
            'if (result === 0) $display("PASS"); else $display("FAIL"); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("mailbox_empty_num")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "0" * 32)
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_mailbox_num_after_put_stays_loud(self):
        design = lower(
            'module top; mailbox box; int result; initial begin '
            'box = new(); box.put(1); result = box.num(); end endmodule')
        self.assertIn("CallExpression", [node.get("sv_kind") for node in nodes(design)])

    def test_mailbox_num_before_construction_stays_loud(self):
        design = lower(
            'module top; mailbox box; int result; initial begin '
            'result = box.num(); box = new(); end endmodule')
        self.assertIn("CallExpression", [node.get("sv_kind") for node in nodes(design)])

    def test_dynamic_semaphore_key_method_stays_loud(self):
        design = lower(
            'module top; semaphore sem; integer keys; initial begin '
            'sem = new(0); sem.put(keys); end endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_uninitialized_semaphore_zero_method_stays_loud(self):
        design = lower(
            'module top; semaphore sem; initial begin '
            'sem.put(0); end endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
