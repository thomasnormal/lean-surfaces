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

    def test_literal_semaphore_try_get_tracks_remaining_keys(self):
        design = lower(
            'module top; semaphore sem; int first, second, failed; '
            'initial begin sem = new(3); first = sem.try_get(2); '
            'second = sem.try_get(1); failed = sem.try_get(1); '
            'if (first > 0 && second > 0 && failed == 0) $display("PASS"); '
            'else $display("FAIL"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("semaphore_literal_try_get")]
        self.assertEqual([node["semaphore_available"] for node in values], [3, 1, 0])
        self.assertEqual([node["semaphore_request"] for node in values], [2, 1, 1])
        self.assertEqual([node["bits"] for node in values],
                         ["0" * 31 + "1", "0" * 31 + "1", "0" * 32])
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_literal_semaphore_try_get_default_is_one(self):
        design = lower(
            'module top; semaphore sem = new(1); int result; '
            'initial begin result = sem.try_get(); '
            'if (result > 0 && sem.try_get(1) == 0) $display("PASS"); '
            'else $display("FAIL"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("semaphore_literal_try_get")]
        self.assertEqual(len(values), 2)
        self.assertEqual([node["semaphore_request"] for node in values], [1, 1])
        self.assertEqual([node["bits"] for node in values],
                         ["0" * 31 + "1", "0" * 32])

    def test_literal_semaphore_default_constructor_has_zero_keys(self):
        design = lower(
            'module top; semaphore sem; int result; initial begin '
            'sem = new(); result = sem.try_get(1); '
            'if (result == 0) $display("PASS"); else $display("FAIL"); '
            'end endmodule')
        values = [node for node in nodes(design)
                  if node.get("semaphore_literal_try_get")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["semaphore_available"], 0)
        self.assertEqual(values[0]["bits"], "0" * 32)

    def test_dynamic_or_mixed_semaphore_try_get_stays_loud(self):
        design = lower(
            'module top; semaphore sem; int keys, result; initial begin '
            'sem = new(2); result = sem.try_get(keys); sem.put(1); end endmodule')
        self.assertIn("CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_literal_semaphore_put_and_get_balance(self):
        design = lower(
            'module top; semaphore sem; bit done; initial begin '
            'sem = new(1); sem.put(2); sem.get(3); done = 1; '
            'if (done) $display("PASS"); end endmodule')
        methods = [node for node in nodes(design)
                   if node.get("semaphore_literal_method")]
        self.assertEqual([node["semaphore_literal_method"] for node in methods],
                         ["put", "get"])
        self.assertFalse(any(node.get("sv_kind") ==
                             "ExpressionStatement:CallExpression"
                             for node in nodes(design)))

    def test_literal_semaphore_get_that_would_block_stays_loud(self):
        design = lower(
            'module top; semaphore sem; initial begin '
            'sem = new(1); sem.get(2); end endmodule')
        self.assertIn("ExpressionStatement:CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

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

    def test_empty_mailbox_try_get_and_peek_return_zero(self):
        design = lower(
            'module top; mailbox box; int value, get_result, peek_result; '
            'initial begin box = new(); get_result = box.try_get(value); '
            'peek_result = box.try_peek(value); '
            'if (get_result == 0 && peek_result == 0) $display("PASS"); '
            'else $display("FAIL"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("mailbox_empty_try")]
        self.assertEqual([node["mailbox_empty_try"] for node in values],
                         ["try_get", "try_peek"])
        self.assertEqual([node["bits"] for node in values], ["0" * 32] * 2)
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_untriggered_and_null_events_report_triggered_false(self):
        design = lower(
            'module top; event a; event b; int first, second; initial begin '
            'b = null; first = a.triggered(); second = b.triggered(); '
            'if (first === 0 && second === 0) $display("PASS"); '
            'else $display("FAIL"); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("event_triggered_false")]
        self.assertEqual(len(values), 2)
        self.assertTrue(all(node["bits"] == "0" for node in values))

    def test_triggered_event_stays_loud(self):
        design = lower(
            'module top; event e; int result; initial begin -> e; '
            'result = e.triggered(); end endmodule')
        self.assertTrue(any(str(node.get("sv_kind", "")).startswith("CallExpression")
                            for node in nodes(design)))

    def test_mailbox_num_after_literal_put_is_exact(self):
        design = lower(
            'module top; mailbox box; int result; initial begin '
            'box = new(); box.put(1); result = box.num(); end endmodule')
        values = [node for node in nodes(design)
                  if node.get("mailbox_literal_num")]
        self.assertEqual(len(values), 1)
        self.assertEqual(values[0]["bits"], "0" * 31 + "1")
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

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
