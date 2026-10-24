"""Tests for the aliased flat-cell unpacked-union target boundary."""
import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def extract_source(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()
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


class UnpackedUnionMembers(unittest.TestCase):
    def test_equal_width_members_alias_one_cell(self):
        design = extract_source(
            "module top; typedef union { logic [7:0] a; logic [7:0] b; } u_t; "
            "u_t value; initial begin value.a = 8'hA5; "
            "if (value.b === 8'hA5) $display(\"PASS\"); end endmodule")
        declarations = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertEqual([node["name"] for node in declarations], ["value"])
        assigns = [node for node in nodes(design) if node.get("kind") == "BlockingAssign"]
        self.assertEqual(assigns[0]["target"]["name"], "value")
        self.assertEqual(assigns[0]["value"]["bits"], "10100101")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_whole_copy_reuses_the_aliased_cell(self):
        design = extract_source(
            "module top; typedef union { logic [7:0] a; logic [7:0] b; } u_t; "
            "u_t source; u_t copy; initial begin source.a = 8'hA5; copy = source; "
            "if (copy.b === 8'hA5) $display(\"PASS\"); end endmodule")
        copies = [node for node in nodes(design)
                  if node.get("unpacked_union_whole_copy_lowered")]
        self.assertEqual(len(copies), 1)
        self.assertEqual(copies[0]["target"]["name"], "copy")
        self.assertEqual(copies[0]["value"]["name"], "source")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_nonblocking_whole_copy_stays_loud(self):
        design = extract_source(
            "module top; typedef union { logic [7:0] a; logic [7:0] b; } u_t; "
            "u_t source; u_t copy; initial copy <= source; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_whole_values_support_case_equality(self):
        design = extract_source(
            "module top; typedef union { logic [7:0] a; logic [7:0] b; } u_t; "
            "u_t left; u_t right; initial begin left.a = 8'hA5; right.b = 8'hA5; "
            "if (left === right) $display(\"PASS\"); end endmodule")
        comparisons = [node for node in nodes(design)
                       if node.get("kind") == "Binary" and node.get("op") == "==="]
        self.assertEqual(len(comparisons), 1)
        self.assertEqual(comparisons[0]["left"]["name"], "left")
        self.assertEqual(comparisons[0]["right"]["name"], "right")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_whole_union_arithmetic_stays_loud(self):
        design = extract_source(
            "module top; typedef union { logic [7:0] a; logic [7:0] b; } u_t; "
            "u_t left; u_t right; initial begin if (left + right == 0) "
            "$display(\"PASS\"); else $display(\"FAIL\"); end endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_local_union_uses_flat_cell(self):
        design = extract_source(
            "module top; initial begin typedef union { bit [3:0] a; bit [3:0] b; } u_t; "
            "u_t value; value.b = 4'hc; if (value.a == 4'hc) $display(\"PASS\"); "
            "end endmodule")
        declarations = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertTrue(any(node.get("unpacked_union_cell") for node in declarations))
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_mixed_width_union_stays_loud(self):
        design = extract_source(
            "module top; typedef union { logic [7:0] a; logic [3:0] b; } u_t; "
            "u_t value; initial value.a = 8'hA5; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "VariableSymbol:type"
                            for node in nodes(design)))

    def test_nested_union_member_stays_loud(self):
        design = extract_source(
            "module top; typedef struct { logic [7:0] x; } s_t; "
            "typedef union { s_t a; s_t b; } u_t; u_t value; "
            "initial value.a.x = 8'hA5; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "VariableSymbol:type"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
