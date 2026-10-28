"""Declaration-order numeric enum methods, preserving source admission."""
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=EnumNumericMethods | origin=spec | authority=IEEE-1800-2023#6.19.5 | map=lowering:exact-member-case-equality-and-declaration-order;step:frontend-unsigned-two-state-conversion;refusals:effects-before-folding


DECL = "typedef enum logic [3:0] {A=3, B=7, C=1} E; E value, result; integer count;"


def source(expression, declarations=DECL, target="result"):
    return "module top; " + declarations + " initial " + target + " = " + expression + "; endmodule"


def methods(design):
    return [n for n in nodes(design) if n.get("enum_method_lowered")]


class EnumNumericMethods(unittest.TestCase):
    def clean(self, text):
        design = lower(text)
        self.assertTrue(methods(design))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))
        return design

    def test_endpoints_follow_declaration_order_and_width(self):
        for name, bits in (("first", "0011"), ("last", "0001")):
            root, = methods(self.clean(source("value." + name + "()")))
            self.assertEqual((root["kind"], root["width"], root["bits"]), ("Literal", 4, bits))

    def test_num_keeps_32_bit_signed_result(self):
        root, = methods(self.clean(source("value.num()", target="count")))
        self.assertEqual((root["width"], root["signed"], int(root["bits"], 2)), (32, True, 3))

    def test_default_step_is_exact_case_lookup(self):
        for name in ("next", "prev"):
            root, = methods(self.clean(source("value." + name + "()")))
            self.assertEqual(root["kind"], "Ternary")
            self.assertEqual(root["cond"]["op"], "===")
            self.assertEqual(root["cond"]["left"]["name"], "value")
            self.assertEqual(root["cond"]["right"]["bits"], "0011")
            self.assertEqual(root["then"]["bits"], "0111" if name == "next" else "0001")
            self.assertEqual(root["else"]["else"]["else"]["bits"], "xxxx")

    def test_two_state_nonmember_default_is_zero(self):
        root, = methods(self.clean(source("value.next(0)", DECL.replace("logic", "bit"))))
        # A converted constant may retain a Squash2 wrapper, so inspect the outer lookup only.
        self.assertEqual(root["else"]["else"]["else"]["bits"], "0000")

    def test_dynamic_count_retains_conversion_and_unsigned_remainder(self):
        design = self.clean(source("value.next(count)"))
        remainder = next(n for n in nodes(design) if n.get("op") == "u%")
        self.assertEqual(remainder["width"], 32)
        self.assertEqual(remainder["left"]["kind"], "Squash2")
        self.assertEqual(remainder["left"]["operand"]["name"], "count")
        self.assertEqual(int(remainder["right"]["bits"], 2), 3)

    def test_named_xz_values_are_not_wildcards(self):
        text = source("value.next()", "typedef enum logic [2:0] {A=3'bx10, B=3'bz01} E; E value, result;")
        root, = methods(self.clean(text))
        self.assertEqual(root["cond"]["op"], "===")
        self.assertEqual(root["cond"]["right"]["bits"], "x10")
        self.assertEqual(root["then"]["bits"], "z01")

    def test_packed_field_and_fixed_array_receivers_reuse_reads(self):
        field = source("packet.value.next()", DECL + " typedef struct packed {E value; logic valid;} P; P packet;")
        root, = methods(self.clean(field))
        self.assertEqual(root["cond"]["left"]["kind"], "SelectRead")
        cell = source("cells[1].prev()", DECL + " E cells[0:1];")
        root, = methods(self.clean(cell))
        self.assertEqual(root["cond"]["left"]["name"], "cells[1]")

    def test_defaulted_parentheses_and_generated_members(self):
        for call in ("value.next", "value.prev", "value.num"):
            self.clean(source(call, "typedef enum {A[3], Z} E; E value, result; integer count;",
                              target="count" if call.endswith("num") else "result"))

    def test_signed_result_context_keeps_enum_signedness(self):
        design = self.clean(source("value.first()", "typedef enum logic signed [3:0] {A=-3,B=7} E; E value; logic signed [63:0] result;"))
        root, = methods(design)
        self.assertTrue(root["signed"])
        self.assertTrue(any(n.get("kind") == "SignedResize" for n in nodes(design)))

    def test_effects_cannot_hide_behind_constant_endpoints_or_casts(self):
        declarations = DECL + " function E f(); count++; return A; endfunction"
        for call in ("f().first()", "f().num()", "value.next(count++)", "64'(f().first())"):
            design = lower(source(call, declarations, target="result" if call in ("f().first()", "value.next(count++)") else "count"))
            self.assertFalse(methods(design))
            self.assertTrue(any(n.get("sv_kind") == "EnumMethod:source" for n in nodes(design)))

    def test_name_comparison_survives_constant_conversion(self):
        for call in ('64\'(A.name() == "A")', '64\'(value.name() == "A")'):
            design = lower(source(call, target="count"))
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))
        design = symbolic("module divider; " + DECL + " initial count=64'(value.num()); endmodule")
        self.assertFalse(methods(design))
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_name_in_display_is_a_string_value(self):
        design = lower(
            "module top; " + DECL
            + ' initial $display("%s", value.name()); endmodule')
        names = [n for n in nodes(design) if n.get("enum_name_lowered")]
        self.assertEqual(len(names), 1)
        self.assertEqual(names[0]["kind"], "EnumName")
        self.assertEqual([case["name"] for case in names[0]["cases"]], ["A", "B", "C"])
        self.assertEqual(names[0]["default"], "")

    def test_discarded_name_statement_reuses_enum_lowering(self):
        design = lower(
            "module top; " + DECL
            + " initial begin value = B; value.name(); $display(\"PASS\"); "
              "$finish; end endmodule")
        statements = [node for node in nodes(design)
                      if node.get("enum_name_statement")]
        self.assertEqual(len(statements), 1)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_discarded_numeric_statements_reuse_enum_lowering(self):
        design = lower(
            "module top; " + DECL
            + " initial begin value = B; value.first(); value.last(); "
              "value.num(); value.next(); value.prev(); $display(\"PASS\"); "
              "$finish; end endmodule")
        statements = [node for node in nodes(design)
                      if node.get("enum_numeric_statement")]
        self.assertEqual([node["enum_numeric_statement"] for node in statements],
                         ["first", "last", "num", "next", "prev"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_frontend_error_is_a_design_barrier(self):
        design = lower(source("value.first()", DECL + " int bad=missing;"), require_valid=False)
        self.assertTrue(any(n.get("sv_kind") == "EnumMethod:invalid-compilation" for n in nodes(design)))


if __name__ == "__main__":
    unittest.main()
