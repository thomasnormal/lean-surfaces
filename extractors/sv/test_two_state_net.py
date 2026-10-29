"""Admission checks for two-state data on ordinary wires."""

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


class TwoStateNet(unittest.TestCase):
    def test_un_driven_wire_bit_preserves_floating_net_state(self):
        module = lower(
            "module top; wire bit floating; wire bit [3:0] bus; "
            "endmodule")["modules"][0]
        self.assertEqual(
            [(decl["name"], decl["width"], decl["two_state"])
             for decl in module["decls"]],
            [("floating", 1, True), ("bus", 4, True)])
        self.assertFalse(any(node.get("sv_kind") == "NetSymbol:2state"
                             for node in nodes(module)))

    def test_four_state_driver_is_squashed_at_wire_boundary(self):
        module = lower(
            "module top; wire bit driven; assign driven = 1'bx; "
            "endmodule")["modules"][0]
        assignment = module["processes"][0]["body"]
        self.assertEqual(assignment["value"]["kind"], "Squash2")
        self.assertEqual(assignment["value"]["operand"]["bits"], "x")


class DefaultDisplayFormat(unittest.TestCase):
    def test_integral_arguments_use_decimal_defaults(self):
        module = lower(
            "module top; bit [7:0] value = 8'haf; "
            "initial begin $display(value); $write(value); $display; end "
            "endmodule")["modules"][0]
        calls = module["processes"][0]["body"]["stmts"]
        self.assertEqual(calls[0]["kind"], "SysCall")
        self.assertEqual(calls[0]["format"], "%d")
        self.assertTrue(calls[0]["default_format"])
        self.assertEqual(calls[1]["format"], "%d")
        self.assertEqual(calls[2]["format"], None)

    def test_source_pure_string_uses_character_default(self):
        module = lower(
            'module top; string text; initial begin text = "hello"; '
            "$display(text); end endmodule")["modules"][0]
        call = module["processes"][0]["body"]["stmts"][1]
        self.assertEqual(call["kind"], "SysCall")
        self.assertEqual(call["format"], "%s")
        self.assertTrue(call["args"][0]["string_source_default_display"])

    def test_unpacked_value_without_format_stays_loud(self):
        module = lower(
            "module top; string text; initial begin $display(text); end "
            "endmodule")["modules"][0]
        self.assertTrue(any(node.get("sv_kind") == "SysCall:format"
                            for node in nodes(module)))


if __name__ == "__main__":
    unittest.main()
