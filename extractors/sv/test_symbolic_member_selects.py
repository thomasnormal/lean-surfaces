"""Constant selects through members of packed structs/unions (WP-E1).

A member that is a MULTI-DIMENSIONAL packed array (`logic [3:0][7:0] bytes`)
has elements wider than one bit, and its labels count elements. The symbolic
lowering used to put a 1-bit window at `member offset + label` (bit units):
`p.bytes[2]` became `PartSel[4:4]` of width 1, `u.h[1]` became `[1:1]`, a
write to `out_v.b[0]` became a 1-bit write, `p.bytes[2:1]` carried width 16
over a 2-bit span, and `hasUnsupported` stayed false. Every window is now
the flat bit range of the selected ELEMENTS, and the select-lowering guard
(`_sym_select_checked`) turns any select whose emitted width/offset
disagrees with the compiler-resolved type into a loud `:window-mismatch`.
"""
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import extract


def sv_kinds(node, found=None):
    found = [] if found is None else found
    if isinstance(node, dict):
        if node.get("kind") == "Unsupported":
            found.append(node.get("sv_kind"))
        for value in node.values():
            sv_kinds(value, found)
    elif isinstance(node, list):
        for value in node:
            sv_kinds(value, found)
    return found


def window(node):
    """(msb, lsb, width, root) of a flat `PartSel` over an `Ident`."""
    assert node["kind"] == "PartSel", node
    assert node["value"]["kind"] == "Ident", node
    return (node["msb"]["value"], node["lsb"]["value"], node["width"],
            node["value"]["name"])


def assigns(module):
    """name -> value expression of every continuous `assign name = expr`."""
    return {p["target"]["name"]: p["value"] for p in module["processes"]
            if p["kind"] == "Assign" and p["target"]["kind"] == "Ident"}


class SymbolicMemberSelects(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    STRUCT = (
        "module top (input logic [33:0] p_i, output logic [7:0] b2,"
        " output logic [3:0] nib, output logic [15:0] r, output logic [7:0] b0,"
        " output logic [1:0] tg);"
        " typedef struct packed { logic [3:0][7:0] bytes; logic [1:0] tag; } pkt_t;"
        " pkt_t p; assign p = p_i;"
        " assign b2 = p.bytes[2]; assign nib = p.bytes[1][3:0];"
        " assign r = p.bytes[2:1]; assign b0 = p.bytes[0]; assign tg = p.tag;"
        " endmodule")

    def test_struct_member_element_and_range_selects(self):
        module = self.extract(self.STRUCT)
        self.assertEqual(sv_kinds(module), [])
        values = assigns(module)
        # bytes = bits [33:2]; element i is [8i+9 : 8i+2].
        self.assertEqual(window(values["b2"]), (25, 18, 8, "p"))
        self.assertEqual(window(values["b0"]), (9, 2, 8, "p"))
        # bytes[1][3:0]: the low nibble of element 1 = [13:10].
        self.assertEqual(window(values["nib"]), (13, 10, 4, "p"))
        # bytes[2:1]: elements 2 and 1 = [25:10], 16 bits over a 16-bit span.
        self.assertEqual(window(values["r"]), (25, 10, 16, "p"))
        # A plain member (no select) is unchanged.
        self.assertEqual(window(values["tg"]), (1, 0, 2, "p"))

    UNION = (
        "module top (input logic [31:0] w_i, output logic [31:0] swapped_o,"
        " output logic [15:0] hi_o, output logic [7:0] byte3_o,"
        " output logic bit5_o, output logic [3:0] mid_o);"
        " typedef union packed { logic [31:0] w; logic [1:0][15:0] h;"
        " logic [3:0][7:0] b; } word_u;"
        " word_u in_v, out_v;"
        " always_comb begin in_v.w = w_i;"
        " out_v.b[0] = in_v.b[3]; out_v.b[1] = in_v.b[2];"
        " out_v.b[2] = in_v.b[1]; out_v.b[3] = in_v.b[0]; end"
        " assign swapped_o = out_v.w; assign hi_o = in_v.h[1];"
        " assign byte3_o = in_v.b[3]; assign bit5_o = in_v.w[5];"
        " assign mid_o = in_v.w[3 +: 4]; endmodule")

    def test_union_member_reads(self):
        module = self.extract(self.UNION)
        self.assertEqual(sv_kinds(module), [])
        values = assigns(module)
        self.assertEqual(window(values["hi_o"]), (31, 16, 16, "in_v"))
        self.assertEqual(window(values["byte3_o"]), (31, 24, 8, "in_v"))
        # A one-dimensional member keeps its bit window, indexed forms too.
        self.assertEqual(window(values["bit5_o"]), (5, 5, 1, "in_v"))
        self.assertEqual(window(values["mid_o"]), (6, 3, 4, "in_v"))

    def test_union_member_write_targets(self):
        module = self.extract(self.UNION)
        stmts = [s for p in module["processes"] if p["kind"] == "AlwaysComb"
                 for s in p["body"]["stmts"]]
        pairs = [(window(s["target"]), window(s["value"])) for s in stmts[1:]]
        # out_v.b[i] = in_v.b[3-i]: byte-swap, every window 8 bits wide.
        self.assertEqual(pairs, [((8 * i + 7, 8 * i, 8, "out_v"),
                                  (8 * (3 - i) + 7, 8 * (3 - i), 8, "in_v"))
                                 for i in range(4)])

    def test_continuous_member_element_target(self):
        module = self.extract(
            "module top (input logic [7:0] a, input logic [7:0] b,"
            " output logic [15:0] o);"
            " typedef union packed { logic [15:0] w; logic [1:0][7:0] b; } u_t;"
            " u_t q; assign q.b[1] = a; assign q.b[0] = b; assign o = q.w;"
            " endmodule")
        self.assertEqual(sv_kinds(module), [])
        targets = {window(p["target"])[:3] for p in module["processes"]
                   if p["kind"] == "Assign" and p["target"]["kind"] == "PartSel"}
        self.assertEqual(targets, {(15, 8, 8), (7, 0, 8)})

    def test_ascending_member_range(self):
        module = self.extract(
            "module top (input logic [33:0] p_i, output logic [7:0] b0,"
            " output logic [7:0] b3, output logic [15:0] r);"
            " typedef struct packed { logic [0:3][7:0] bytes; logic [1:0] tag; } t;"
            " t p; assign p = p_i;"
            " assign b0 = p.bytes[0]; assign b3 = p.bytes[3];"
            " assign r = p.bytes[1:2]; endmodule")
        self.assertEqual(sv_kinds(module), [])
        values = assigns(module)
        # `[0:3]`: element 0 is the MOST significant one.
        self.assertEqual(window(values["b0"]), (33, 26, 8, "p"))
        self.assertEqual(window(values["b3"]), (9, 2, 8, "p"))
        self.assertEqual(window(values["r"]), (25, 10, 16, "p"))

    def test_nested_aggregates(self):
        module = self.extract(
            "module top (input logic [15:0] o_i, output logic [3:0] n1,"
            " output logic [3:0] z);"
            " typedef struct packed { logic [1:0][3:0] n; logic [3:0] z; } inner_t;"
            " typedef struct packed { inner_t inn; logic [3:0] lo; } outer_t;"
            " outer_t o; assign o = o_i;"
            " assign n1 = o.inn.n[1]; assign z = o.inn.z; endmodule")
        self.assertEqual(sv_kinds(module), [])
        values = assigns(module)
        # inn = [15:4]: n = [15:8] (n[1] = [15:12]), z = [7:4].
        self.assertEqual(window(values["n1"]), (15, 12, 4, "o"))
        self.assertEqual(window(values["z"]), (7, 4, 4, "o"))

    def test_member_of_packed_array_element(self):
        module = self.extract(
            "module top (input logic [23:0] a_i, output logic [3:0] an0);"
            " typedef struct packed { logic [1:0][3:0] n; logic [3:0] z; } inner_t;"
            " inner_t [1:0] arr; assign arr = a_i;"
            " assign an0 = arr[1].n[0]; endmodule")
        # (The array-of-struct variable itself is a loud declaration refusal;
        # the select is still lowered, and must be right.)
        self.assertEqual(sv_kinds(assigns(module)["an0"]), [])
        # arr[1] = [23:12]; n inside it is [23:16]; n[0] = [19:16].
        self.assertEqual(window(assigns(module)["an0"]), (19, 16, 4, "arr"))

    def test_nested_indexed_select_over_wide_element(self):
        module = self.extract(
            "module top (input logic [33:0] p_i, output logic [1:0] y);"
            " typedef struct packed { logic [3:0][7:0] bytes; logic [1:0] tag; } t;"
            " t p; assign p = p_i; assign y = p.bytes[1][2 +: 2]; endmodule")
        self.assertEqual(sv_kinds(module), [])
        # bytes[1] = [17:10]; `[2 +: 2]` inside it = bits 2..3 = [13:12].
        self.assertEqual(window(assigns(module)["y"]), (13, 12, 2, "p"))

    def test_unadmitted_member_selects_stay_loud(self):
        module = self.extract(
            "module top #(parameter int K = 2) (input logic [33:0] p_i,"
            " input logic [1:0] i, output logic [7:0] d, output logic [7:0] k,"
            " output logic [7:0] o, output logic [15:0] ix, output logic [7:0] dn);"
            " typedef struct packed { logic [3:0][7:0] bytes; logic [1:0] tag; } t;"
            " t p; assign p = p_i;"
            " assign d = p.bytes[i]; assign k = p.bytes[K];"
            " assign o = p.bytes[7]; assign ix = p.bytes[1 +: 2];"
            " assign dn = p.bytes[i][7:0]; endmodule")
        values = assigns(module)
        self.assertEqual(sv_kinds(values["d"]), ["ElementSelectExpression:member-index"])
        # A parameter label is folded at the default point only: loud.
        self.assertEqual(sv_kinds(values["k"]), ["ElementSelectExpression:member-index"])
        self.assertEqual(sv_kinds(values["o"]), ["ElementSelectExpression:member-index"])
        self.assertEqual(sv_kinds(values["ix"]),
                         ["RangeSelectExpression:member-indexed"])
        self.assertEqual(sv_kinds(values["dn"]), ["ElementSelectExpression:member-index"])


class SelectGuard(unittest.TestCase):
    """`_sym_select_checked`: any select whose emitted window disagrees with
    the compiler-resolved type is loud, whichever lowering produced it."""

    def extract(self, source, mutate):
        original = extract._convert_sym_select_expr

        def patched(sm, e, cname):
            node = original(sm, e, cname)
            mutate(node)
            return node

        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            with mock.patch.object(extract, "_convert_sym_select_expr", patched):
                extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    SOURCE = ("module top (input logic [33:0] p_i, output logic [7:0] y);"
              " typedef struct packed { logic [3:0][7:0] bytes; logic [1:0] tag; } t;"
              " t p; assign p = p_i; assign y = p.bytes[2]; endmodule")

    def selected(self, module):
        return assigns(module)["y"]

    def test_unmutated_is_accepted(self):
        module = self.extract(self.SOURCE, lambda node: None)
        self.assertEqual(sv_kinds(module), [])

    def test_width_disagreeing_with_the_resolved_type_is_loud(self):
        def mutate(node):
            if node["kind"] == "PartSel":
                node["width"] = 1
                node["msb"]["value"] = node["lsb"]["value"]
        module = self.extract(self.SOURCE, mutate)
        self.assertEqual(sv_kinds(self.selected(module)),
                         ["ElementSelectExpression:window-mismatch"])

    def test_span_disagreeing_with_the_width_is_loud(self):
        def mutate(node):
            if node["kind"] == "PartSel":
                node["msb"]["value"] = node["lsb"]["value"] + 2
        module = self.extract(self.SOURCE, mutate)
        self.assertEqual(sv_kinds(self.selected(module)),
                         ["ElementSelectExpression:window-mismatch"])

    def test_window_outside_the_emitted_vector_is_loud(self):
        def mutate(node):
            if node["kind"] == "PartSel":
                node["msb"]["value"] += 40
                node["lsb"]["value"] += 40
        module = self.extract(self.SOURCE, mutate)
        self.assertEqual(sv_kinds(self.selected(module)),
                         ["ElementSelectExpression:window-mismatch"])

    def test_write_target_with_a_wrong_window_is_loud(self):
        source = ("module top (input logic [7:0] a, output logic [15:0] o);"
                  " typedef union packed { logic [15:0] w; logic [1:0][7:0] b; } u_t;"
                  " u_t q; always_comb begin q.w = 16'h0; q.b[1] = a; end"
                  " assign o = q.w; endmodule")

        def mutate(node):
            if node["kind"] == "PartSel":
                node["width"] = 1
        module = self.extract(source, mutate)
        self.assertTrue(sv_kinds(module))


class LegacySelectGuard(unittest.TestCase):
    """The self-check (M0) select reads and targets are held to the width
    invariant as well."""

    SOURCE = ("module top; logic [7:0] v; logic [3:0] hi; "
              "initial begin v = 8'hA5; hi = v[7:4]; v[3:0] = hi; end endmodule")

    def design(self):
        from pyslang.ast import Compilation
        from pyslang.syntax import SyntaxTree
        tree = SyntaxTree.fromText(self.SOURCE)
        compilation = Compilation()
        compilation.addSyntaxTree(tree)
        compilation.getAllDiagnostics()
        extract._SOURCE_BYTES = self.SOURCE.encode()
        return extract.convert_design(tree.sourceManager, compilation)

    @staticmethod
    def unsupported_kinds(value, found=None):
        found = [] if found is None else found
        if isinstance(value, dict):
            if value.get("kind") == "Unsupported":
                found.append(value.get("sv_kind"))
            for child in value.values():
                LegacySelectGuard.unsupported_kinds(child, found)
        elif isinstance(value, list):
            for child in value:
                LegacySelectGuard.unsupported_kinds(child, found)
        return found

    def test_unmutated_selects_are_admitted(self):
        self.assertEqual(self.unsupported_kinds(self.design()), [])

    def test_select_read_with_a_wrong_width_is_loud(self):
        original = extract._convert_selected_read

        def patched(sm, expr, kind):
            node = original(sm, expr, kind)
            if node.get("kind") == "SelectRead":
                node["width"] = 1
            return node

        with mock.patch.object(extract, "_convert_selected_read", patched):
            kinds = self.unsupported_kinds(self.design())
        self.assertIn("RangeSelectExpression:window-mismatch", kinds)

    def test_select_target_with_a_wrong_width_is_loud(self):
        original = extract._legacy_blocking_target

        def patched(sm, lhs, concat_leaf=False):
            node, admitted = original(sm, lhs, concat_leaf)
            if node.get("kind") == "SelectTarget":
                node["width"] = 1
            return node, admitted

        with mock.patch.object(extract, "_legacy_blocking_target", patched):
            kinds = self.unsupported_kinds(self.design())
        # A refused select leaves no usable target: the assignment's own tag
        # reaches the envelope (as for `Select:wide-index` writes).
        self.assertEqual(kinds, ["AssignmentExpression:target"])


if __name__ == "__main__":
    unittest.main()
