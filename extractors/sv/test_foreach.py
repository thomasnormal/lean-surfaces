"""IEEE 12.7.3 fixed foreach lowering, including whole-loop transfers."""
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=Foreach | origin=spec | authority=IEEE-1800-2023#12.7.3 | map=bindings:automatic-signed-int;dimensions:declared-order;control:one-ordinal-loop


def loops(design):
    return [n for n in nodes(design) if n.get("foreach_lowered")]


class Foreach(unittest.TestCase):
    def test_mixed_dimensions_share_one_loop(self):
        d = lower("module top; bit [3:1] mem[2:0]; int sum; initial foreach(mem[i,j]) sum+=mem[i][j]; endmodule")
        loop, = loops(d)
        self.assertEqual([(x["left"], x["right"]) for x in loop["foreach_dimensions"]],
                         [(2, 0), (3, 1)])
        self.assertEqual(int(loop["condition"]["right"]["bits"], 2), 9)
        self.assertEqual(len([n for n in nodes(d) if n.get("kind") == "For"]), 1)
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(d)))

    def test_negative_ascending_bounds_and_omissions(self):
        d = lower("module top; bit [3:1] mem[-1:1]; initial begin foreach(mem[,j]) begin end foreach(mem[]) begin end end endmodule")
        first, empty = loops(d)
        self.assertEqual([(x["left"], x["right"]) for x in first["foreach_dimensions"]], [(3, 1)])
        self.assertEqual(empty["foreach_dimensions"], [])
        self.assertEqual(int(empty["condition"]["right"]["bits"], 2), 1)

    def test_iterator_scopes_do_not_alias_same_named_bindings(self):
        d = lower("module top; int a[2]; int i=99; initial begin foreach(a[i]) foreach(a[i]) begin end foreach(a[i]) begin end end endmodule")
        decls = [n for n in nodes(d) if n.get("automatic_foreach")]
        names = [n["name"] for n in decls]
        self.assertEqual(len(names), len(set(names)))
        self.assertNotIn("i", names)
        self.assertTrue(all(n["width"] == 32 for n in decls))
        self.assertTrue(all(n["signed"] for n in decls if not n["name"].endswith(":$ordinal")))

    def test_reentry_and_automatic_array_body_are_admitted(self):
        d = lower("module top; int a[2]; initial repeat(2) foreach(a[i]) begin automatic int b[2]='{1,2}; a[i]=b[0]; end endmodule")
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(d)))

    def test_scalar_body_lifetimes_stay_loud(self):
        d = lower("module top; int a[2]; initial foreach(a[i]) begin int value=0; value++; end endmodule")
        self.assertTrue(any(n.get("sv_kind") == "ForeachLoopStatement:body-lifetime" for n in nodes(d)))

    def test_dynamic_and_unsupported_storage_stay_loud(self):
        for declaration in ("int a[]", "int a[$]", "int a[int]", "int a[2][3]"):
            d = lower("module top; " + declaration + "; initial foreach(a[i]) begin end endmodule")
            self.assertFalse(loops(d))
            self.assertTrue(any(n.get("sv_kind") == "ForeachLoopStatement:array" for n in nodes(d)))

    def test_symbolic_foreach_stays_loud(self):
        d = symbolic("module divider; int a[2]; initial foreach(a[i]) a[i]=i; endmodule")
        self.assertFalse(loops(d))
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(d)))

    def test_invalid_iterator_write_is_a_design_barrier(self):
        d = lower("module top; int a[2]; initial foreach(a[i]) i=1; endmodule", require_valid=False)
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(d)))
        d = lower("module top; int a[2]; initial foreach(a[i]) a[i]=i; initial missing=1; endmodule", require_valid=False)
        self.assertTrue(any(n.get("sv_kind") == "Loop:invalid-compilation" for n in nodes(d)))

    def test_names_are_stable_across_frontend_buffers(self):
        source = "module top; int a[2]; initial foreach(a[i]) a[i]=i; endmodule"
        def names():
            return [n["name"] for n in nodes(lower(source)) if n.get("automatic_foreach")]
        self.assertEqual(names(), names())

    def test_declared_packed_index_is_widened_before_subtraction(self):
        d = lower("module top; logic [-1:-3] word; int index; initial $display(\"%b\",word[index]); endmodule")
        read, = [n for n in nodes(d) if n.get("kind") == "SelectRead"]
        self.assertEqual(read["index"]["op"], "-")
        self.assertEqual(read["index"]["width"], 34)
        self.assertTrue(read["index_signed"])
        self.assertEqual(read["index"]["left"]["kind"], "SignedResize")

    def test_unresolved_index_types_and_effects_stay_loud(self):
        for declaration, index in (("logic [63:0] index", "index"),
                                   ("int index", "index++")):
            d = lower("module top; logic [-1:-3] word; " + declaration +
                      "; initial $display(\"%b\",word[" + index + "]); endmodule")
            self.assertTrue(any(n.get("sv_kind") == "ElementSelectExpression:source-type"
                                for n in nodes(d)))

    def test_escaped_source_name_cannot_alias_iterator(self):
        source = "module top; int a[2]; initial foreach(a[i]) begin end endmodule"
        name = next(n["name"] for n in nodes(lower(source)) if n.get("automatic_foreach"))
        # Append without moving the loop's source offsets.
        source = source.replace(" endmodule", " int \\" + name + " ; endmodule")
        d = lower(source)
        self.assertTrue(any(n.get("sv_kind") == "ForeachLoopStatement:storage-collision" for n in nodes(d)))


if __name__ == "__main__":
    unittest.main()
