"""Bound packed blocking targets, before any constant folding of effects."""
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


class PackedAssignmentTargets(unittest.TestCase):
    def targets(self, statement, declarations="logic [7:0] value; integer index;"):
        design = extract_source("module top; " + declarations +
                                " initial begin " + statement + " end endmodule")
        return [node for node in nodes(design) if node.get("kind") == "SelectTarget"]

    def test_live_bit_index_keeps_signedness(self):
        target, = self.targets("value[index] = 1'b1;")
        self.assertEqual(target["width"], 1)
        self.assertTrue(target["index_signed"])
        self.assertFalse(target["descending"])
        self.assertEqual(target["index"]["kind"], "Ident")

    def test_simple_and_indexed_parts_keep_geometry(self):
        targets = self.targets("value[5:2] = 4'b0011; value[index +: 2] = 2'b01; "
                               "value[index -: 3] = 3'b110;")
        self.assertEqual([target["width"] for target in targets], [4, 2, 3])
        self.assertEqual([target["descending"] for target in targets], [False, False, True])

    def test_two_state_leaf_retains_conversion(self):
        target, = self.targets("value[3:1] = 3'bxz1;", "bit [7:0] value;")
        self.assertTrue(target["two_state"])

    def test_effectful_index_stays_loud(self):
        self.assertFalse(self.targets("value[index++] = 1'b1;"))

    def test_effectful_rhs_stays_loud(self):
        design = extract_source("module top; logic [7:0] value; "
                                "initial value[0] = $urandom(); endmodule")
        reasons = [node.get("sv_kind") for node in nodes(design)]
        self.assertIn("AssignmentExpression:selected-effects", reasons)

    def test_nonblocking_selected_target_keeps_window_geometry(self):
        target, = self.targets("value[0] <= 1'b1;")
        self.assertEqual(target["kind"], "SelectTarget")

    def test_unpacked_base_is_not_a_packed_destination(self):
        self.assertFalse(self.targets("value[0] = 4'b1010;", "logic [3:0] value [2];"))

    def test_frontend_errors_are_not_erased(self):
        design = extract_source("module top; logic [7:0] value; initial begin "
                                "value[0] = 1'b1; end initial missing = 1; endmodule")
        reasons = [node.get("sv_kind") for node in nodes(design)]
        self.assertIn("SelectTarget:invalid-compilation", reasons)

    def test_concat_preserves_source_order_and_widths(self):
        design = extract_source("module top; logic [1:0] first, second; "
                                "initial {first, second} = 4'b1001; endmodule")
        target, = [node for node in nodes(design) if node.get("kind") == "ConcatTarget"]
        self.assertEqual(target["width"], 4)
        self.assertEqual([part["name"] for part in target["parts"]], ["first", "second"])
        self.assertEqual([part["width"] for part in target["parts"]], [2, 2])

    def test_nested_mixed_concat_retains_each_leaf_type(self):
        design = extract_source("module top; bit [1:0] first; logic [3:0] second; "
                                "integer index; initial {first, {second[index], second[3:2]}} "
                                "= 5'bxz101; endmodule")
        targets = [node for node in nodes(design) if node.get("kind") == "ConcatTarget"]
        self.assertEqual([target["width"] for target in targets], [5, 3])
        self.assertTrue(targets[0]["parts"][0]["two_state"])
        self.assertEqual([part["width"] for part in targets[1]["parts"]], [1, 2])
        self.assertTrue(targets[1]["parts"][0]["index_signed"])

    def test_alias_and_index_dependencies_are_not_precaptured(self):
        design = extract_source("module top; logic [1:0] index; logic [3:0] value; "
                                "initial {index, value[index]} = 3'b111; endmodule")
        target, = [node for node in nodes(design) if node.get("kind") == "ConcatTarget"]
        self.assertEqual(target["parts"][1]["index"]["kind"], "Ident")
        self.assertEqual(target["parts"][1]["index"]["name"], "index")

    def test_effectful_concat_index_is_loud(self):
        design = extract_source("module top; logic [3:0] value; integer index; "
                                "initial {value[index++], value[0]} = 2'b11; endmodule")
        self.assertFalse(any(node.get("kind") == "ConcatTarget" for node in nodes(design)))

    def test_effectful_concat_rhs_is_loud_before_folding(self):
        design = extract_source("module top; logic first, second; "
                                "initial {first, second} = $urandom(); endmodule")
        self.assertIn("AssignmentExpression:selected-effects",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_concat_error_barrier_is_not_erased(self):
        design = extract_source("module top; logic first, second; "
                                "initial {first, second} = 2'b11; initial missing = 1; endmodule")
        self.assertIn("ConcatTarget:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_selected_concatenation_is_not_an_lvalue(self):
        design = extract_source("module top; logic [1:0] first, second; "
                                "initial {first, second}[1:0] = 2'b11; endmodule")
        self.assertFalse(any(node.get("kind") == "ConcatTarget" for node in nodes(design)))

    def test_nonblocking_concat_stays_pending(self):
        design = extract_source("module top; logic first, second; "
                                "initial {first, second} <= 2'b11; endmodule")
        self.assertFalse(any(node.get("kind") == "ConcatTarget"
                             for node in nodes(design)))

    def test_nonblocking_concat_stays_pending(self):
        design = extract_source("module top; logic first, second; "
                                "initial {first, second} <= 2'b11; endmodule")
        self.assertFalse(any(node.get("kind") == "ConcatTarget" for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
