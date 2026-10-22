"""Aggregate initializers for shallow unpacked integral structs are cells."""
import unittest

from test_packed_assignment_targets import extract_source, nodes


class UnpackedStructInitializers(unittest.TestCase):
    def test_positional_initializer_squashes_two_state_fields(self):
        design = extract_source(
            "module top; typedef struct { bit [3:0] bits; int count; } T; "
            "T value = '{4'b1x0z, 3}; endmodule")
        decls = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertEqual([decl["name"] for decl in decls],
                         ["value.bits", "value.count"])
        self.assertEqual(decls[0]["init"]["operand"]["bits"], "1x0z")
        self.assertEqual(decls[1]["init"]["operand"]["bits"],
                         format(3, "032b"))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_keyed_and_default_initializers_follow_field_order(self):
        for initializer in ("'{count: 7, bits: 4'ha}", "'{default: 4'h3}"):
            with self.subTest(initializer=initializer):
                design = extract_source(
                    "module top; typedef struct { bit [3:0] bits; "
                    "bit [3:0] count; } T; T value = " + initializer +
                    "; endmodule")
                decls = [node for node in nodes(design)
                         if node.get("kind") == "Var"]
                self.assertEqual([decl["init"]["operand"]["bits"]
                                  for decl in decls],
                                 ["1010", "0111"] if "count:" in initializer
                                 else ["0011", "0011"])
                self.assertFalse(any(node.get("kind") == "Unsupported"
                                     for node in nodes(design)))

    def test_partial_keyed_initializer_stays_loud(self):
        design = extract_source(
            "module top; struct { bit [3:0] bits; bit count; } value = "
            "'{bits: 4'ha}; endmodule")
        self.assertTrue(any(node.get("sv_kind") == "VariableSymbol:2state"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
