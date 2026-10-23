"""Declaration-only 2-state dynamic arrays are inert."""

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


class DynamicArrayDeclarations(unittest.TestCase):
    def test_uninitialized_2state_dynamic_array_is_inert(self):
        design = lower(
            'module top; bit values[]; initial $display("PASS"); endmodule')
        self.assertFalse(any(node.get("sv_kind") == "VariableSymbol:2state"
                             for node in nodes(design)))

    def test_initialized_dynamic_array_stays_loud(self):
        design = lower(
            "module top; bit values[] = '{1, 2}; initial $finish; endmodule")
        self.assertIn("VariableSymbol:2state",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_4state_dynamic_array_stays_loud(self):
        design = lower(
            'module top; logic values[]; initial $finish; endmodule')
        self.assertIn("VariableSymbol:type",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_constant_new_dynamic_array_flattens_for_fixed_copy(self):
        design = lower(
            """module top;
               int fixed_values[3];
               int dynamic_values[] = new[3];
               initial begin
                 for (int i = 0; i < 3; i++) dynamic_values[i] = i + 1;
                 fixed_values = dynamic_values;
                 $display("PASS");
               end
               endmodule""")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("kind") == "Var" and
                            node.get("name") == "dynamic_values[2]"
                            for node in nodes(design)))

    def test_dynamic_to_fixed_size_mismatch_stays_loud(self):
        design = lower(
            """module top;
               int fixed_values[2];
               int dynamic_values[] = new[3];
               initial begin
                 fixed_values = dynamic_values;
               end
               endmodule""")
        self.assertTrue(any(node.get("kind") == "Unsupported" and
                            node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_procedural_constant_allocation_and_cells_are_live(self):
        design = lower(
            """module top;
               initial begin
                 int values[];
                 values = new[2];
                 values[0] = 10;
                 values[1] = 20;
                 if (values[1] == 20) $display("PASS");
               end
               endmodule""")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
