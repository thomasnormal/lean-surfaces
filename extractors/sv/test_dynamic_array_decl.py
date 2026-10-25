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

    def test_4state_dynamic_array_without_allocation_stays_loud(self):
        design = lower(
            'module top; logic values[]; initial $finish; endmodule')
        self.assertIn("VariableSymbol:type",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_4state_dynamic_array_constant_allocation_is_live(self):
        design = lower(
            """module top;
               logic values[];
               int index;
               initial begin
                 values = new[3];
                 index = 2;
                 values[index] = 1'b1;
                 if (values[0] === 1'bx && values[index] === 1'b1)
                   $display("PASS");
               end
               endmodule""")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        decls = [node for node in nodes(design) if node.get("kind") == "Var"]
        values = [node for node in decls if node.get("name", "").startswith("values[")]
        self.assertEqual([node["name"] for node in values],
                         ["values[0]", "values[1]", "values[2]"])
        self.assertTrue(all(node.get("init") is None for node in values))

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

    def test_dynamic_to_fixed_size_mismatch_is_runtime_halt(self):
        design = lower(
            """module top;
               int fixed_values[2];
               int dynamic_values[] = new[3];
               initial begin
                 fixed_values = dynamic_values;
               end
               endmodule""")
        self.assertTrue(any(node.get("dynamic_fixed_size_mismatch")
                            and node.get("kind") == "SysCall"
                            and node.get("name") == "$finish"
                            for node in nodes(design)))

    def test_dynamic_to_fixed_size_mismatch_halts_without_copy(self):
        design = lower(
            """module top;
               int fixed_values[2];
               int dynamic_values[] = new[3];
               initial begin
                 fixed_values = dynamic_values;
                 $display("UNREACHED");
               end
               endmodule""")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             and node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("dynamic_fixed_size_mismatch")
                            and node.get("kind") == "SysCall"
                            and node.get("name") == "$finish"
                            for node in nodes(design)))

    def test_dynamic_to_fixed_equal_size_stays_live(self):
        design = lower(
            """module top;
               int fixed_values[2];
               int dynamic_values[] = new[2];
               initial begin
                 fixed_values = dynamic_values;
               end
               endmodule""")
        self.assertFalse(any(node.get("dynamic_fixed_size_mismatch")
                             for node in nodes(design)))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             and node.get("sv_kind") ==
                             "AssignmentExpression:target"
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

    def test_struct_elements_receive_type_defaults(self):
        design = lower(
            """module top;
               typedef struct { int count; bit [3:0] tag; } item_t;
               item_t items[];
               initial begin
                 items = new[2];
                 if (items[0].count == 0 && items[0].tag === 0 &&
                     items[1].count == 0 && items[1].tag === 0)
                   $display("PASS");
               end
               endmodule""")
        decls = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertEqual([decl["name"] for decl in decls], [
            "items[0].count", "items[0].tag", "items[1].count", "items[1].tag"])
        self.assertEqual(decls[0]["init"]["operand"]["bits"], "0" * 32)
        self.assertEqual(decls[1]["init"]["operand"]["bits"], "0" * 4)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_struct_elements_receive_field_initializers(self):
        design = lower(
            """module top;
               typedef struct { int id = 7; byte code; } item_t;
               item_t items[];
               initial begin
                 items = new[2];
                 if (items[0].id == 7 && items[0].code == 0 &&
                     items[1].id == 7 && items[1].code == 0)
                   $display("PASS");
               end
               endmodule""")
        decls = [node for node in nodes(design) if node.get("kind") == "Var"]
        ids = [decl for decl in decls if decl["name"].endswith(".id")]
        self.assertEqual(len(ids), 2)
        self.assertTrue(all(decl["init"]["kind"] == "Squash2" for decl in ids))
        self.assertTrue(all(decl["init"]["operand"]["bits"] ==
                            format(7, "032b") for decl in ids))
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_four_state_struct_dynamic_array_constant_allocation_is_live(self):
        design = lower(
            """module top;
               typedef struct { logic value; bit ready; } item_t;
               item_t items[];
               initial begin
                 items = new[2];
                 if (items[0].value === 1'bx && items[0].ready === 1'b0)
                   $display("PASS");
               end
               endmodule""")
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
