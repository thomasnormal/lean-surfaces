"""Direct integral packed-struct field windows reuse vector state."""
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


class PackedStructFields(unittest.TestCase):
    def test_direct_field_read_write_is_a_window(self):
        design = extract_source(
            "module top; typedef struct packed { logic [3:0] hi; logic [3:0] lo;} T; "
            "T value; initial begin value.hi = 4'ha; "
            "if (value.hi === 4'ha) $display(\"PASS\"); end endmodule")
        targets = [node for node in nodes(design)
                   if node.get("kind") == "SelectTarget"]
        reads = [node for node in nodes(design)
                 if node.get("kind") == "SelectRead"]
        self.assertEqual(len(targets), 1)
        self.assertEqual(len(reads), 1)
        self.assertEqual(targets[0]["width"], 4)
        self.assertEqual(targets[0]["index"]["bits"], "0" * 29 + "100")

    def test_nested_member_chain_is_one_window(self):
        design = extract_source(
            "module top; typedef struct packed { logic [3:0] hi;} T; "
            "typedef struct packed { T inner;} U; U value; "
            "initial begin value.inner.hi = 4'ha; "
            "if (value.inner.hi === 4'ha) $display(\"PASS\"); end endmodule")
        targets = [node for node in nodes(design)
                   if node.get("kind") == "SelectTarget"]
        reads = [node for node in nodes(design)
                 if node.get("kind") == "SelectRead"]
        self.assertEqual(len(targets), 1)
        self.assertEqual(len(reads), 1)
        self.assertEqual(targets[0]["value"]["name"], "value")
        self.assertEqual(targets[0]["index"]["bits"], "0" * 32)
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_packed_array_element_member_is_one_window(self):
        design = extract_source(
            "module top; typedef struct packed { logic [3:0] hi; "
            "logic [3:0] lo;} T; T [3:0] value; "
            "initial begin value[0].hi = 4'ha; "
            "if (value[0].hi === 4'ha) $display(\"PASS\"); end endmodule")
        targets = [node for node in nodes(design)
                   if node.get("kind") == "SelectTarget"]
        reads = [node for node in nodes(design)
                 if node.get("kind") == "SelectRead"]
        self.assertEqual(len(targets), 1)
        self.assertEqual(len(reads), 1)
        self.assertEqual(targets[0]["value"]["name"], "value")
        self.assertEqual(targets[0]["index"]["bits"], "0" * 29 + "100")

    def test_packed_array_dynamic_element_member_stays_loud(self):
        design = extract_source(
            "module top(input logic [1:0] index); "
            "typedef struct packed { logic [3:0] hi; logic [3:0] lo;} T; "
            "T [3:0] value; initial value[index].hi = 4'ha; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
