"""One-dimensional fixed-array `%p` diagnostics use flattened cells."""
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


class ArrayNamedDisplay(unittest.TestCase):
    def test_fixed_array_percent_p_uses_declared_cell_order(self):
        design = extract_source(
            "module top; typedef int triple[1:3]; "
            "initial begin triple t; t = '{1, 2, 3}; "
            "$display(\"FAIL %p\", t); end endmodule")
        displays = [node for node in nodes(design)
                    if node.get("kind") == "ArrayDisplay"]
        self.assertEqual(len(displays), 1)
        names = [item["name"] for item in displays[0]["elements"]]
        self.assertEqual([name.rsplit(":", 1)[-1] for name in names],
                         ["t[1]", "t[2]", "t[3]"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_nested_array_percent_p_stays_loud(self):
        design = extract_source(
            "module top; int value [0:1][0:1]; "
            "initial $display(\"FAIL %p\", value); endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

    def test_packed_struct_elements_stay_loud(self):
        design = extract_source(
            "module top; typedef struct packed {logic [3:0] x;} item_t; "
            "item_t value [0:1]; initial begin "
            "$display(\"FAIL %p\", value); end endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))

if __name__ == "__main__":
    unittest.main()
