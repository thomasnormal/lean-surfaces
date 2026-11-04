"""Positional fixed-unpacked array initializers lowered to vector cells."""
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


class UnpackedArrayInitializers(unittest.TestCase):
    def test_positional_pattern_populates_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1] = '{8'h12, 8'h34}; "
            "initial if (value[1] === 8'h34) $display(\"PASS\"); endmodule")
        decls = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertEqual([(d["name"], d["init"]["bits"]) for d in decls],
                         [("value[0]", "00010010"), ("value[1]", "00110100")])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_default_pattern_populates_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1] = '{default:8'h12}; "
            "initial $display(\"%h\", value[0]); endmodule")
        decls = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertEqual([(d["name"], d["init"]["bits"]) for d in decls],
                         [("value[0]", "00010010"),
                          ("value[1]", "00010010")])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_replicated_pattern_populates_cells(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1] = '{2{8'h34}}; "
            "initial $display(\"%h\", value[1]); endmodule")
        decls = [node for node in nodes(design) if node.get("kind") == "Var"]
        self.assertEqual([d["init"]["bits"] for d in decls],
                         ["00110100", "00110100"])
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))

    def test_wrong_length_replicated_initializer_stays_loud(self):
        design = extract_source(
            "module top; logic [7:0] value [0:1] = '{3{8'h34}}; "
            "initial $display(\"%h\", value[1]); endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
