"""The predefined stdout descriptor has a deterministic position error."""

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


class FtellCalls(unittest.TestCase):
    def test_stdout_position_returns_minus_one(self):
        design = extract_source(
            "module top; int position; initial "
            "position = $ftell(32'h8000_0001); endmodule")
        values = [node for node in nodes(design)
                  if node.get("kind") == "Literal"
                  and node.get("ftell_stdout_error")]
        self.assertEqual([(node["width"], node["bits"]) for node in values],
                         [(32, "1" * 32)])

    def test_dynamic_descriptor_stays_loud(self):
        design = extract_source(
            "module top; int fd, position; initial "
            "position = $ftell(fd); endmodule")
        self.assertIn("CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_discarded_stdout_position_is_inert(self):
        design = extract_source(
            "module top; initial $ftell(32'h8000_0001); endmodule")
        self.assertIn(True, [node.get("ftell_stdout_error_statement")
                             for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
