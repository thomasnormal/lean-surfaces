"""Time-zero `$time` expression admission for the self-check surface."""
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


class TimeQueries(unittest.TestCase):
    def test_time_is_zero_literal_at_time_zero(self):
        design = extract_source(
            "module top; initial $display(\"%0d\", $time); endmodule")
        times = [node for node in nodes(design)
                 if node.get("kind") == "Literal" and node.get("time_zero")]
        self.assertEqual([(node["width"], node["bits"]) for node in times],
                         [(64, "0" * 64)])

    def test_time_arguments_stay_loud(self):
        design = extract_source(
            "module top; integer unit; initial $display(\"%0d\", $time(unit)); endmodule")
        self.assertIn("InvalidStatement",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_stime_is_zero_literal_at_time_zero(self):
        design = extract_source(
            "module top; initial $display(\"%0d\", $stime); endmodule")
        times = [node for node in nodes(design)
                 if node.get("kind") == "Literal" and node.get("time_zero")]
        self.assertEqual([(node["width"], node["bits"]) for node in times],
                         [(32, "0" * 32)])

    def test_stime_arguments_stay_loud(self):
        design = extract_source(
            "module top; integer unit; initial $display(\"%0d\", $stime(unit)); endmodule")
        self.assertIn("InvalidStatement",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
