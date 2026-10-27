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

    def test_realtime_to_integral_is_zero_literal_at_time_zero(self):
        design = extract_source(
            "module top; integer now; initial now = $realtime; endmodule")
        values = [node for node in nodes(design)
                  if node.get("kind") == "Literal" and
                  node.get("realtime_conversion")]
        self.assertEqual([(node["width"], node["bits"], node["time_zero"])
                          for node in values],
                         [(32, "0" * 32, True)])

    def test_realtime_direct_value_stays_loud(self):
        design = extract_source(
            "module top; initial $display(\"%f\", $realtime); endmodule")
        self.assertIn("CallExpression",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_realtime_exact_conversions_are_zero_at_time_zero(self):
        design = extract_source(
            "module top; initial begin "
            "if ($rtoi($realtime) !== 0) $display(\"FAIL\"); "
            "if ($realtobits($realtime) !== 64'b0) $display(\"FAIL\"); "
            "if ($shortrealtobits($realtime) !== 32'b0) $display(\"FAIL\"); "
            "end endmodule")
        values = [node for node in nodes(design)
                  if node.get("rtoi_literal") or
                  node.get("realtobits_literal") or
                  node.get("shortrealtobits_literal")]
        self.assertEqual(len(values), 3)
        self.assertEqual([(node["width"], node["bits"]) for node in values], [
            (32, "0" * 32),
            (64, "0" * 64),
            (32, "0" * 32),
        ])
        self.assertFalse(any(node.get("sv_kind") == "CallExpression"
                             for node in nodes(design)))

    def test_realtime_conversion_after_delay_stays_loud(self):
        design = extract_source(
            "module top; initial begin #1; "
            "if ($rtoi($realtime) === 1) $display(\"PASS\"); "
            "end endmodule")
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_realtime_conversion_outside_initial_stays_loud(self):
        design = extract_source(
            "module top; logic [31:0] out; "
            "assign out = $rtoi($realtime); endmodule")
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
