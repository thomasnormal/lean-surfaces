import unittest

import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


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


class LiteralFormatStrings(unittest.TestCase):
    def test_display_accepts_literal_string_concatenation(self):
        design = lower(
            'module top; initial $display({"PA", "SS"}); endmodule')
        calls = [node for node in nodes(design) if node.get("kind") == "SysCall"]
        self.assertEqual([(call["name"], call["format"]) for call in calls],
                         [("$display", "PASS")])

    def test_dynamic_format_concatenation_stays_loud(self):
        design = lower(
            'module top; string fmt; initial $display({fmt, "SS"}); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "SysCall:format"
                            for node in nodes(design)))

    def test_all_output_format_boundaries_share_the_fold(self):
        design = lower(
            'module top; initial begin '
            '$write({"A", "B"}); $strobe({"C", "D"}); '
            '$fdisplay(32\'d1, {"E", "F"}); '
            '$fwrite(32\'d1, {"G", "H"}); end endmodule')
        calls = [node for node in nodes(design) if node.get("kind") == "SysCall"]
        self.assertEqual([(call["name"], call["format"]) for call in calls],
                         [("$write", "AB"), ("$strobe", "CD"),
                          ("$display", "EF"), ("$write", "GH")])


if __name__ == "__main__":
    unittest.main()
