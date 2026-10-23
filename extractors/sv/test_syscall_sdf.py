"""The inert `$sdf_annotate` self-check slice is deliberately narrow."""

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


class SdfAnnotateTask(unittest.TestCase):
    def test_filename_and_empty_config_forms_are_inert(self):
        design = lower(
            'module top; initial begin '
            '$sdf_annotate("timing.sdf"); '
            '$sdf_annotate("noexist.sdf", top, ""); '
            '$display("PASS"); end endmodule')
        unsupported = [node for node in nodes(design)
                       if node.get("sv_kind") == "ExpressionStatement:CallExpression"]
        self.assertEqual(unsupported, [])
        self.assertEqual(
            [node.get("pure_diagnostic") for node in nodes(design)
             if node.get("kind") == "Empty"],
            ["$sdf_annotate", "$sdf_annotate"],
        )

    def test_timing_bearing_optional_forms_stay_loud(self):
        design = lower(
            'module top; string cfg; initial begin '
            '$sdf_annotate("timing.sdf", top); '
            '$sdf_annotate("timing.sdf", top, "config.sdf"); '
            '$sdf_annotate(cfg); end endmodule')
        self.assertEqual(
            [node.get("sv_kind") for node in nodes(design)].count(
                "ExpressionStatement:CallExpression"),
            3,
        )


if __name__ == "__main__":
    unittest.main()
