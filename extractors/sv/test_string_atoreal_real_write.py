"""Source-pure ``string.atoreal()`` writes disappear into opaque real storage."""

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


class StringAtorealRealWrite(unittest.TestCase):
    def test_ascii_literal_conversion_is_inert(self):
        design = lower(
            'module top; string text; real value; initial begin '
            'text = "3.14"; value = text.atoreal(); '
            '$display("PASS"); end endmodule')
        all_nodes = list(nodes(design))
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in all_nodes))
        self.assertTrue(any(node.get("floating_string_atoreal_write_noop")
                            for node in all_nodes))

    def test_dynamic_or_aliased_string_stays_loud(self):
        for source in (
                'module top; string text, source; real value; initial begin '
                'source = "3.14"; text = source; value = text.atoreal(); end endmodule',
                'module top; string text, other; real value; initial begin '
                'text = "3.14"; other = text; value = text.atoreal(); end endmodule'):
            design = lower(source)
            kinds = [node.get("sv_kind") for node in nodes(design)]
            self.assertTrue("AssignmentExpression:target" in kinds
                            or "IntraAssignment:type-or-effects" in kinds)

    def test_non_ascii_and_observed_real_stay_loud(self):
        for source in (
                'module top; string text; real value; initial begin '
                'text = "hé"; value = text.atoreal(); end endmodule',
                'module top; string text; real value; initial begin '
                'text = "3.14"; value = text.atoreal(); '
                'if (value > 3.0) $display("PASS"); end endmodule'):
            design = lower(source)
            kinds = [node.get("sv_kind") for node in nodes(design)]
            if "hé" in source:
                self.assertIn("AssignmentExpression:target", kinds)
            else:
                self.assertIn("NamedValueExpression:2state", kinds)

    def test_scheduled_and_nonblocking_writes_stay_loud(self):
        for source in (
                'module top; string text; real value; initial begin '
                'text = "3.14"; value <= text.atoreal(); end endmodule',
                'module top; string text; real value; initial begin '
                'text = "3.14"; value = #1 text.atoreal(); end endmodule'):
            design = lower(source)
            kinds = [node.get("sv_kind") for node in nodes(design)]
            self.assertTrue("AssignmentExpression:target" in kinds
                            or "IntraAssignment:type-or-effects" in kinds)


if __name__ == "__main__":
    unittest.main()
