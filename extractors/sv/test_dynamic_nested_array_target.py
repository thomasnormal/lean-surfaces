"""Dynamic outer-array targets over fixed unpacked inner dimensions."""
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


class DynamicNestedArrayTarget(unittest.TestCase):
    def test_dynamic_outer_and_inner_selectors_lower_to_flat_cells(self):
        design = lower(
            "module top; logic [3:0] value[][0:1]; int outer, inner; "
            "initial begin value = new[2]; outer = 1; inner = 0; "
            "value[outer][inner] = 4'ha; end endmodule")
        self.assertFalse(any(node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))
        names = [node["target"]["name"]
                 for node in nodes(design)
                 if node.get("kind") == "BlockingAssign"
                 and node.get("target", {}).get("name", "").startswith("value[")]
        self.assertEqual(names,
                         ["value[0][0]", "value[0][1]",
                          "value[1][0]", "value[1][1]"])

    def test_unsampled_dynamic_outer_array_stays_loud(self):
        design = lower(
            "module top; logic [3:0] value[][0:1]; int outer; "
            "initial begin outer = 1; value[outer][0] = 4'ha; end endmodule")
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_nested_dynamic_inner_dimension_stays_loud(self):
        design = lower(
            "module top; logic [3:0] value[][]; int outer, inner; "
            "initial begin value = new[2]; outer = 1; inner = 0; "
            "value[outer][inner] = 4'ha; end endmodule")
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
