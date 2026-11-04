"""Shape checks for invalid hierarchy repricing."""
import unittest

from hierarchy_invalid_reprice import hierarchy_features


class InvalidHierarchyReprice(unittest.TestCase):
    def test_mixed_parameter_assignment(self):
        self.assertEqual(
            hierarchy_features("vdff #(10, .delay(15)) bad();"),
            ("mixed-ordered-and-named-parameters",))

    def test_localparam_override(self):
        self.assertEqual(
            hierarchy_features("module c; localparam int W=1; endmodule "
                               "module t; c #(.W(2)) x(); endmodule"),
            ("localparam-override",))

    def test_hierarchical_type_operator(self):
        self.assertEqual(
            hierarchy_features("var type(u.x) v;"),
            ("hierarchical-type-operator-reference",))


if __name__ == "__main__":
    unittest.main()
