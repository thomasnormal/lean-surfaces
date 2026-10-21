"""Shape checks for the ClassType:ClassType repricing instrument."""
import unittest

from class_use_reprice import class_features, class_header_shape


class ClassUseReprice(unittest.TestCase):
    def test_class_headers(self):
        self.assertEqual(class_header_shape("virtual class Packet;"),
                         "virtual class")
        self.assertEqual(class_header_shape("class Child extends Base;"),
                         "class extends")
        self.assertEqual(class_header_shape("interface class I;"),
                         "interface class")

    def test_features_overlap(self):
        source = ("class C; rand int x; constraint c { x > 0; } "
                  "virtual interface V vif; covergroup cg; "
                  "function void f; endfunction endclass")
        self.assertEqual(class_features(source),
                         ("methods", "constraints", "random-fields",
                          "virtual-interface", "covergroups"))

    def test_extends_and_unknown_span(self):
        self.assertEqual(class_features("class Child extends Base; endclass"),
                         ("extends",))
        self.assertEqual(class_header_shape("not a declaration span"),
                         "other class span")
        self.assertEqual(class_features("class C; endclass"), ())


if __name__ == "__main__":
    unittest.main()
