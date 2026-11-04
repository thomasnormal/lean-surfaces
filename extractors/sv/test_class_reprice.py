"""Shape checks for the ClassType repricing instrument."""
import unittest

from class_reprice import class_features, class_header_shape


class ClassReprice(unittest.TestCase):
    def test_class_headers(self):
        self.assertEqual(class_header_shape("virtual class Packet;"),
                         "virtual class")
        self.assertEqual(class_header_shape("class Child extends Base;"),
                         "class extends")
        self.assertEqual(class_header_shape("interface class I;"),
                         "interface class")

    def test_features_overlap(self):
        source = "class C; rand int x; constraint c { x > 0; } function void f; endfunction endclass"
        self.assertEqual(class_features(source), ("methods", "constraints",
                                                   "random-fields"))

    def test_unknown_span_stays_loud(self):
        self.assertEqual(class_header_shape("not a declaration span"),
                         "other class span")
        self.assertEqual(class_features("class C; endclass"), ())


if __name__ == "__main__":
    unittest.main()
