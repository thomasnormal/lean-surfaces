"""Shape checks for empty-member repricing."""
import unittest

from empty_member_reprice import empty_member_features


class EmptyMemberReprice(unittest.TestCase):
    def test_soft_keyword(self):
        self.assertEqual(
            empty_member_features('`begin_keywords "1800-2012"\nreg [7:0] soft;'),
            ("soft-keyword-under-begin-keywords",))

    def test_primitive_array_without_name(self):
        self.assertEqual(
            empty_member_features("and [3:0] (out, in, 1'b1);"),
            ("primitive-array-without-instance-name",))

    def test_nested_attribute(self):
        self.assertEqual(
            empty_member_features("(* my_attr = (* nested *) 1 *) int x;"),
            ("nested-attribute-expression",))


if __name__ == "__main__":
    unittest.main()
