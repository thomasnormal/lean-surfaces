"""Shape checks for package-initializer repricing."""
import unittest

from package_initializer_reprice import package_initializer_features


class PackageInitializerReprice(unittest.TestCase):
    def test_qualified_arithmetic_reference(self):
        self.assertEqual(
            package_initializer_features("y = p1::x * 2"),
            ("runtime-reference", "qualified-reference", "arithmetic",
             "multiple-identifiers"),
        )

    def test_multiple_identifiers(self):
        self.assertEqual(package_initializer_features("z = x + y"),
                         ("runtime-reference", "arithmetic",
                          "multiple-identifiers"))

    def test_literal_is_not_a_runtime_reference(self):
        self.assertEqual(package_initializer_features("x = 10"), ())


if __name__ == "__main__":
    unittest.main()
