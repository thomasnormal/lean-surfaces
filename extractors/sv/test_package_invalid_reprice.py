"""Shape checks for invalid-package repricing."""
import unittest

from package_invalid_reprice import package_invalid_features


class PackageInvalidReprice(unittest.TestCase):
    def test_repeated_timeunit(self):
        self.assertEqual(package_invalid_features(
            "package p; timeunit 1ns; timeunit 1ps; endpackage"),
            ("repeated-timeunit",))

    def test_import_collision(self):
        self.assertEqual(package_invalid_features(
            "package p; import a::x; import b::x; endpackage"),
            ("import", "multiple-imports"))

    def test_export_without_import(self):
        self.assertEqual(package_invalid_features(
            "package p; export q::x; endpackage"),
            ("export", "export-without-import"))


if __name__ == "__main__":
    unittest.main()
