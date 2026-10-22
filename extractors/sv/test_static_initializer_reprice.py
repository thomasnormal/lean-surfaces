"""Shape checks for the residual static-initializer instrument."""
import unittest

from static_initializer_reprice import static_initializer_features


class StaticInitializerReprice(unittest.TestCase):
    def test_random_initializer_keeps_effect_and_dependency(self):
        labels = static_initializer_features(
            "bit [3:0] number = $urandom & 15;", "")
        self.assertEqual(labels[:3], (
            "static-initializer", "random-or-randomize", "system-function"))
        self.assertIn("bitwise-expression", labels)

    def test_cast_and_real_conversion(self):
        labels = static_initializer_features(
            "int i = int'(2.0 * 3.5);", "")
        self.assertIn("type-or-size-cast", labels)
        self.assertIn("real-conversion", labels)

    def test_macro_and_package_reads_remain_source_dependent(self):
        labels = static_initializer_features(
            "word_t local_v = value;", "`define X value\nimport pkg::value;")
        self.assertIn("macro-expansion", labels)
        self.assertIn("package-or-qualified-read", labels)
        self.assertIn("runtime-dependent-read", labels)


if __name__ == "__main__":
    unittest.main()
