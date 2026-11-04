"""Shape checks for the ConfigBlock repricing instrument."""
import unittest

from config_reprice import config_shape


class ConfigReprice(unittest.TestCase):
    def test_design_and_binding_shapes(self):
        self.assertEqual(
            config_shape(True, 0, [("default", "liblist"),
                                   ("cell", "use")]),
            "design+default-liblist+cell-use")

    def test_localparam_and_missing_design_are_visible(self):
        self.assertEqual(config_shape(False, 2, []),
                         "no-design+localparam")

    def test_unknown_rule_kind_stays_in_telemetry(self):
        self.assertEqual(config_shape(True, 0, [("future", "unknown")]),
                         "design+future-unknown")


if __name__ == "__main__":
    unittest.main()
