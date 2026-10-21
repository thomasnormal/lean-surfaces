"""Shape checks for the primitive-instance repricing instrument."""
import unittest

from primitive_reprice import instance_shape, primitive_group, primitive_name


class PrimitiveReprice(unittest.TestCase):
    def test_primitive_name_and_group(self):
        class Instance:
            primitiveType = 'Primitive, "bufif1")'
            delay = None
            arrayName = None
            portConnections = [1, 2, 3]

        self.assertEqual(primitive_name(Instance()), "bufif1")
        self.assertEqual(primitive_group("bufif1"), "conditional gate")

    def test_instance_shape_retains_driver_features(self):
        class Instance:
            primitiveType = 'Primitive, "and")'
            delay = object()
            arrayName = "g"
            portConnections = [1, 2, 3]

        self.assertEqual(instance_shape(Instance()), {
            "primitive": "and",
            "group": "logic gate",
            "delay": True,
            "array": True,
            "connections": 3,
        })

    def test_unknown_primitive_stays_other(self):
        self.assertEqual(primitive_group("vendor_gate"), "other primitive")


if __name__ == "__main__":
    unittest.main()
