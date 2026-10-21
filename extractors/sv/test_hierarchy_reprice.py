"""Shape checks for the hierarchy-port repricing instrument."""
import unittest

from hierarchy_reprice import instance_shape


class HierarchyReprice(unittest.TestCase):
    def test_fully_connected_port_instance(self):
        class Port:
            direction = "PortDirection.In"

        class Body:
            portList = [Port()]

        class Instance:
            body = Body()
            portConnections = [type("Connection", (), {
                "expression": type("Expression", (), {
                    "kind": "ExpressionKind.NamedValue"
                })()
            })()]

        self.assertEqual(instance_shape(Instance()),
                         ("connected", ("In",), ("NamedValue",)))

    def test_partial_and_unconnected_instances_are_distinct(self):
        class Port:
            direction = "PortDirection.Out"

        class Body:
            portList = [Port(), Port()]

        def instance(expressions):
            class Instance:
                body = Body()
                portConnections = [type("Connection", (), {
                    "expression": expression
                })() for expression in expressions]
            return Instance()

        empty = type("Expression", (), {"kind": "ExpressionKind.Empty"})
        self.assertEqual(instance_shape(instance([None, None]))[0],
                         "unconnected")
        self.assertEqual(instance_shape(instance([None, empty()]))[0],
                         "partial")

    def test_connection_kind_does_not_guess_semantics(self):
        class Port:
            direction = "PortDirection.InOut"

        class Body:
            portList = [Port()]

        class Instance:
            body = Body()
            portConnections = [type("Connection", (), {
                "expression": type("Expression", (), {
                    "kind": "ExpressionKind.RangeSelect"
                })()
            })()]

        self.assertEqual(instance_shape(Instance())[2], ("RangeSelect",))


if __name__ == "__main__":
    unittest.main()
