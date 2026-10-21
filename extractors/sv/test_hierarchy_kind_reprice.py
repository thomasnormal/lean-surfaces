"""Shape checks for the non-module hierarchy repricing instrument."""
import unittest

from hierarchy_kind_reprice import definition_kind, instance_shape


class HierarchyKindReprice(unittest.TestCase):
    def test_definition_kind_uses_frontend_definition_metadata(self):
        class Definition:
            definitionKind = "DefinitionKind.Program"

        class Body:
            definition = Definition()
            portList = []

        class Instance:
            body = Body()
            portConnections = []

        self.assertEqual(definition_kind(Instance()), "Program")

    def test_shape_distinguishes_top_portless_program(self):
        class Definition:
            definitionKind = "DefinitionKind.Program"

        class Body:
            definition = Definition()
            portList = []

        class Instance:
            body = Body()
            portConnections = []

        instance = Instance()
        self.assertEqual(instance_shape(instance, instance), {
            "kind": "Program",
            "position": "top",
            "ports": 0,
            "connections": (),
        })

    def test_shape_retains_interface_port_connection_kinds(self):
        class Definition:
            definitionKind = "DefinitionKind.Interface"

        class Port:
            pass

        class Body:
            definition = Definition()
            portList = [Port()]

        class Expression:
            kind = "ExpressionKind.NamedValue"

        class Connection:
            expression = Expression()

        class Instance:
            body = Body()
            portConnections = [Connection()]

        self.assertEqual(instance_shape(Instance(), object()), {
            "kind": "Interface",
            "position": "child",
            "ports": 1,
            "connections": ("NamedValue",),
        })


if __name__ == "__main__":
    unittest.main()
