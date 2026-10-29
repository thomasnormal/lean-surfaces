"""Admission checks for plain, un-driven charge-storage nets."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def lower(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class TriRegNet(unittest.TestCase):
    def test_un_driven_plain_trireg_starts_high_impedance(self):
        module = lower("module top; trireg n; endmodule")["modules"][0]
        self.assertEqual(module["decls"][0]["init"]["bits"], "z")
        self.assertFalse(any(node.get("sv_kind") == "NetSymbol:TriReg"
                             for node in nodes(module)))

    def test_un_driven_vector_trireg_repeats_high_impedance(self):
        module = lower("module top; trireg [3:0] bus; endmodule")["modules"][0]
        self.assertEqual(module["decls"][0]["init"]["bits"], "zzzz")

    def test_charge_delay_and_driver_stay_loud(self):
        module = lower(
            "module top; trireg (small) charged; "
            "trireg #(1,2,3) delayed; trireg initialized = 1'b0; "
            "trireg driven; assign driven = 1'b1; endmodule")["modules"][0]
        walls = [node.get("sv_kind") for node in nodes(module)
                 if node.get("kind") == "Unsupported"]
        self.assertEqual(walls.count("NetSymbol:TriReg"), 4)


if __name__ == "__main__":
    unittest.main()
