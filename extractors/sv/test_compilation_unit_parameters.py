"""Compilation-unit parameters are elaboration metadata in legacy mode."""

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


class CompilationUnitParameters(unittest.TestCase):
    def test_parameter_is_metadata_and_reference_is_literal(self):
        design = lower(
            "parameter int WIDTH = 8; module top; "
            "logic [WIDTH-1:0] value = 8'hA5; "
            "initial begin $display(\"%0d\", WIDTH); "
            "$display(\"%0h\", value); end endmodule")
        unsupported = [node for node in nodes(design)
                       if node.get("kind") == "Unsupported"]
        self.assertFalse(unsupported)
        calls = [node for node in nodes(design)
                 if node.get("kind") == "SysCall"]
        self.assertEqual(calls[0]["args"][0]["kind"], "Literal")
        self.assertEqual(calls[0]["args"][0]["bits"], "0" * 28 + "1000")

    def test_compilation_unit_variable_remains_loud(self):
        design = lower(
            "int runtime_value; parameter int WIDTH = 8; "
            "module top; logic [WIDTH-1:0] value; endmodule")
        self.assertIn("VariableSymbol", [node.get("sv_kind")
                                          for node in nodes(design)
                                          if node.get("kind") == "Unsupported"])


if __name__ == "__main__":
    unittest.main()
