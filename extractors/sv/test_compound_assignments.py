"""Bound scalar compound assignments, before constant folding."""
import json
from pathlib import Path
import tempfile
import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def extract_source(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def body(source):
    design = extract_source("module top; logic [3:0] value, delta; "
                           "initial begin " + source + " end endmodule")
    return design["modules"][0]["processes"][0]["body"]["stmts"]


class CompoundAssignments(unittest.TestCase):
    def test_scalar_binary_compounds_lower_to_binary_reads(self):
        statements = body("value = 4'b0001; delta = 4'b0011; "
                           "value += delta; value -= 4'b0001; "
                           "value &= 4'b0110; value |= 4'b1000; "
                           "value ^= 4'b0011;")
        compounds = statements[2:]
        self.assertEqual([statement["kind"] for statement in compounds],
                         ["BlockingAssign"] * 5)
        self.assertEqual([statement["value"]["op"] for statement in compounds],
                         ["+", "-", "&", "|", "^"])
        self.assertTrue(all(statement["value"]["left"]["kind"] == "Ident"
                            for statement in compounds))

    def test_unsupported_compound_operator_stays_loud(self):
        statements = body("value *= delta;")
        self.assertEqual(statements[0]["sv_kind"], "AssignmentExpression:compound")

    def test_conversion_wrapped_compound_width_stays_loud(self):
        statement = body("value += 1;")[0]
        self.assertEqual(statement["kind"], "Unsupported")
        self.assertEqual(statement["sv_kind"],
                         "AssignmentExpression:compound-width")

    def test_nested_binary_rhs_is_retained(self):
        statement = body("value += (delta + 4'b0001);")[0]
        right = statement["value"]["right"]
        self.assertEqual(right["kind"], "Binary")
        self.assertEqual(right["left"]["name"], "delta")
        self.assertEqual(right["right"]["bits"], "0001")

    def test_two_state_destination_uses_existing_squash(self):
        design = extract_source("module top; bit [3:0] value; "
                                "logic [3:0] delta; "
                                "initial value &= delta; endmodule")
        statement = design["modules"][0]["processes"][0]["body"]
        self.assertEqual(statement["value"]["kind"], "Squash2")
        self.assertEqual(statement["value"]["operand"]["op"], "&")

    def test_selected_compound_target_stays_loud(self):
        design = extract_source("module top; logic [3:0] value; "
                                "initial value[0] += 1'b1; endmodule")
        statement = design["modules"][0]["processes"][0]["body"]
        self.assertEqual(statement["sv_kind"], "AssignmentExpression:compound")

    def test_symbolic_compound_assignments_stay_loud(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "top.sv"
            output = Path(directory) / "top.sv.json"
            source.write_text("module top; logic [3:0] value, delta; "
                              "initial value += delta; endmodule")
            extract.process_symbolic("top", [str(source)], [], str(output))
            design = json.loads(output.read_text())["design"]
            statement = design["modules"][0]["processes"][0]["body"]
            self.assertEqual(statement["sv_kind"],
                             "AssignmentExpression:compound")


if __name__ == "__main__":
    unittest.main()
