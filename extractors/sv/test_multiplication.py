"""Integral runtime multiplication and context-sized extraction."""
from pathlib import Path
import json
import tempfile
import unittest

import extract
from test_bit_queries import lower, nodes


def products(design):
    return [node for node in nodes(design)
            if node.get("kind") == "Binary" and node.get("op") == "*"]


def symbolic(source):
    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / "multiplier.sv"
        output_path = Path(directory) / "multiplier.sv.json"
        source_path.write_text(source)
        extract.process_symbolic("multiplier", [str(source_path)], [], str(output_path))
        return json.loads(output_path.read_text())["design"]


class Multiplication(unittest.TestCase):
    def test_reference_fixtures_are_admitted(self):
        sources = sorted((Path(__file__).resolve().parents[2] /
                          "harness/sv/multiplication").glob("*.sv"))
        self.assertEqual(len(sources), 4)
        for source in sources:
            with self.subTest(source=source.name):
                design = lower(source.read_text())
                self.assertTrue(products(design))
                self.assertFalse(any(node.get("kind") == "Unsupported"
                                     for node in nodes(design)))

    def test_runtime_operands_are_not_folded(self):
        design = lower("module top; logic [7:0] left, right, result; "
                       "initial result = left * right; endmodule")
        product = products(design)[0]
        self.assertEqual(product["width"], 8)
        self.assertEqual([product[side]["kind"] for side in ("left", "right")],
                         ["Ident", "Ident"])

    def test_destination_context_widens_operands_before_product(self):
        design = lower("module top; logic [3:0] left, right; logic [7:0] result; "
                       "initial result = left * right; endmodule")
        product = products(design)[0]
        self.assertEqual(product["width"], 8)
        self.assertEqual([product[side]["kind"] for side in ("left", "right")],
                         ["Resize", "Resize"])

    def test_signed_operands_extend_but_mixed_operands_zero_extend(self):
        design = lower("module top; logic signed [3:0] left, right; "
                       "logic [3:0] unsigned_value; logic [7:0] result; "
                       "initial begin result = left * right; "
                       "result = left * unsigned_value; end endmodule")
        signed_product, mixed_product = products(design)
        self.assertEqual([signed_product[side]["kind"] for side in ("left", "right")],
                         ["SignedResize", "SignedResize"])
        self.assertEqual([mixed_product[side]["kind"] for side in ("left", "right")],
                         ["Resize", "Resize"])

    def test_narrow_destination_truncates_after_product(self):
        design = lower("module top; logic [7:0] left, right; logic [3:0] result; "
                       "initial result = left * right; endmodule")
        value = design["modules"][0]["processes"][0]["body"]["value"]
        self.assertEqual(value["kind"], "Resize")
        self.assertEqual(value["width"], 4)
        self.assertEqual(products(design)[0]["width"], 8)

    def test_compound_multiplication_reads_its_original_target(self):
        design = lower("module top; logic [7:0] product, factor; "
                       "initial product *= factor; endmodule")
        product = products(design)[0]
        self.assertEqual(product["left"]["name"], "product")
        self.assertEqual(product["right"]["name"], "factor")

    def test_selected_compound_target_stays_loud(self):
        design = lower("module top; logic [7:0] product; logic [3:0] factor; "
                       "initial product[3:0] *= factor; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_invalid_compilation_cannot_hide_multiplication(self):
        design = lower("module top; logic [7:0] left, right, result; "
                       "initial result = left * right; initial missing = 1; endmodule",
                       require_valid=False)
        self.assertTrue(products(design))
        self.assertIn("Multiplication:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_symbolic_runtime_product_keeps_variable_operands(self):
        design = symbolic("module multiplier #(parameter W = 8) "
                          "(input logic [W-1:0] left, right, "
                          "output logic [W-1:0] product); "
                          "assign product = left * right; endmodule")
        product = products(design)[0]
        self.assertEqual([product[side]["kind"] for side in ("left", "right")],
                         ["Ident", "Ident"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_symbolic_constant_product_keeps_parameter_references(self):
        design = symbolic("module multiplier #(parameter W = 8); "
                          "localparam P = W * 2; logic [P-1:0] value; endmodule")
        product = products(design)[0]
        self.assertEqual(product["left"]["kind"], "ParamRef")
        self.assertEqual(product["left"]["name"], "W")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
