"""Width-preserving integral signing functions and their consuming contexts."""
import unittest
from pathlib import Path

import extract
from test_bit_queries import lower, nodes, query_source


def signing_nodes(design):
    return [node for node in nodes(design) if node.get("signing_cast")]


class SigningCalls(unittest.TestCase):
    def test_reference_fixtures_are_admitted(self):
        sources = sorted((Path(__file__).resolve().parents[2] /
                          "harness/sv/signing_calls").glob("*.sv"))
        self.assertEqual(len(sources), 4)
        for source in sources:
            with self.subTest(source=source.name):
                design = lower(source.read_text())
                self.assertTrue(signing_nodes(design))
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_same_width_calls_preserve_operands_and_replace_signedness(self):
        source = ("module top; logic [7:0] value; logic signed [7:0] signed_value; "
                  "initial begin value = $unsigned(signed_value); "
                  "signed_value = $signed(value); end endmodule")
        casts = signing_nodes(lower(source))
        self.assertEqual([node["kind"] for node in casts], ["Ident", "Ident"])
        self.assertEqual([node["width"] for node in casts], [8, 8])
        self.assertEqual([node.get("signed", False) for node in casts], [False, True])

    def test_signed_widening_and_unsigned_zero_extension(self):
        source = ("module top; logic [3:0] value; logic [7:0] result; "
                  "initial begin result = $signed(value); "
                  "result = $unsigned(value); end endmodule")
        statements = lower(source)["modules"][0]["processes"][0]["body"]["stmts"]
        self.assertEqual([statement["value"]["kind"] for statement in statements],
                         ["SignedResize", "Resize"])
        self.assertEqual([statement["value"]["width"] for statement in statements], [8, 8])

    def test_consuming_comparisons_use_call_signedness(self):
        source = ("module top; logic [3:0] value; logic result; initial begin "
                  "result = $signed(value) < 4'sd0; "
                  "result = $unsigned(value) < 4'sd0; end endmodule")
        statements = lower(source)["modules"][0]["processes"][0]["body"]["stmts"]
        self.assertEqual([statement["value"]["op"] for statement in statements], ["s<", "<"])

    def test_display_argument_signedness_follows_call(self):
        design = lower(query_source("$signed(value), $unsigned(value)",
                                    "logic signed [7:0] value; "))
        call = next(node for node in nodes(design) if node.get("kind") == "SysCall")
        self.assertEqual(call["arg_signed"], [True, False])

    def test_discarded_integral_casts_are_inert(self):
        source = ("module top; logic [7:0] value; initial begin "
                  "$signed(8'hff); $unsigned(value); "
                  "$display(\"PASS\"); end endmodule")
        design = lower(source)
        self.assertEqual([node.get("signing_statement") for node in nodes(design)
                          if node.get("signing_statement")],
                         ["$signed", "$unsigned"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_two_state_call_does_not_squash_four_state_result(self):
        source = ("module top; bit [3:0] value; logic [3:0] result; "
                  "initial result = $signed(value); endmodule")
        value = lower(source)["modules"][0]["processes"][0]["body"]["value"]
        self.assertEqual(value["kind"], "Ident")
        self.assertEqual(value["signing_cast"], "$signed")

    def test_nested_calls_keep_the_outer_signedness(self):
        design = lower(query_source("$unsigned($signed(value)), $signed($unsigned(value))",
                                    "logic signed [7:0] value; "))
        casts = signing_nodes(design)
        self.assertEqual([node.get("signed", False) for node in casts], [False, True])
        self.assertEqual([node["name"] for node in casts], ["value", "value"])

    def test_bits_of_pure_signing_call_is_admitted(self):
        design = lower(query_source("$bits($signed(value)), $bits($unsigned(value))",
                                    "logic [7:0] value; "))
        queries = [node for node in nodes(design) if node.get("fixed_bits_query")]
        self.assertEqual([int(node["bits"], 2) for node in queries], [8, 8])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_pure_calls_are_admitted_in_case_and_selected_assignment(self):
        source = ("module top; logic [3:0] value, result; initial begin "
                  "case ($signed(value)) 4'sd0: result = 0; "
                  "default: result = 1; endcase "
                  "result[1:0] = $unsigned(value[3:2]); end endmodule")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(lower(source))))

    def test_constant_context_keeps_cast_provenance(self):
        source = "module top; logic [7:0] result; initial result = $signed(4'b1001); endmodule"
        design = lower(source)
        self.assertEqual(signing_nodes(design)[0]["bits"], "1001")
        self.assertEqual(design["modules"][0]["processes"][0]["body"]["value"]["kind"],
                         "SignedResize")

    def test_bad_compilation_cannot_hide_admitted_casts(self):
        source = ("module top; logic [3:0] value; logic [7:0] result; "
                  "initial result = $signed(4'b1001); initial undeclared = 1; endmodule")
        design = lower(source, require_valid=False)
        self.assertTrue(signing_nodes(design))
        self.assertIn("SigningCast:invalid-compilation", [node.get("sv_kind") for node in nodes(design)])

    def test_nonintegral_and_effectful_operands_stay_loud(self):
        for declaration, expression in (
            ("real value; ", "$signed(value)"),
            ("logic [7:0] value [2]; ", "$unsigned(value)"),
            ("logic [7:0] value; ", "$signed(value++)"),
            ("logic [7:0] value; ", "$unsigned((value = 1))"),
            ("logic [7:0] value; ", "$bits($signed(value++))"),
        ):
            with self.subTest(expression=expression):
                design = lower(query_source(expression, declaration), require_valid=False)
                self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_invalid_signatures_stay_loud(self):
        for expression in ("$signed()", "$unsigned(1, 2)", "$signed(undeclared)"):
            with self.subTest(expression=expression):
                design = lower(query_source(expression), require_valid=False)
                self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_escaped_user_function_is_not_a_signing_call(self):
        source = ("module top; function automatic int \\$signed (int value); "
                  "return value; endfunction initial $display(\"%0d\", \\$signed (7)); endmodule")
        self.assertFalse(signing_nodes(lower(source)))

    def test_symbolic_path_keeps_its_existing_cast_nodes(self):
        from pyslang.ast import Compilation
        from pyslang.syntax import SyntaxTree

        source = "module top; logic [3:0] value, result; initial result = $signed(value); endmodule"
        tree = SyntaxTree.fromText(source)
        compilation = Compilation()
        compilation.addSyntaxTree(tree)
        compilation.getAllDiagnostics()
        extract._SOURCE_BYTES = source.encode()
        extract._SYM = extract.SymCtx(compilation, tree.sourceManager, {})
        try:
            design = extract.convert_design(tree.sourceManager, compilation)
        finally:
            extract._SYM = None
        casts = [node for node in nodes(design) if node.get("kind") == "Cast"]
        self.assertEqual(len(casts), 1)
        self.assertTrue(casts[0]["signed"])
        self.assertFalse(signing_nodes(design))


if __name__ == "__main__":
    unittest.main()
