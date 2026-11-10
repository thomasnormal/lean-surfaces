"""Slang scope identity, resolved lifetime and symbolic local types (§6.21)."""
import json
from pathlib import Path
import tempfile
import unittest

import extract
from test_bit_queries import nodes


def symbolic(source, retained=False):
    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / "top.sv"
        output_path = Path(directory) / "top.sv.json"
        source_path.write_text(source)
        extract.process_symbolic("top", [str(source_path)], [], str(output_path),
                                 retain_proc_rewrites=retained)
        return json.loads(output_path.read_text())["design"]


def locals_in(design):
    return [n for n in nodes(design) if n.get("kind") == "LocalDecl"]


class LocalScopeMetadata(unittest.TestCase):
    def test_anonymous_scopes_keep_distinct_source_identity(self):
        design = symbolic("module top(input logic clk); "
                          "always @(posedge clk) begin logic t; t=1; end "
                          "always @(negedge clk) begin logic t; t=0; end endmodule", True)
        a, b = locals_in(design)
        # Slang deliberately omits anonymous block names from printed paths.
        # Those paths must not be treated as unique declaration identities.
        self.assertEqual(a["lexical_path"], b["lexical_path"])
        self.assertNotEqual(a["span"], b["span"])
        blocks = [n for n in nodes(design) if n.get("kind") == "Block"]
        self.assertEqual([n["scope"]["name"] for n in blocks], ["", ""])
        self.assertNotEqual(blocks[0]["span"], blocks[1]["span"])
        self.assertEqual(design["modules"][0]["decls"], [])

    def test_block_without_retained_locals_keeps_existing_fields(self):
        design = symbolic("module top(input logic clk, d, output logic q); "
                          "always_ff @(posedge clk) begin : sample q<=d; end endmodule", True)
        block, = [n for n in nodes(design) if n.get("kind") == "Block"]
        self.assertNotIn("scope", block)

    def test_shadowed_names_keep_separate_parser_scope_identities(self):
        design = symbolic("module top(input logic clk); "
                          "always_ff @(posedge clk) begin : outer "
                          "logic [3:0] t; t=1; begin : inner "
                          "logic [3:0] t; t=2; end end endmodule", True)
        declarations = locals_in(design)
        self.assertEqual([d["name"] for d in declarations], ["t", "t"])
        self.assertEqual([d["lexical_path"] for d in declarations],
                         ["top.outer.t", "top.outer.inner.t"])
        scopes = [n["scope"] for n in nodes(design)
                  if n.get("kind") == "Block" and n.get("scope")]
        self.assertEqual([s["name"] for s in scopes], ["outer", "inner"])
        self.assertTrue(all(s["default_lifetime"] == "static" for s in scopes))
        self.assertEqual(design["modules"][0]["decls"], [])

    def test_resolved_lifetime_includes_module_default_and_explicit_override(self):
        for module_lifetime, implicit in [("", "static"), ("automatic", "automatic")]:
            with self.subTest(module_lifetime=module_lifetime):
                design = symbolic(f"module {module_lifetime} top(input logic clk); "
                                  "always @(posedge clk) begin : sample "
                                  "logic a; static logic s; automatic logic b; "
                                  "a=1; s=0; b=1; end endmodule", True)
                declarations = locals_in(design)
                self.assertEqual([d["lifetime"] for d in declarations],
                                 [implicit, "static", "automatic"])
                body = design["modules"][0]["processes"][0]["body"]
                self.assertEqual(body["scope"]["default_lifetime"], implicit)

    def test_symbolic_type_survives_the_resolved_default_width(self):
        design = symbolic("module top #(parameter int W=7)(input logic clk); "
                          "always_ff @(posedge clk) begin : sample "
                          "logic signed [W-1:0] s; bit [W-1:0] b; "
                          "s='1; b='0; end endmodule", True)
        s, b = locals_in(design)
        self.assertTrue(s["signed"])
        self.assertFalse(s["two_state"])
        self.assertTrue(b["two_state"])
        for d in [s, b]:
            self.assertEqual(d["width"], 7)
            self.assertEqual(d["decl_type"]["kind"], "PackedType")
            self.assertTrue(any(n.get("kind") == "ParamRef" and n.get("name") == "W"
                                for n in nodes(d["decl_type"])))

    def test_ordinary_symbolic_path_also_retains_metadata(self):
        design = symbolic("module top(input logic clk, input logic [3:0] d, "
                          "output logic [3:0] q); always_ff @(posedge clk) "
                          "begin : capture logic [3:0] t; t=d; q<=t; end endmodule")
        declaration, = locals_in(design)
        self.assertEqual(declaration["lifetime"], "static")
        self.assertEqual(declaration["lexical_path"], "top.capture.t")
        self.assertEqual(declaration["decl_type"]["resolved"], 4)

    def test_initializer_is_retained_once_on_its_declaration(self):
        design = symbolic("module top(input logic clk); always @(posedge clk) "
                          "begin : sample static logic [3:0] s=4'h9; "
                          "automatic logic [3:0] a=4'h6; s=a; end endmodule", True)
        s, a = locals_in(design)
        self.assertEqual(s["lifetime"], "static")
        self.assertEqual(a["lifetime"], "automatic")
        self.assertEqual(s["init"]["bits"], "1001")
        self.assertEqual(a["init"]["bits"], "0110")
        self.assertFalse(any(n.get("kind") == "NonblockingAssign" for n in nodes(design)))

    def test_metadata_is_deterministic_and_has_no_object_addresses(self):
        source = ("module top(input logic clk); always @(posedge clk) "
                  "begin : sample logic x; x=0; end endmodule")
        first = symbolic(source, True)
        self.assertEqual(first, symbolic(source, True))
        self.assertNotIn("0x", json.dumps(first))


if __name__ == "__main__":
    unittest.main()
