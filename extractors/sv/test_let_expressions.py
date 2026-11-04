"""IEEE 11.12: bound expression templates and lexical storage identities."""
from pathlib import Path
import unittest
import extract
from test_bit_queries import lower, nodes
from test_elaborated_generate import walls
from test_division import symbolic

# REFERENCE: b03b0a3b73727ba781dd4d7a 24.03-s004 2026-10-20 | tests=binding | source=Examples/system-verilog/let_expressions/binding.sv@sha256:75ce296763a0c23b0ef9aa989e3703fe5d00bf7d43fab02f455ca52eb435f57e | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# REFERENCE: dd359c6ae6a63f1283f53c17 24.03-s004 2026-10-20 | tests=call | source=Examples/system-verilog/let_expressions/call.sv@sha256:e9b97df59c248d2b2e253878951977cf9a5bf25073957843fb4010c3b62a50f3 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# REFERENCE: d131ac0601814c4465fbf855 24.03-s004 2026-10-20 | tests=certificate | source=Examples/system-verilog/let_expressions/certificate.sv@sha256:17f5597e37b25f42a237a95ab6d29ab7cde82ccc2015fbe4acbb5d538e9be59a | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# REFERENCE: 528421725d2b3a50177f573c 24.03-s004 2026-10-20 | tests=effects | source=Examples/system-verilog/let_expressions/effects.sv@sha256:5ee81e71294b540e08ce72971f9e8f2482b6b531752765aa650292c6fbdcca1c | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# REFERENCE: 9e29b5de4163af92fb63e6a5 24.03-s004 2026-10-20 | tests=local | source=Examples/system-verilog/let_expressions/local.sv@sha256:bc065ab862053db508afdd460895367de43089665db2f06e3b06d1dce0987b98 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# REFERENCE: f15f532a1ceb1ee3a1fdb244 24.03-s004 2026-10-20 | tests=program | source=Examples/system-verilog/let_expressions/program.sv@sha256:af52324ce6c3eac8b76f2e61a0cdec2f568c56490ee8e0c1cd7c0be8ced82911 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# REFERENCE: 49383f3eb729b467587c94dd 24.03-s004 2026-10-20 | tests=sizing | source=Examples/system-verilog/let_expressions/sizing.sv@sha256:2cc1da1a70aa06e76b0dc57276c9bb08b85f50c0376af42f5e4bf5974c00c6a2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# REFERENCE: 9c5fd762733e0f5f2bbc4b92 24.03-s004 2026-10-20 | tests=structure | source=Examples/system-verilog/let_expressions/structure.sv@sha256:19ead2ca28de495bf38017cab0cceff22a670236fb44513d68ce7d439694b140 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# REFERENCE: 60a678378f8e897c3abebf09 24.03-s004 2026-10-20 | tests=timing | source=Examples/system-verilog/let_expressions/timing.sv@sha256:ee50869ba77f49dfd5ba65ec75840593d9e740d5f9c2def33caddaaa86f7fed2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# REFERENCE: f177e74e6c20640c68fc43ff 24.03-s004 2026-10-20 | tests=unused | source=Examples/system-verilog/let_expressions/unused.sv@sha256:ab0dffd96ad1882b35fa5ac036f95d2cd6b2d3219a24ed8a754e4a568e0ae017 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/let_expressions/README.md#let-expressions
# SYNTHETIC-ORACLE: tests=admission-and-binding | origin=spec | authority=docs/sv-let-expressions.md#let-expressions | map=binding:actual-symbol;order:declaration-before-use;invalid:whole-design;nonmodule:scheduling-barrier;typed-default:structural-only


def fixture(name):
    return lower(Path("Examples/system-verilog/let_expressions", name + ".sv").read_text())


class LetExpressions(unittest.TestCase):
    def test_supported_scope_forms_use_existing_nodes(self):
        for name in ["binding", "certificate", "local", "sizing", "structure", "timing", "unused"]:
            with self.subTest(name=name):
                self.assertFalse(walls(fixture(name)))

    def test_declaration_scope_survives_same_spelled_locals(self):
        design = fixture("binding")
        locals_ = [n["name"] for n in nodes(design) if n.get("kind") == "Var" and n.get("static_local_storage")]
        self.assertEqual(len(locals_), 2)
        self.assertEqual(len(set(locals_)), 2)
        self.assertTrue(all(name.startswith("$local:") for name in locals_))
        self.assertIn("x", {n.get("name") for n in nodes(design) if n.get("kind") == "Ident"})

    def test_actual_certificate_keeps_module_binding(self):
        d = fixture("certificate")
        store = next(n for n in nodes(d) if n.get("kind") == "BlockingAssign"
                     and n["target"].get("name") == "result")
        self.assertEqual(store["value"]["kind"], "Binary")
        self.assertEqual(store["value"]["left"]["name"], "held")
        self.assertEqual(store["value"]["right"]["name"], "actual")

    def test_unused_actual_does_not_create_a_function_activation(self):
        self.assertFalse(walls(fixture("unused")))
        self.assertFalse(any(n.get("kind") == "Call" for n in nodes(fixture("unused"))))

    def test_effectful_expansion_retains_existing_refusal(self):
        self.assertIn("UnaryExpression:Postincrement", walls(fixture("effects")))

    def test_subroutine_in_expansion_is_not_guessed(self):
        self.assertIn("CallExpression", walls(fixture("call")))

    def test_nonmodule_roots_keep_named_scheduling_barrier(self):
        self.assertIn("Hierarchy:module-kind", walls(fixture("program")))
        self.assertIn("Hierarchy:module-kind", walls(lower("interface ifc;let v=1;endinterface module top;ifc u();endmodule")))

    def test_unused_redefinition_keeps_compilation_barrier(self):
        d = lower("module top;let v=1;let v=2;endmodule", require_valid=False)
        self.assertIn("Let:invalid-compilation", walls(d))

    def test_recursive_template_is_not_admitted(self):
        d = lower("module top;let r(a)=r(a);int y;initial y=r(2);endmodule", require_valid=False)
        self.assertIn("Let:invalid-compilation", walls(d))

    def test_forward_use_is_rejected_even_when_frontend_expands_it(self):
        for name in ["later", "/* comment */ later", "\\later "]:
            d = lower("module top;int y;initial y=" + name + "(1);let later(a)=a+1;endmodule")
            self.assertIn("Let:used-before-declaration", walls(d))

    def test_macro_expansion_retains_declaration_order(self):
        d = lower('`define CALL later(1)\nmodule top;int y;initial y=`CALL;let later(a)=a+1;endmodule')
        self.assertIn("Let:used-before-declaration", walls(d))

    def test_forward_use_in_nested_template_is_rejected(self):
        d = lower("module top;let first(a)=later(a);let later(a)=a+1;int y;initial y=first(1);endmodule")
        self.assertIn("Let:used-before-declaration", walls(d))

    def test_lexical_shadow_does_not_invent_a_forward_use(self):
        d = lower('module top;initial begin int v;v=1;$display("%0d",v);end let v=2;endmodule')
        self.assertFalse(walls(d))

    def test_source_cannot_alias_generated_local_storage(self):
        s = "module top;int x;initial begin int x;x=3;end endmodule"
        name = next(n["name"] for n in nodes(lower(s)) if n.get("kind") == "Var" and n.get("static_local_storage"))
        d = lower(s.replace("endmodule", "int \\" + name + " ;endmodule"))
        self.assertIn("LexicalBinding:storage-collision", walls(d))

    def test_binding_environment_is_restored(self):
        fixture("binding")
        self.assertFalse(extract._ELAB_BINDINGS)

    def test_symbolic_mode_stays_loud(self):
        self.assertTrue(walls(symbolic("module divider;int x,y;let twice(a)=a+a;initial y=twice(x);endmodule")))

    def test_typed_and_default_forms_are_only_structural_checks(self):
        # Independent simulator rejects these two syntax forms; no runtime
        # expected transcript is asserted here. See the source-bound receipts.
        self.assertFalse(walls(fixture("typed")))
        self.assertFalse(walls(fixture("defaults")))
