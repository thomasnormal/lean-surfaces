"""Self-determined integral replication (IEEE 1800-2023 §11.4.12.1)."""
from pathlib import Path
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic
from test_elaborated_generate import walls

# SYNTHETIC-ORACLE: tests=Replication | origin=spec | authority=IEEE-1800-2023#11.4.12.1 | map=groups:complete-source-order;context:self-determined-before-resize;zero:empty-member-with-pure-operand;effects:source-census;invalid:frontend-barrier;resources:bounded-envelope;symbolic:retained-replication


def replications(design):
    return [n for n in nodes(design) if n.get('replication_lowered')]


class Replication(unittest.TestCase):
    def test_complete_groups_keep_source_order_and_four_state_bits(self):
        d=lower("module top;logic[7:0]x={2{2'b10,2'bxz}};endmodule")
        self.assertFalse(walls(d))
        r,=replications(d)
        self.assertEqual(r['replication_count'],2)
        self.assertEqual(r['width'],8)
        self.assertEqual([[p['bits'] for p in group['parts']] for group in r['parts']], [['10','xz']]*2)

    def test_operand_width_is_self_determined_before_assignment_resize(self):
        d=lower("module top;logic signed[3:0]n=-1;logic signed[11:0]x={2{n}};endmodule")
        self.assertFalse(walls(d))
        r,=replications(d)
        self.assertEqual(r['width'],8)
        self.assertEqual([group['width'] for group in r['parts']],[4,4])
        self.assertFalse(r.get('signed',False))
        self.assertTrue(any(n.get('kind')=='Resize' and n.get('width')==12 for n in nodes(d)))

    def test_constant_parameter_expression_count_is_exact(self):
        d=lower("module top;parameter int N=2;logic[11:0]x={(N+1){4'ha}};endmodule")
        self.assertFalse(walls(d))
        r,=replications(d)
        self.assertEqual(r['replication_count'],3)
        self.assertEqual(r['width'],12)

    def test_zero_member_is_empty_without_retyping_other_operands(self):
        d=lower("module top;logic[7:0]x={{0{4'b1xz0}},8'ha5};endmodule")
        self.assertFalse(walls(d))
        r,=replications(d)
        self.assertEqual(r['width'],0)
        self.assertEqual(r['parts'],[])
        self.assertEqual([n['width'] for n in nodes(d) if n.get('kind')=='Concat'],[8,0])

    def test_nested_replication_preserves_each_group(self):
        d=lower("module top;logic[11:0]x={2{{3{2'b10}}}};endmodule")
        self.assertFalse(walls(d))
        self.assertEqual([r['replication_count'] for r in replications(d)],[2,3,3])

    def test_byte_string_literal_uses_the_existing_bit_encoding(self):
        d=lower('module top;logic[15:0]x={2{"A"}};endmodule')
        self.assertFalse(walls(d))
        r,=replications(d)
        self.assertEqual([g['parts'][0]['bits'] for g in r['parts']],['01000001']*2)

    def test_live_reads_and_captured_nba_keep_their_source(self):
        d=lower("module top;logic[1:0]a;logic[5:0]x;initial x<={3{a}};endmodule")
        self.assertFalse(walls(d))
        r,=replications(d)
        self.assertEqual([g['parts'][0]['name'] for g in r['parts']],['a']*3)
        self.assertTrue(any(n.get('kind')=='NonblockingAssign' for n in nodes(d)))

    def test_composes_with_typed_patterns_cases_and_fixed_cells(self):
        d=lower("module top;logic[3:0]a[0:1];initial begin a='{default:{2{2'b10}}};"
                "case({2{2'b10}}){2{2'b10}}:$display(\"selected\");endcase end endmodule")
        self.assertFalse(walls(d))
        self.assertTrue(replications(d))

    def test_effects_stay_loud_for_positive_and_zero_counts(self):
        for count in (0,2):
            d=lower("module top;logic a;logic[3:0]x;initial x={{"+str(count)+"{a++}},1'b1};endmodule")
            self.assertIn('Replication:effects',walls(d))

    def test_zero_count_does_not_discard_unsupported_pure_operands(self):
        d=lower("module top;logic[7:0]x={{0{{$rtoi(2.0)}}},8'ha5};endmodule")
        # Unsupported math calls must remain visible even at count zero.
        self.assertTrue(walls(d))

    def test_nonconstant_negative_unknown_and_standalone_zero_are_loud(self):
        for expression in ("{n{1'b1}}","{-1{1'b1}}","{1'bx{1'b1}}","{0{1'b1}}"):
            d=lower('module top;int n;logic[7:0]x='+expression+';endmodule',require_valid=False)
            self.assertTrue(walls(d))

    def test_redefinition_warning_is_a_design_barrier(self):
        d=lower("module top;logic[3:0]x={2{2'b10}};logic x;endmodule",require_valid=False)
        self.assertIn('Replication:invalid-compilation',walls(d))

    def test_copy_limit_refuses_without_emitting_a_prefix(self):
        d=lower("module top;logic[1024:0]x={1025{1'b1}};endmodule")
        self.assertIn('Replication:copy-limit',walls(d))
        self.assertFalse(replications(d))

    def test_nested_copy_cost_is_bounded_before_envelope_materialization(self):
        d=lower("module top;logic[65535:0]x={256{{256{1'b1}}}};endmodule")
        self.assertIn('Replication:expansion-limit',walls(d))
        self.assertFalse(replications(d))

    def test_dynamic_string_replication_keeps_its_existing_type_boundary(self):
        d=lower('module top;string s="ab";string t={2{s}};endmodule')
        self.assertTrue(walls(d))

    def test_symbolic_replication_is_unchanged(self):
        d=symbolic("module divider #(parameter int N=2);logic[7:0]x={N{4'ha}};endmodule")
        self.assertTrue(any(n.get('kind')=='Repl' for n in nodes(d)))
        self.assertFalse(replications(d))

    # REFERENCE: e120f6565740df8b0fcb3de5 24.03-s004 2026-10-20 | tests=test_unsized_based_xz_widening_differs_from_sized_literals_and_values | source=Examples/system-verilog/replication/based.sv@sha256:64f8bfef9e338e70508eb36e99850d0c6e82eb659f244cbfa7219b71a81d0d35 | top=top | args=["-ii_val"] | map=Examples/system-verilog/replication/README.md#integral-replication
    def test_unsized_based_xz_widening_differs_from_sized_literals_and_values(self):
        for token, expected in (("'hx",'x'*85),("'hz",'z'*85),("32'hx",'0'*53+'x'*32)):
            d=lower("module top;logic[84:0]x="+token+";endmodule")
            self.assertFalse(walls(d))
            self.assertEqual(d['modules'][0]['decls'][0]['init']['bits'],expected)
        d=lower("module top;logic[84:0]x=85'('hx);bit[84:0]y='hz;endmodule")
        self.assertFalse(walls(d))
        self.assertEqual(d['modules'][0]['decls'][0]['init']['bits'],'x'*85)
        self.assertEqual(d['modules'][0]['decls'][1]['init']['operand']['bits'],'z'*85)

    def test_incorrect_bound_elaboration_constants_are_refused(self):
        for declaration in ("localparam logic[84:0]P='hx;",
                            "typedef enum logic[84:0]{E=85'('hx)}T;",
                            "if('hx===85'hx)begin:a logic x;end else begin:b logic y;end"):
            self.assertIn('UnsizedBasedLiteral:constant-context',walls(lower('module top; '+declaration+' endmodule')))

    def test_count_does_not_consume_an_incorrect_frontend_constant(self):
        d=lower("module top;logic[1:0]x={(('hx===85'hx)+1){1'b1}};endmodule")
        self.assertIn('Replication:constant-count',walls(d))

    def test_authored_runnable_sources_are_admitted(self):
        root=Path(__file__).resolve().parents[2]/'Examples/system-verilog/replication'
        for name in ('groups','contexts','zero','strings','runtime','composition','based'):
            self.assertFalse(walls(lower((root/(name+'.sv')).read_text())),name)


if __name__=='__main__':
    unittest.main()
