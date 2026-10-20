"""Integral assignment-pattern correspondence (IEEE 1800-2023 §10.9)."""
from pathlib import Path
import unittest

import extract
from test_bit_queries import lower, nodes
from test_division import symbolic
from test_elaborated_generate import walls

# SYNTHETIC-ORACLE: tests=AssignmentPatterns | origin=spec | authority=IEEE-1800-2023#10.9 | map=packing:bound-member-widths;keyed:declared-index-order;positional:source-order;replication:constant-shape;effects:source-census;invalid:frontend-barrier;cells:original-storage;symbolic:existing-admission


def patterns(design):
    return [n for n in nodes(design) if n.get('assignment_pattern_lowered')]


def literals(pattern):
    return [n.get('bits') for n in pattern['parts']]


class AssignmentPatterns(unittest.TestCase):
    def test_integer_key_inventory_is_packed_msb_first(self):
        d = lower("module top; integer x='{31:1'b1,0:1'bz,default:'0}; endmodule")
        self.assertFalse(walls(d))
        p, = patterns(d)
        self.assertEqual(literals(p), ['1']+['0']*30+['z'])
        self.assertTrue(p['signed'])

    def test_keyed_packed_vectors_follow_both_declared_directions(self):
        for bounds, expected in (('[7:4]', ['0','x','x','1']), ('[4:7]', ['1','x','x','0'])):
            d = lower("module top; logic "+bounds+" x='{4:1'b1,7:1'b0,default:1'bx}; endmodule")
            self.assertFalse(walls(d))
            p, = patterns(d)
            self.assertEqual(literals(p), expected)

    def test_positional_packed_vector_keeps_source_order_in_both_directions(self):
        for bounds in ('[3:0]', '[0:3]'):
            d = lower("module top; logic "+bounds+" x='{1'b1,1'bx,1'bz,1'b0}; endmodule")
            self.assertFalse(walls(d))
            p, = patterns(d)
            self.assertEqual(literals(p), ['1','x','z','0'])

    def test_struct_members_follow_declaration_order_not_key_spelling(self):
        d = lower("module top; typedef struct packed{logic[2:0]a;logic[4:0]b;}T;"
                  "T x='{b:5'b10101,a:3'b110}; endmodule")
        self.assertFalse(walls(d))
        p, = patterns(d)
        self.assertEqual(literals(p), ['110','10101'])
        self.assertEqual([n['width'] for n in p['parts']], [3,5])

    def test_member_key_overrides_type_and_default_correspondence(self):
        d = lower("module top; typedef logic[3:0]N; typedef struct packed{N a;N b;logic c;}T;"
                  "T x='{N:4'h3,b:4'h9,default:1'b1};endmodule")
        self.assertFalse(walls(d))
        p, = patterns(d)
        self.assertEqual(literals(p), ['0011','1001','1'])

    def test_nested_struct_patterns_remain_recursive_values(self):
        d = lower("module top; typedef struct packed{logic a;logic b;}P;"
                  "typedef struct packed{P p;logic c;}T; T x='{p:'{1'bx,1'bz},c:1'b1};endmodule")
        self.assertFalse(walls(d))
        self.assertEqual(len(patterns(d)), 2)
        self.assertEqual(patterns(d)[0]['width'], 3)
        self.assertEqual(patterns(d)[1]['width'], 2)

    def test_replication_repeats_the_complete_element_group(self):
        d = lower("module top; localparam int N=2; logic[7:0]x='{N{1'bx,1'bz,1'b0,1'b1}};endmodule")
        self.assertFalse(walls(d))
        p, = patterns(d)
        self.assertEqual(literals(p), ['x','z','0','1']*2)

    def test_live_self_reads_in_a_whole_packed_assignment_are_preserved(self):
        d = lower("module top; typedef struct packed{logic a;logic b;}T; T x;"
                  "initial x='{a:x.b,b:x.a};endmodule")
        self.assertFalse(walls(d))
        p, = patterns(d)
        self.assertEqual([n['kind'] for n in p['parts']], ['SelectRead','SelectRead'])
        self.assertEqual({n['name'] for n in nodes(p) if n.get('kind')=='Ident'}, {'x'})

    def test_fixed_array_keyed_cells_use_declared_direction(self):
        for bounds, expected in (('[2:0]', ['0011','0010','0001']), ('[0:2]', ['0001','0010','0011'])):
            d = lower("module top; logic[3:0]a"+bounds+"='{0:4'h1,1:4'h2,2:4'h3};endmodule")
            self.assertFalse(walls(d))
            self.assertEqual([n['init']['bits'] for n in d['modules'][0]['decls']], expected)

    def test_fixed_array_of_struct_patterns_and_existing_self_alias_boundary(self):
        d = lower("module top; typedef struct packed{logic a;logic b;}T; T x[1:0];"
                  "initial x='{1:'{1'b1,1'b0},0:'{1'bx,1'bz}};endmodule")
        self.assertFalse(walls(d))
        self.assertEqual(len(patterns(d)), 2)
        d = lower("module top; int x[0:1];initial x='{x[1],x[0]};endmodule")
        self.assertIn('AssignmentExpression:target', walls(d))

    def test_invalid_patterns_and_redefinitions_cannot_execute(self):
        for source in ("module top; logic[3:0]x='{1'b1,1'b0};endmodule",
                       "module top;logic[3:0]x='{default:'0};logic x;endmodule",
                       "module top;logic[3:0]x='{0:1'b1,0:1'b0,default:'0};endmodule"):
            self.assertTrue(walls(lower(source, require_valid=False)))

    def test_source_effects_remain_loud_before_constant_use(self):
        d = lower("module top; int calls; logic[3:0]x; function logic f();calls++;return 1;endfunction "
                  "initial x='{default:f()};endmodule")
        self.assertIn('AssignmentPattern:effects', walls(d))
        d = lower("module top; logic[3:0]x; logic v; initial x='{default:v++};endmodule")
        self.assertIn('AssignmentPattern:effects', walls(d))

    def test_unpacked_results_and_existing_multidimensional_storage_stay_loud(self):
        d = lower("module top; logic[1:0][3:0]x='{4'ha,4'h5};endmodule")
        self.assertIn('VariableSymbol:range', walls(d))
        d = lower("module top; typedef struct{int a;int b;}T;T x='{1,2};endmodule")
        self.assertTrue(walls(d))

    def test_element_limit_refuses_rather_than_truncating(self):
        d = lower("module top;logic[1024:0]x='{default:'0};endmodule")
        self.assertIn('AssignmentPattern:element-limit', walls(d))
        self.assertFalse(patterns(d))

    def test_symbolic_packed_pattern_admission_is_unchanged(self):
        d = symbolic("module divider;logic[3:0]x='{1'b1,1'b0,1'bx,1'bz};endmodule")
        self.assertTrue(any('AssignmentPatternExpression' in str(w) for w in walls(d)))
        self.assertFalse(patterns(d))

    def test_authored_runnable_sources_are_admitted(self):
        root=Path(__file__).resolve().parents[2]/'Examples/system-verilog/assignment_patterns'
        for name in ('keys','structs','runtime','arrays','replicated'):
            self.assertFalse(walls(lower((root/(name+'.sv')).read_text())),name)


if __name__ == '__main__':
    unittest.main()
