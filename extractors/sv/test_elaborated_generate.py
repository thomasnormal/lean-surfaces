"""Elaborated scope storage and constants, IEEE 1800-2023 clauses 6/23/27."""
from pathlib import Path
import unittest

import extract
from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=ElaboratedGenerate | origin=spec | authority=IEEE-1800-2023#27 | map=branches:instantiated-members-only;loops:per-entry-localparam-and-storage;hierarchy:bound-live-declarations;constants:elaborated-integral-values;locals:declaration-identity;temporaries:scope-qualified;invalid:frontend-barrier;initialization:order-oracle-required;symbolic:retained-generate


def walls(design):
    return [n.get('sv_kind') for n in nodes(design) if n.get('kind') == 'Unsupported']


def declarations(design):
    return design['modules'][0]['decls']


class ElaboratedGenerate(unittest.TestCase):
    def test_only_live_if_else_chain_members_are_emitted(self):
        d = lower('module top; parameter int N=2; '
                  'if(N==1)begin:a string bad; end else if(N==2)begin:b int x=4; end '
                  'else begin:c string bad; end endmodule')
        self.assertFalse(walls(d))
        self.assertEqual(len(declarations(d)), 1)
        self.assertEqual(declarations(d)[0]['generated_scope'][-1], 'b')

    def test_case_generate_selection_and_unconditional_nesting(self):
        d = lower('module top; case(2) 1:begin:a string bad; end '
                  '2:begin:b logic x; end default:begin:c string bad; end endcase '
                  'begin:outer begin:inner logic x; end end endmodule')
        self.assertFalse(walls(d))
        self.assertEqual(len(declarations(d)), 2)
        self.assertNotEqual(*[n['name'] for n in declarations(d)])

    def test_loop_entries_have_distinct_storage_and_exact_implicit_localparams(self):
        d = lower('module top; for(genvar i=-1;i<=1;i++)begin:g int x=i; end endmodule')
        self.assertFalse(walls(d))
        self.assertEqual(len({n['name'] for n in declarations(d)}), 3)
        literals = [n['bits'] for n in nodes(d) if n.get('kind') == 'Literal']
        self.assertEqual(literals, ['1'*32, '0'*32, '0'*31+'1'])

    def test_descending_and_nested_loop_entries(self):
        d = lower('module top; genvar i; for(i=2;i>=0;i--)begin:g '
                  'for(genvar j=0;j<2;j++)begin:h int x=i+j; end end endmodule')
        self.assertFalse(walls(d))
        self.assertEqual(len({n['name'] for n in declarations(d)}), 6)

    def test_zero_count_has_no_runtime_member(self):
        d = lower('module top; for(genvar i=0;i<0;i++)begin:g string bad; end endmodule')
        self.assertFalse(walls(d))
        self.assertFalse(declarations(d))

    def test_top_and_generated_hierarchical_reads_and_stores_bind_the_same_slot(self):
        d = lower('module top; int x; if(1)begin:g int x; '
                  'initial begin top.x=1; top.g.x=2; x=3; end end endmodule')
        names = [n['name'] for n in nodes(d) if n.get('kind') == 'Ident']
        self.assertFalse(walls(d))
        self.assertEqual(names[0], 'x')
        self.assertEqual(names[1], names[2])
        self.assertNotEqual(names[0], names[1])

    def test_integral_parameter_values_are_exact_and_have_no_runtime_slot(self):
        d = lower('module top; parameter logic[3:0] X=4\'b10xz; localparam int N=-2; '
                  'initial $display("%b %0d",X,top.N); endmodule')
        self.assertFalse(walls(d))
        self.assertFalse(declarations(d))
        self.assertEqual([n['bits'] for n in nodes(d) if n.get('kind') == 'Literal'], ['10xz', '1'*31+'0'])

    def test_generated_import_does_not_reallocate_package_storage(self):
        d = lower('package P; int x; endpackage module top; '
                  'for(genvar i=0;i<2;i++)begin:g import P::x; initial x=i; end endmodule')
        self.assertFalse(walls(d))
        self.assertEqual([n['name'] for n in declarations(d)], ['$package:1:P:x'])
        self.assertEqual({n['name'] for n in nodes(d) if n.get('kind') == 'Ident'}, {'$package:1:P:x'})

    def test_nonintegral_and_type_parameters_remain_loud(self):
        for declaration in ('parameter real N=1.5;', 'parameter string S="value";', 'parameter type T=int;'):
            d = lower('module top; '+declaration+' endmodule')
            self.assertTrue(walls(d))

    def test_repeated_procedural_locals_and_arrays_use_scope_identity(self):
        d = lower('module top; for(genvar i=0;i<2;i++)begin:g '
                  'initial begin automatic int x=i; automatic int a[0:1]; x=2; a[0]=x; end '
                  'end endmodule')
        self.assertFalse(walls(d))
        local = [n['name'] for n in nodes(d) if n.get('kind') == 'LocalDecl']
        self.assertEqual(len(local), len(set(local)))
        self.assertEqual(len(local), 6)

    def test_repeated_intra_assignment_capture_names_are_distinct(self):
        d = lower('module top; for(genvar i=0;i<2;i++)begin:g int x; initial x=#2 i; end endmodule')
        self.assertFalse(walls(d))
        captures = [n['name'] for n in nodes(d) if n.get('kind') == 'LocalDecl']
        self.assertEqual(len(set(captures)), 2)

    def test_repeated_foreach_cursor_and_iterators_are_distinct(self):
        d = lower('module top; for(genvar g=0;g<2;g++)begin:row int a[0:1]; '
                  'initial foreach(a[i]) a[i]=i; end endmodule')
        # Dynamic array-index stores retain their existing boundary; cursor
        # storage itself must still be distinct across copies of the source.
        local = [n['name'] for n in nodes(d) if n.get('kind') == 'LocalDecl']
        self.assertEqual(len(local), len(set(local)))
        self.assertEqual(len(local), 4)

    def test_hierarchical_fixed_array_cells_and_alias_checks(self):
        d = lower('module top; if(1)begin:g int a[0:1]; end '
                  'initial begin g.a[0]=3; $display("%0d",g.a[0]); end endmodule')
        self.assertFalse(walls(d))
        d = lower('module top; if(1)begin:g int a[0:1]; '
                  'initial a[0:1]=\'{a[1],a[0]}; end endmodule')
        self.assertIn('AssignmentExpression:target', walls(d))

    def test_runtime_static_initializer_dependencies_stay_loud(self):
        for source in ('module top; int a=3; if(1)begin:g int b=a; end endmodule',
                       'module top; if(1)begin:g int a=3; end int b=g.a; endmodule'):
            self.assertIn('Generate:initializer-order', walls(lower(source)))

    def test_invalid_source_and_redefinition_warnings_are_design_barriers(self):
        for source in ('module top; int runtime_value; if(runtime_value)begin:g int x; end endmodule',
                       'module top; if(1)begin:g int x; end initial absent=1; endmodule',
                       'module top; parameter int N=1; int x; int x; endmodule'):
            self.assertIn('Elaboration:invalid-compilation', walls(lower(source, require_valid=False)))

    def test_active_unsupported_members_stay_loud_and_portless_hierarchy_lowers(self):
        d = lower('module top; if(1)begin:g function int f(); return 1; endfunction end endmodule')
        self.assertNotIn('SubroutineSymbol:Subroutine', walls(d))
        d = lower('module child; int x; endmodule module top; child u(); initial u.x=1; endmodule')
        self.assertFalse(walls(d))
        self.assertTrue(d['modules'][0]['hierarchy_lowered'])

    def test_generated_storage_collision_cannot_capture_a_source_binding(self):
        source = 'module top; if(1)begin:g int x; end '
        name = declarations(lower(source+'endmodule'))[0]['name']
        d = lower(source+'int \\'+name+' ; endmodule')
        self.assertIn('Generate:storage-collision', walls(d))

    def test_expansion_limit_refuses_without_truncation(self):
        d = lower('module top; for(genvar i=0;i<1025;i++)begin:g logic x; end endmodule')
        self.assertIn('Generate:instance-limit', walls(d))
        self.assertFalse(declarations(d))

    def test_context_is_restored_and_repeated_extraction_is_identical(self):
        source = 'module top; for(genvar i=0;i<2;i++)begin:g int x=i; end endmodule'
        d = lower(source)
        lower('module top; int x; endmodule')
        self.assertEqual(d, lower(source))
        self.assertEqual(extract._ELAB_BINDINGS, {})
        self.assertEqual(extract._ELAB_PARAMETERS, set())
        self.assertEqual(extract._ELAB_HIER_VALUES, set())
        self.assertEqual(extract._ELAB_CURRENT_SCOPE, '')

    def test_symbolic_path_still_retains_generate_and_parameter_nodes(self):
        d = symbolic('module divider #(parameter int N=2); '
                     'for(genvar i=0;i<N;i++)begin:g logic x; end endmodule')
        self.assertTrue(any(n.get('kind') == 'GenerateFor' for n in nodes(d)))
        self.assertFalse(any(n.get('elaboration_lowered') for n in nodes(d)))

    def test_authored_runnable_sources_are_admitted(self):
        root = Path(__file__).resolve().parents[2]/'Examples/system-verilog/elaborated_generate'
        for name in ('scopes','loops','locals','captures','imports','parameters'):
            self.assertFalse(walls(lower((root/(name+'.sv')).read_text())), name)

    def test_generated_constant_indexed_part_select_targets_are_windows(self):
        d = lower("module top; wire [7:0] values; "
                   "for(genvar i=0;i<4;i++) begin:g "
                   "assign values[i*2 +: 2] = i; end endmodule")
        self.assertNotIn("AssignmentExpression:target", walls(d))
        assignments = [node for node in nodes(d) if node.get("kind") == "Assign"]
        self.assertEqual(len(assignments), 4)
        self.assertEqual([node["target"]["index"]["bits"][-4:]
                          for node in assignments], ["0000", "0010", "0100", "0110"])

        d = lower("module top; wire [7:0] values; "
                   "for(genvar i=0;i<4;i++) begin:g "
                   "assign values[7-i*2 -: 2] = i; end endmodule")
        self.assertNotIn("AssignmentExpression:target", walls(d))
        assignments = [node for node in nodes(d) if node.get("kind") == "Assign"]
        self.assertEqual([node["target"]["index"]["bits"][-4:]
                          for node in assignments], ["0111", "0101", "0011", "0001"])

    def test_generated_constant_packed_targets_are_continuous_windows(self):
        d = lower('module top; wire [3:0] chain; assign chain[0]=1\'b1; '
                  'for(genvar i=0;i<3;i++) begin:g '
                  'assign chain[i+1]=chain[i]; end endmodule')
        self.assertFalse(walls(d))
        assignments = [node for node in nodes(d) if node.get('kind') == 'Assign']
        self.assertEqual(len(assignments), 4)
        self.assertEqual([node['target']['index']['bits'][-2:]
                          for node in assignments], ['00', '01', '10', '11'])


if __name__ == '__main__':
    unittest.main()
