"""IEEE 7.12.3: intrinsic-width folds and symbol-bound with expressions."""
from pathlib import Path
import unittest
import extract
from test_bit_queries import lower,nodes
from test_elaborated_generate import walls
from test_division import symbolic
# REFERENCE: 20342820699402559b0932d2 24.03-s004 2026-10-20 | tests=automatic | source=Examples/system-verilog/array_reductions/automatic.sv@sha256:0a84696634115fb9899678a93e4b0b1fa0aad2bb09d43e7c804c74a4a4e15d2f | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
# REFERENCE: 27f88ac7e35aa6420a9a16cc 24.03-s004 2026-10-20 | tests=certificate | source=Examples/system-verilog/array_reductions/certificate.sv@sha256:2a712f2333e66dde2a1f17f0adc36cf244cab94b273564c85ff2cc389c7d2397 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
# REFERENCE: 358a4cf082915bd4bd384e91 24.03-s004 2026-10-20 | tests=effect | source=Examples/system-verilog/array_reductions/effect.sv@sha256:49d0492c529634c3636ea44e8a499623994c947aa977dc5b32b85f23113165e5 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
# REFERENCE: 1bcd6d321b3b28a57409497c 24.03-s004 2026-10-20 | tests=iterator_index | source=Examples/system-verilog/array_reductions/iterator_index.sv@sha256:48e2c7d3c948b0a0a622930ac5048ccf17d094c833bc484ef9a7306ae2529e4c | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
# REFERENCE: 19fe8d2083e458b2a9c0abe2 24.03-s004 2026-10-20 | tests=nested | source=Examples/system-verilog/array_reductions/nested.sv@sha256:a9755dd4e0b09ea7a29a0c9aedf91444e42681a4791970e20e605366eeeeab57 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
# REFERENCE: d98ddf292ef8f4197be1b0bd 24.03-s004 2026-10-20 | tests=rules | source=Examples/system-verilog/array_reductions/rules.sv@sha256:6fa2f5b8b605ba88d7424382532150b6edc04ad8ce80e63f83277149b05f0477 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
# REFERENCE: bf01345e37e9a61d5be348c4 24.03-s004 2026-10-20 | tests=structure | source=Examples/system-verilog/array_reductions/structure.sv@sha256:7e29e2cf3e0decae5679f41ba0cec29525b6e3b44b40a502fbc5e1fbde6ce557 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
# REFERENCE: 5560a8c58d2746d40128c5b3 24.03-s004 2026-10-20 | tests=timing | source=Examples/system-verilog/array_reductions/timing.sv@sha256:b8e49ae2b87e6ea172fe13f2d3f219ae83a6695cb0d61dc244c1b390b4f44cf0 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/array_reductions/README.md#fixed-array-reduction-methods
# SYNTHETIC-ORACLE: tests=binding-and-admission | origin=spec | authority=docs/sv-array-reductions.md#fixed-array-reduction-methods | map=width:intrinsic-element-or-with;binding:actual-symbol;depth:balanced-pure-operators;barriers:storage-effects-types-invalid;certificates:actual-parsed-assignment



def fixture(name):
    return lower(Path('Examples/system-verilog/array_reductions',name+'.sv').read_text())


class ArrayReductions(unittest.TestCase):
    def test_five_methods_lower_to_existing_operators(self):
        d=fixture('rules')
        self.assertFalse(walls(d))
        self.assertEqual({n['array_reduction_lowered'] for n in nodes(d)
                          if 'array_reduction_lowered' in n},{'sum','product','and','or','xor'})

    def test_call_width_is_independent_of_assignment_context(self):
        d=lower('module top;logic[3:0] a[3];longint y;initial y=a.sum();endmodule')
        roots=[n for n in nodes(d) if n.get('array_reduction_lowered')=='sum']
        self.assertEqual([n['width'] for n in roots],[4])

    def test_with_cast_determines_combining_width(self):
        d=lower("module top;logic[3:0] a[3];int y;initial y=a.sum() with (int'(item));endmodule")
        roots=[n for n in nodes(d) if n.get('array_reduction_lowered')=='sum']
        self.assertEqual([n['width'] for n in roots],[32])

    def test_explicit_iterator_binding_preserves_surrounding_item(self):
        d=fixture('rules')
        self.assertFalse(walls(d))
        self.assertIn('item',{n.get('name') for n in nodes(d) if n.get('kind')=='Ident'})
        self.assertFalse(any(n.get('name','').startswith('$foreach:') for n in nodes(d)))

    def test_hierarchy_cells_and_packed_fields_remain_bound(self):
        self.assertFalse(walls(fixture('structure')))

    def test_automatic_cell_lifetime_and_nba_path_are_preserved(self):
        self.assertFalse(walls(fixture('timing')))
        self.assertFalse(walls(fixture('automatic')))

    def test_single_cell_is_an_expression_without_extra_identity(self):
        d=lower('module top;logic[4:0] a[7:7];logic[4:0] y;initial y=a.product();endmodule')
        root=next(n for n in nodes(d) if n.get('array_reduction_lowered'))
        self.assertEqual((root['kind'],root['name']),('Ident','a[7]'))

    def test_large_fixed_array_has_balanced_expression_depth(self):
        d=lower('module top;logic[7:0] a[1024];logic[7:0] y;initial y=a.sum();endmodule')
        self.assertFalse(walls(d))
        root=next(n for n in nodes(d) if n.get('array_reduction_lowered'))
        def depth(n):
            return 1+max(depth(n['left']),depth(n['right'])) if n['kind']=='Binary' else 0
        self.assertEqual(depth(root),10)

    def test_nested_with_reductions_restore_both_iterator_bindings(self):
        d=lower("module top;int a[2],b[2],y;initial y=a.sum(x) with (b.sum(z) with (z+x));endmodule")
        self.assertFalse(walls(d))
        self.assertFalse(extract._ARRAY_REDUCTION_VALUES)

    def test_nested_fixed_array_rows_reduce_to_scalar(self):
        source = ("module top; logic [7:0] m[2][2] = "
                  "'{ '{5,10}, '{15,20} }; logic [7:0] y; "
                  "initial y = m.sum with (item.sum with (item)); endmodule")
        d = lower(source)
        self.assertFalse(walls(d))
        lowered = [n for n in nodes(d) if n.get('array_reduction_lowered')]
        self.assertGreaterEqual(len(lowered), 2)
        self.assertTrue(all(n.get('width') == 8 for n in lowered))

    def test_nested_reduction_fixture_is_admitted(self):
        d = fixture('../nested_2d_reductions/nested_2d_reductions')
        self.assertFalse(walls(d))

    def test_dynamic_struct_field_reduction_is_admitted(self):
        source = ("module top; typedef struct { int id; int weight; } item_t; "
                  "item_t items[]; int total; initial begin items=new[2]; "
                  "items[0]='{id:1,weight:10}; items[1]='{id:2,weight:20}; "
                  "total=items.sum() with (item.weight); end endmodule")
        d = lower(source)
        self.assertFalse(walls(d))
        self.assertTrue(any(n.get('array_reduction_lowered') == 'sum'
                            for n in nodes(d)))

    def test_dynamic_array_index_reduction_is_admitted(self):
        source = ("module top; int values[]; int total; initial begin "
                  "values = new[3]('{10,20,30}); "
                  "total = values.sum with (item + item.index()); end endmodule")
        d = lower(source)
        self.assertFalse(walls(d))
        self.assertTrue(any(n.get('array_reduction_index') for n in nodes(d)))

    def test_with_effects_remain_loud(self):
        self.assertIn('ArrayReduction:storage-or-effects',walls(fixture('effect')))

    def test_iterator_index_query_uses_sampled_position(self):
        d = fixture('iterator_index')
        self.assertFalse(walls(d))
        self.assertTrue(any(n.get('array_reduction_index') for n in nodes(d)))

    def test_empty_dynamic_storage_uses_zero_identity(self):
        d=lower('module top;int a[];int y,z;initial begin '
                 'y=a.sum(); z=a.product(); end endmodule')
        self.assertFalse(walls(d))
        self.assertEqual(
            {n.get('array_reduction_lowered') for n in nodes(d)
             if n.get('empty_array_reduction')}, {'sum', 'product'})

    def test_discarded_reductions_reuse_value_lowering(self):
        d = lower('module top; logic [3:0] a[2]; initial begin '
                   'a[0]=1; a[1]=2; a.sum(); a.product(); a.and(); '
                   'a.or(); a.xor(); $display("PASS"); $finish; end endmodule')
        methods = [node.get('array_reduction_statement') for node in nodes(d)
                   if node.get('array_reduction_statement')]
        self.assertEqual(methods, ['sum', 'product', 'and', 'or', 'xor'])
        self.assertFalse(walls(d))

    def test_dynamic_storage_with_unknown_extent_remains_loud(self):
        d=lower('module top;int a[];int n;int y;'
                 'initial begin a=new[n]; y=a.sum(); end endmodule')
        self.assertIn('ArrayReduction:storage-or-effects',walls(d))

    def test_invalid_redefinition_retains_compilation_barrier(self):
        d=lower('module top;int a[2],y;int y;initial y=a.sum();endmodule',require_valid=False)
        self.assertIn('ArrayReduction:invalid-compilation',walls(d))

    def test_symbolic_surface_is_unchanged(self):
        d=symbolic('module divider;logic[7:0] a[2];logic[7:0] y;initial y=a.sum();endmodule')
        self.assertTrue(walls(d))
