"""IEEE 6.21 / 9.3: static storage and automatic sequential entries."""
from pathlib import Path
import unittest
import extract
from test_bit_queries import lower,nodes
from test_elaborated_generate import walls
from test_division import symbolic

# REFERENCE: 7deb2ae9ce23b3daa158a048 24.03-s004 2026-10-20 | tests=automatic | source=Examples/system-verilog/static_locals/automatic.sv@sha256:74119694a29fe12d0f61f9f2e4c0e09d218efceba416b4e8bb9dca7940416a78 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: a474b88404d946bd9c175b3c 24.03-s004 2026-10-20 | tests=certificate | source=Examples/system-verilog/static_locals/certificate.sv@sha256:a30bce69093252b7575e14be45e9f905c8ad55c6d79bf9fdd9f41d0ff3689e04 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: 92ad75893d727250b88b982a 24.03-s004 2026-10-20 | tests=default_lifetime | source=Examples/system-verilog/static_locals/default_lifetime.sv@sha256:6e767758354f37fd5dcaf0870316446f4672462fccebd13204749e0019f6ceff | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: d5b996840a9241012d0c6493 24.03-s004 2026-10-20 | tests=initializer_effect | source=Examples/system-verilog/static_locals/initializer_effect.sv@sha256:b86e3915122d0f39b3da881afd30d97dc0e8eae0137934dbf02d0c819411aca2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: 776555f02dea92c46ced95b5 24.03-s004 2026-10-20 | tests=initializer_order | source=Examples/system-verilog/static_locals/initializer_order.sv@sha256:03e197775515f1206d8ca6c2aa92735d698ee6a3c07a7c659cf6bb6e3077132a | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: 255f3bee71bd2fb0fa23be5b 24.03-s004 2026-10-20 | tests=initializer_read | source=Examples/system-verilog/static_locals/initializer_read.sv@sha256:b38e50c1ad1551e64dbd459e00b4e9581135bd03d063be3ecbd8ad4c043259d5 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: c33d70fdad4993c446d887a3 24.03-s004 2026-10-20 | tests=nba | source=Examples/system-verilog/static_locals/nba.sv@sha256:ba6b1c518c4b7c5ef49bb492e0c6478805d6cb235468690cafc002eec1f8305e | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: f2acc5a16b42767004a1df2d 24.03-s004 2026-10-20 | tests=preentry | source=Examples/system-verilog/static_locals/preentry.sv@sha256:6e134cef86fa23267206140df38e8b25227a17e73cf4f7200b5b27fb9e162a0b | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: e99e93c829e313a6bd95e3c1 24.03-s004 2026-10-20 | tests=reentry | source=Examples/system-verilog/static_locals/reentry.sv@sha256:fd5c1b3d38f16a2a3ca9ef257b7d1c43d80e0edbd787d9d40d357130e97f1d9b | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: 63d03789ee75d95c9c60c270 24.03-s004 2026-10-20 | tests=shadow | source=Examples/system-verilog/static_locals/shadow.sv@sha256:643d3494bd9e12cdadcb5af3a20c07be3753d8cf68c7789ce0e89409dda750d2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: 2c18aac11282bafbc7d8e496 24.03-s004 2026-10-20 | tests=structure | source=Examples/system-verilog/static_locals/structure.sv@sha256:dfca10b91fb1b039b3ca1082fb9122343a1299a3677d753e9b193a749eb0649c | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# REFERENCE: aab68993bb563b089657e1e8 24.03-s004 2026-10-20 | tests=capture | source=Examples/system-verilog/static_locals/capture.sv@sha256:38d0fe5fbef2ae6bfdb267543ddb8978b60f9d31036d8125d04839ee9dfbcda1 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
# SYNTHETIC-ORACLE: tests=storage-and-admission | origin=spec | authority=docs/sv-procedural-lifetimes.md#procedural-variable-lifetimes | map=static:pre-process-once;automatic:per-entry;binding:declaration-identity;initializers:closed-pure;barriers:default-provenance-order-effects-invalid


def fixture(name):
    return lower(Path('Examples/system-verilog/static_locals',name+'.sv').read_text())


class ProceduralLifetimes(unittest.TestCase):
    def test_static_storage_exists_before_entry(self):
        d=fixture('preentry')
        self.assertFalse(walls(d))
        self.assertEqual({n['name'] for n in nodes(d) if n.get('static_local_storage')},
                         {'count','four','two'})
        self.assertFalse(any(n.get('kind')=='LocalDecl' for n in nodes(d)))

    def test_static_reentry_is_empty_and_automatic_reentry_is_local(self):
        d=fixture('reentry')
        self.assertFalse(walls(d))
        self.assertEqual([n['name'] for n in nodes(d) if n.get('static_local_storage')],['saved'])
        self.assertEqual([n['name'] for n in nodes(d) if n.get('automatic_scalar')],['fresh'])

    def test_named_block_reads_and_writes_keep_bound_identity(self):
        d=fixture('shadow')
        self.assertFalse(walls(d))
        names=[n['name'] for n in nodes(d) if n.get('static_local_storage')]
        self.assertEqual(len(names),2)
        self.assertEqual(len(set(names)),2)
        self.assertTrue(all(name.startswith('$local:') for name in names))

    def test_hierarchy_arrays_and_fields_share_storage(self):
        self.assertFalse(walls(fixture('structure')))

    def test_explicit_automatic_init_retains_live_entry_reads(self):
        d=fixture('automatic')
        self.assertFalse(walls(d))
        local=next(n for n in nodes(d) if n.get('automatic_scalar'))
        self.assertIn('source',{n.get('name') for n in nodes(local['init'])})

    def test_ambiguous_automatic_module_default_is_loud(self):
        self.assertIn('AutomaticLocal:default-lifetime',walls(fixture('default_lifetime')))

    def test_nba_capture_reuses_preinitialized_static_store(self):
        self.assertFalse(walls(fixture('nba')))

    def test_nonclosed_and_effectful_initializers_are_loud_before_entry(self):
        for name in ['initializer_read','initializer_effect']:
            self.assertIn('StaticLocal:initializer',walls(fixture(name)))

    def test_other_preprocess_initializer_cannot_choose_static_order(self):
        self.assertIn('StaticLocal:initializer-order',walls(fixture('initializer_order')))

    def test_never_entered_unsupported_body_still_censuses_static_initializer(self):
        d=lower('module top;int source;initial if(0) begin fork begin static int x=source;end join end endmodule')
        self.assertIn('StaticLocal:initializer',walls(d))

    def test_closed_pure_queries_and_parameters_are_initializable(self):
        d=lower('module top;parameter int P=3;initial begin static int x=P+2;static int n=$bits(int);end endmodule')
        self.assertFalse(walls(d))

    def test_static_initializer_may_read_prior_pure_static(self):
        d=lower('module top; initial begin '
                "logic [3:0] value = 4'b10xz; "
                'logic [3:0] result = value << 0; '
                'if (result === value) $display("PASS"); '
                '$finish; end endmodule')
        self.assertFalse(walls(d))
        names = [n['name'] for n in nodes(d)
                 if n.get('kind') == 'Var' and n.get('static_local_storage')]
        self.assertEqual(names, ['value', 'result'])
        result = next(n for n in nodes(d)
                      if n.get('name') == 'result'
                      and n.get('static_local_storage'))
        self.assertEqual(result['init']['left']['name'], 'value')

    def test_unqualified_environment_query_is_not_a_closed_initializer(self):
        d=lower('module top;initial begin static int x=$test$plusargs("flag");end endmodule')
        self.assertIn('StaticLocal:initializer',walls(d))

    def test_automatic_hierarchical_reference_stays_loud(self):
        d=lower('module top;initial begin:local_scope automatic int x=2;end initial $display("%0d",local_scope.x);endmodule',require_valid=False)
        self.assertTrue(walls(d))

    def test_invalid_source_keeps_preprocess_barrier(self):
        d=lower('module top;initial begin static int x=2;x=missing;end endmodule',require_valid=False)
        self.assertIn('StaticLocal:invalid-compilation',walls(d))

    def test_repeated_extraction_is_stable(self):
        text=Path('Examples/system-verilog/static_locals/shadow.sv').read_text()
        self.assertEqual(lower(text),lower(text))
        self.assertFalse(extract._ELAB_BINDINGS)

    def test_symbolic_scope_is_unchanged(self):
        self.assertTrue(walls(symbolic('module divider;initial begin:scope static int x=2;end initial $display("%0d",scope.x);endmodule')))
