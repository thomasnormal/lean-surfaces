"""IEEE 6.24.2: conversion, enum validity and source-control placement."""
from pathlib import Path
import unittest
from test_bit_queries import lower, nodes
from test_elaborated_generate import walls
from test_division import symbolic

# REFERENCE: 0e7730bbab791e971ef72672 24.03-s004 2026-10-20 | tests=conditional | source=Examples/system-verilog/dynamic_cast/conditional.sv@sha256:89d9118dcca1c24febecb24e7c81f6936afcaf2213161d788fcae67790568bfa | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# REFERENCE: 72538893c3532a3a40c98a5c 24.03-s004 2026-10-20 | tests=control | source=Examples/system-verilog/dynamic_cast/control.sv@sha256:22caebe43141a5e12e73de25f3866f8016dc7c5e942d8265047ccec06586a707 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# REFERENCE: 70711ef71e50f92b905b84c3 24.03-s004 2026-10-20 | tests=rules | source=Examples/system-verilog/dynamic_cast/rules.sv@sha256:8f8c9d0efd54fde3155c299e0f4e3558c6d43a10746559b409336a83a1525e28 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# REFERENCE: a63f4905d24fda41bc5a69bf 24.03-s004 2026-10-20 | tests=selected | source=Examples/system-verilog/dynamic_cast/selected.sv@sha256:de26b062014cf5b52e4504925a081d39e395a6b16cd782fe69503f8ed940b02e | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# REFERENCE: f8d31e2830d3b79ac35fade6 24.03-s004 2026-10-20 | tests=source_effect | source=Examples/system-verilog/dynamic_cast/source_effect.sv@sha256:8104aca35b66cb89ce78f923baf3221c0233a3646108a72ff6dc1b595c4f50c2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# REFERENCE: 548b04125236309016eb2002 24.03-s004 2026-10-20 | tests=task_failure | source=Examples/system-verilog/dynamic_cast/task_failure.sv@sha256:a63600a4a35c4faf4cd6f7f8f70b2015357d20221629d8851a744a99d87b2f62 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# REFERENCE: 563759e330aef53817a0fe18 24.03-s004 2026-10-20 | tests=task_success | source=Examples/system-verilog/dynamic_cast/task_success.sv@sha256:99d5762c9fa25a8c44cac877815a8f91cfb8d580f97f0713c86c8cad5fef8cd4 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# REFERENCE: ecedfe9e5fd0bbb1fec98568 24.03-s004 2026-10-20 | tests=timing | source=Examples/system-verilog/dynamic_cast/timing.sv@sha256:5ad43f4ac4ec844e15185a6c66db652db1c094ae3ac24ecf3ebdd8218babeceb | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# REFERENCE: c3032fe3eacc1abe09b978a8 24.03-s004 2026-10-20 | tests=unordered | source=Examples/system-verilog/dynamic_cast/unordered.sv@sha256:d81576dc0e8c4eb1faaa725bde1c5ac32e93c8dc39459a78d76771f0e2fa32c7 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# REFERENCE: df57813163e4b8a357005397 24.03-s004 2026-10-20 | tests=certificate | source=Examples/system-verilog/dynamic_cast/certificate.sv@sha256:cde576e1db69ee705208f4bb9e4b564d9ca3100f25ce0703b81de97d341c80c7 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/dynamic_cast/README.md#dynamic-integral-casts
# SYNTHETIC-ORACLE: tests=DynamicCast-binding-and-admission | origin=spec | authority=docs/sv-dynamic-cast.md#dynamic-integral-casts | map=captures:one-converted-source;membership:bound-table;dispatch:representable-fixed-positions;task:diagnostic-refusal;contexts:effect-boundary;collision:disjoint-generated-storage;invalid:frontend-barrier;symbolic:unchanged


def fixture(name):
    return lower(Path('Examples/system-verilog/dynamic_cast', name+'.sv').read_text())


class DynamicCast(unittest.TestCase):
    def test_live_sources_and_tables_survive_extraction(self):
        d = fixture('certificate')
        self.assertFalse(walls(d))
        captures = [n for n in nodes(d) if n.get('kind')=='LocalDecl' and n.get('automatic_cast')]
        self.assertEqual(len(captures), 2)
        self.assertEqual(captures[1]['init']['operand']['name'], 'source')
        self.assertEqual(captures[1]['width'], 4)
        self.assertFalse(any(n.get('kind')=='DynamicCastExpr' for n in nodes(d)))

    def test_named_x_and_z_members_are_exact_patterns(self):
        d = fixture('rules')
        patterns = {n['bits'] for n in nodes(d) if n.get('kind')=='Literal'}
        self.assertTrue({'x1','z0'} <= patterns)
        self.assertTrue(any(n.get('kind')=='Squash2' for n in nodes(d)))

    def test_logical_operands_have_conditional_preludes(self):
        d = fixture('control')
        self.assertFalse(walls(d))
        self.assertGreater(len([n for n in nodes(d) if n.get('kind')=='If']), 6)

    def test_selected_destinations_reuse_cell_and_packed_stores(self):
        d = fixture('selected')
        self.assertFalse(walls(d))
        targets = [n['target'] for n in nodes(d) if n.get('kind')=='BlockingAssign']
        self.assertTrue(any(n.get('name')=='cells[1]' for n in targets))
        self.assertTrue(any(n.get('kind')=='SelectTarget' for n in targets))

    def test_narrow_selector_does_not_wrap_unrepresentable_cell(self):
        d = lower('module top;typedef enum logic[2:0]{A=1,B=2} e_t;'
                  'e_t a[0:4];logic[1:0] i;int r;initial r=$cast(a[i],1);endmodule')
        self.assertFalse(walls(d))
        writes = {n['target'].get('name') for n in nodes(d) if n.get('kind')=='BlockingAssign'}
        self.assertIn('a[3]', writes)
        self.assertNotIn('a[4]', writes)

    def test_repeated_calls_get_independent_capture_names(self):
        d = fixture('rules')
        names = [n['name'] for n in nodes(d) if n.get('kind')=='LocalDecl' and n.get('automatic_cast')]
        self.assertEqual(len(names), len(set(names)))

    def test_task_form_preserves_invalid_branch(self):
        self.assertIn('DynamicCast:task-diagnostic', walls(fixture('task_success')))
        self.assertIn('DynamicCast:task-diagnostic', walls(fixture('task_failure')))

    def test_dependent_unordered_operands_refuse(self):
        self.assertIn('DynamicCast:expression-effects', walls(fixture('unordered')))

    def test_conditional_effect_context_refuses(self):
        self.assertIn('DynamicCast:expression-effects', walls(fixture('conditional')))

    def test_source_side_effects_refuse(self):
        self.assertIn('DynamicCast:type-or-effects', walls(fixture('source_effect')))

    def test_static_initializer_effect_refuses(self):
        d=lower('module top;typedef enum{A=1,B=2} e_t;e_t e;'
                'int r=$cast(e,1);initial $finish;endmodule')
        self.assertIn('DynamicCast:expression-context', walls(d))

    def test_real_conversion_remains_loud(self):
        d=lower('module top;int x,r;initial r=$cast(x,1.5);endmodule')
        self.assertIn('DynamicCast:type-or-effects', walls(d))

    def test_effectful_selector_refuses(self):
        d=lower('module top;logic[7:0] v;int i,r;initial r=$cast(v[i++],1);endmodule')
        self.assertIn('DynamicCast:type-or-effects', walls(d))

    def test_source_binding_cannot_capture_generated_storage(self):
        d=lower('module top;typedef enum{A=1,B=2} e_t;e_t e;'
                'int \\$cast:1 ;int r;initial r=$cast(e,1);endmodule')
        self.assertIn('DynamicCast:storage-collision', walls(d))

    def test_frontend_invalid_source_retains_barrier(self):
        d=lower('module top;typedef enum{A=1,B=2} e_t;e_t e;int x;int x;'
                'int r;initial r=$cast(e,1);endmodule',require_valid=False)
        self.assertIn('DynamicCast:invalid-compilation', walls(d))

    def test_symbolic_surface_does_not_admit_stateful_cast(self):
        d=symbolic('module divider #(parameter int N=8);int x,r;initial r=$cast(x,1);endmodule')
        self.assertTrue(walls(d))
        self.assertFalse(any(n.get('dynamic_cast_lowered') for n in nodes(d)))


if __name__ == '__main__':
    unittest.main()
