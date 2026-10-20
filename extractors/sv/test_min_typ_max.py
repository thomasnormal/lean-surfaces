"""Elaboration-selected min/typ/max arms, IEEE 1800-2023 §11.11/§10.8."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import extract
from pyslang.syntax import SyntaxTree
from test_bit_queries import nodes
from test_division import symbolic
from test_elaborated_generate import walls

# REFERENCE: 29c155322993572653288b2d 24.03-s004 2026-10-20 | tests=MinTypMax-choices-min | source=Examples/system-verilog/min_typ_max/choices.sv@sha256:a85302083f858d586ac7d39e2def9dba807dfbd9b97dfcddff76635eccd062f6 | top=top | args=["-ii_val","-mindelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: 0728d2d4a990a029ee44f6e1 24.03-s004 2026-10-20 | tests=MinTypMax-choices-typ | source=Examples/system-verilog/min_typ_max/choices.sv@sha256:a85302083f858d586ac7d39e2def9dba807dfbd9b97dfcddff76635eccd062f6 | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: f8ecbddd33f9bc55c32c8243 24.03-s004 2026-10-20 | tests=MinTypMax-choices-max | source=Examples/system-verilog/min_typ_max/choices.sv@sha256:a85302083f858d586ac7d39e2def9dba807dfbd9b97dfcddff76635eccd062f6 | top=top | args=["-ii_val","-maxdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: 49c6fa3ca4f3d7e47f7dcc3b 24.03-s004 2026-10-20 | tests=MinTypMax-composition-typ | source=Examples/system-verilog/min_typ_max/composition.sv@sha256:33946782fb97af254d492cfc3e0a0a44386197a41fd7768f8cba9c7d376a849b | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: 38303d599b21911c77aab27e 24.03-s004 2026-10-20 | tests=MinTypMax-runtime-typ | source=Examples/system-verilog/min_typ_max/runtime.sv@sha256:ccca4ce35fb7861fbe1747dfbdd8034c76d569419a600e4eec430f3ec859cb4f | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: 927a5566cea80ee8ccb9a225 24.03-s004 2026-10-20 | tests=MinTypMax-elaboration-typ | source=Examples/system-verilog/min_typ_max/elaboration.sv@sha256:1cbf484159215aafc8bcaf39fb399660dbb7c08453385e15eacb1c19a9bd6194 | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: 258f925bcc219068b0fe34fc 24.03-s004 2026-10-20 | tests=MinTypMax-timing-min | source=Examples/system-verilog/min_typ_max/timing.sv@sha256:d5aad3f19c9ab96a87f9b901af987a5b8237892c45e208c3718b8170787e167b | top=top | args=["-ii_val","-mindelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: 4bdb569966f9172d6fd69af9 24.03-s004 2026-10-20 | tests=MinTypMax-timing-typ | source=Examples/system-verilog/min_typ_max/timing.sv@sha256:d5aad3f19c9ab96a87f9b901af987a5b8237892c45e208c3718b8170787e167b | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: 84c258a8c685497122270e56 24.03-s004 2026-10-20 | tests=MinTypMax-timing-max | source=Examples/system-verilog/min_typ_max/timing.sv@sha256:d5aad3f19c9ab96a87f9b901af987a5b8237892c45e208c3718b8170787e167b | top=top | args=["-ii_val","-maxdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: 7852196ee4fbb3f239912613 24.03-s004 2026-10-20 | tests=MinTypMax-unknown-typ | source=Examples/system-verilog/min_typ_max/unknown.sv@sha256:0e495a69a067340b5cf7d60d8a36aee9e4d48d21fa69ab4331fd2c0acd2ebc0e | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: 8f9dab996795162b9f1c4293 24.03-s004 2026-10-20 | tests=MinTypMax-unselected-typ | source=Examples/system-verilog/min_typ_max/unselected.sv@sha256:1b0b86e6f0dc54a2f3406ad1efd3039f810fd7722573886ef55f71d40d05c27a | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: ff52df8c8ba81fa91d0a3a78 24.03-s004 2026-10-20 | tests=MinTypMax-unselected_math-typ | source=Examples/system-verilog/min_typ_max/unselected_math.sv@sha256:bede42e2ee0f5be2e9e80d917687aba0b532ca0afa3034bdd76c8b481f13ba0b | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: c878ad77f567fd6033c055d1 24.03-s004 2026-10-20 | tests=MinTypMax-effects-typ | source=Examples/system-verilog/min_typ_max/effects.sv@sha256:91dbf53d197088535f4a965c0597f873c0f274c47178054b54f8ae9861fb0d5c | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# REFERENCE: cf25df2003a11d9b08aed26c 24.03-s004 2026-10-20 | tests=MinTypMax-argument_context-typ | source=Examples/system-verilog/min_typ_max/argument_context.sv@sha256:a22a1fe86b7de8adcd491f88612589517c712432d020458a46c6db1313f1c5a2 | top=top | args=["-ii_val","-typdelays"] | map=Examples/system-verilog/min_typ_max/README.md#min-typ-max
# SYNTHETIC-ORACLE: tests=MinTypMax-schema-and-admission | origin=spec | authority=IEEE-1800-2023#11.11 | map=choice:global-elaboration;value:selected-bound-tree;effects:selected-arm-only;invalid:frontend-barrier;options:recorded-nondefault;symbolic:nonconstant-loud


def lower(source, choice='typ', require_valid=True):
    extract._SYM = None
    extract._SOURCE_BYTES = source.encode()
    tree = SyntaxTree.fromText(source)
    compilation = extract._compilation_with_choice(choice)
    compilation.addSyntaxTree(tree)
    if require_valid and any(d.isError() for d in compilation.getAllDiagnostics()):
        raise AssertionError('min/typ/max regression source has frontend errors')
    return extract.convert_design(tree.sourceManager, compilation)


def choices(design):
    return [n for n in nodes(design) if n.get('kind') == 'MinTypMax']


class MinTypMax(unittest.TestCase):
    def test_all_choices_select_positions_rather_than_sort_values(self):
        for mode, value in (('min', 33), ('typ', 22), ('max', 11)):
            d = lower('module top;int v;initial v=(33:22:11);endmodule', mode)
            self.assertFalse(walls(d))
            selected, = choices(d)
            self.assertEqual(selected['choice'], mode)
            self.assertEqual(int(selected['value']['bits'], 2), value)

    def test_live_selected_variable_is_retained(self):
        for mode, name in (('min', 'a'), ('typ', 'b'), ('max', 'c')):
            d = lower('module top;logic[7:0]a,b,c,v;initial v=(a:b:c);endmodule', mode)
            selected, = choices(d)
            self.assertEqual(selected['value']['name'], name)
            self.assertFalse(walls(d))

    def test_assignment_context_converts_complete_selected_value(self):
        for mode, width in (('min', 32), ('typ', 8), ('max', 16)):
            d = lower("module top;logic[3:0]v;initial v=(32'h11:8'h22:16'h33);endmodule", mode)
            selected, = choices(d)
            self.assertEqual(selected['width'], width)
            self.assertEqual(selected['value']['width'], width)
            self.assertTrue(any(n.get('kind') == 'Resize' and n['width'] == 4 for n in nodes(d)))

    def test_signed_extension_keeps_the_bound_conversion(self):
        d = lower("module top;logic signed[7:0]a,b,c;logic signed[15:0]v;initial v=(a:b:c);endmodule")
        self.assertFalse(walls(d))
        self.assertTrue(any(n.get('kind') == 'SignedResize' for n in nodes(d)))
        selected, = choices(d)
        self.assertTrue(selected['signed'])

    def test_nested_choices_share_the_global_mode(self):
        for mode in ('min', 'typ', 'max'):
            d = lower('module top;int v;initial v=((1:2:3):(4:5:6):(7:8:9));endmodule', mode)
            self.assertFalse(walls(d))
            self.assertEqual([n['choice'] for n in choices(d)], [mode, mode])

    def test_source_effects_in_unselected_arms_are_not_evaluated(self):
        s = 'module top;int n,v;initial v=(n++:7:n++);endmodule'
        self.assertFalse(walls(lower(s)))
        for mode in ('min', 'max'):
            self.assertIn('MinTypMaxExpression:selected-source', walls(lower(s, mode)))

    def test_selected_effect_is_not_erased_by_outer_folding(self):
        d = lower('module top;int n,v;initial v=((1:n++:2)==1);endmodule')
        self.assertTrue(walls(d))

    def test_unselected_numeric_refusal_does_not_poison_a_constant_context(self):
        s = "module top;localparam int W=($clog2(8'hxx):8:$clog2(8'hxx));logic[W-1:0]v;endmodule"
        self.assertFalse(walls(lower(s)))
        for mode in ('min', 'max'):
            self.assertIn('$clog2:constant-context', walls(lower(s, mode)))

    def test_only_selected_runtime_numeric_call_survives(self):
        d = lower('module top;logic[7:0]a,b,c;int v;initial v=($clog2(a):$clog2(b):$clog2(c));endmodule')
        self.assertFalse(walls(d))
        call, = [n for n in nodes(d) if n.get('kind') == 'Clog2']
        self.assertEqual(call['operand']['name'], 'b')

    def test_unselected_package_initializer_call_is_not_live(self):
        d = lower('package p;int n;int v=(n++:7:n++);endpackage module top;import p::*;initial $display("%0d",v);endmodule')
        self.assertFalse(walls(d))

    def test_pure_nested_contexts_compose(self):
        for expression in ('(1:2:3)+1', '1<<(1:2:3)', '(1:2:3)<(2:3:4)',
                           '{(4\'h1:4\'h2:4\'h3),4\'h0}', '((0:1:0)?1:2)'):
            self.assertFalse(walls(lower('module top;logic[7:0]v;initial v='+expression+';endmodule')), expression)

    def test_packed_pattern_members_select_independently(self):
        d = lower("module top;typedef struct packed{logic[3:0]hi;logic[3:0]lo;}P;P v;"
                  "initial v='{(4'h1:4'h2:4'h3),(4'h4:4'h5:4'h6)};endmodule")
        self.assertFalse(walls(d))
        self.assertEqual(len(choices(d)), 2)

    def test_replication_count_uses_the_selected_bound_constant(self):
        d = lower("module top;logic[7:0]v={(1:2:4){2'b10}};endmodule")
        self.assertFalse(walls(d))
        self.assertTrue(any(n.get('replication_count') == 2 for n in nodes(d)))

    def test_literal_delay_selects_the_existing_timer_amount(self):
        for mode, amount in (('min', 2), ('typ', 5), ('max', 8)):
            d = lower('module top;initial begin #(2:5:8);$finish;end endmodule', mode)
            self.assertFalse(walls(d))
            delay, = [n for n in nodes(d) if n.get('kind') == 'Delay']
            self.assertEqual(delay['amount'], amount)

    def test_selected_dynamic_delay_keeps_the_existing_boundary(self):
        self.assertTrue(walls(lower('module top;int n;initial #(1:n:3) $finish;endmodule')))

    def test_frontend_invalid_unselected_arm_is_loud(self):
        self.assertTrue(walls(lower('module top;int v;initial v=(missing:1:2);endmodule', require_valid=False)))

    def test_redefinition_is_an_admission_barrier(self):
        d = lower('module top;int v;initial v=(1:2:3);logic v;endmodule', require_valid=False)
        self.assertIn('MinTypMaxExpression:invalid-compilation', walls(d))

    def test_selected_real_and_unmodelled_calls_are_loud(self):
        for source in ('real v;initial v=(1.0:2.0:3.0);', 'int v;initial v=(1:$rtoi(2.0):3);'):
            self.assertTrue(walls(lower('module top;'+source+'endmodule')))

    def test_mode_context_is_restored_on_failure(self):
        with mock.patch.object(extract, '_MIN_TYP_MAX', 'min'):
            with mock.patch.object(extract, '_convert_design', side_effect=ValueError('test')):
                with self.assertRaises(ValueError):
                    lower('module top;int v;endmodule', 'max')
            self.assertEqual(extract._MIN_TYP_MAX, 'min')

    def test_nonconstant_symbolic_selection_remains_loud(self):
        self.assertTrue(walls(symbolic('module divider #(parameter int N=8);logic[N-1:0]a,b,c,v;initial v=(a:b:c);endmodule')))

    def test_symbolic_constant_typical_folding_is_preserved(self):
        d = symbolic('module divider #(parameter int N=8);logic[N-1:0]v;initial v=(33:22:11);endmodule')
        self.assertFalse(walls(d))
        self.assertTrue(any(n.get('kind') == 'Literal' and n['bits'] == '00010110'
                            for n in nodes(d)))

    def test_cli_records_nondefault_modes_and_reproduces_exactly(self):
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory)/'choice.sv'
            p.write_text('module top;int v;initial v=(33:22:11);endmodule')
            with contextlib.redirect_stdout(io.StringIO()):
                for mode in ('min', 'typ', 'max'):
                    args = ['--min-typ-max', mode, str(p)]
                    self.assertEqual(extract.main(args), 0)
                    before = Path(str(p)+'.json').read_bytes()
                    envelope = json.loads(before)
                    self.assertEqual(envelope.get('min_typ_max', 'typ'), mode)
                    self.assertEqual(choices(envelope)[0]['choice'], mode)
                    self.assertEqual(extract.main(args), 0)
                    self.assertEqual(Path(str(p)+'.json').read_bytes(), before)

    def test_nondefault_symbolic_option_is_rejected(self):
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(extract.main(['--top', 'divider', '--min-typ-max', 'min', 'missing.sv']), 1)


if __name__ == '__main__':
    unittest.main()
