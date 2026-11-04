"""Runtime ceiling logarithm: IEEE 1800-2023 §20.8.1."""
from pathlib import Path
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic
from test_elaborated_generate import walls

# SYNTHETIC-ORACLE: tests=RuntimeClog2 | origin=spec | authority=IEEE-1800-2023#20.8.1 | map=operand:self-determined-integral-width;result:signed-int;effects:pure-source-census;unknown:no-bound-approximation;symbolic:unchanged


def calls(design):
    return [node for node in nodes(design) if node.get('kind') == 'Clog2']


class RuntimeClog2(unittest.TestCase):
    def test_live_argument_retains_its_own_width(self):
        for width in (1, 8, 32, 128, 4096):
            d = lower(f'module top;logic[{width-1}:0]v;int r;initial r=$clog2(v);endmodule')
            self.assertFalse(walls(d))
            call, = calls(d)
            self.assertEqual(call['operand']['width'], width)
            self.assertEqual(call['operand']['name'], 'v')
            self.assertEqual(call['width'], 32)
            self.assertIs(call['signed'], True)

    def test_sign_does_not_reinterpret_or_extend_the_argument(self):
        d = lower('module top;logic signed[7:0]v;int r;initial r=$clog2(v);endmodule')
        call, = calls(d)
        self.assertEqual(call['operand']['width'], 8)
        self.assertIs(call['operand']['signed'], True)
        self.assertFalse(walls(d))

    def test_assignment_conversion_wraps_the_complete_call(self):
        d = lower('module top;logic[127:0]v;logic[2:0]r;initial r=$clog2(v);endmodule')
        self.assertFalse(walls(d))
        self.assertTrue(any(n.get('kind')=='Resize' and n['width']==3 and
                            n.get('operand',{}).get('kind')=='Clog2' for n in nodes(d)))

    def test_known_constant_fast_path_is_preserved(self):
        d = lower('module top;int v=$clog2(9);endmodule')
        self.assertFalse(walls(d))
        self.assertFalse(calls(d))
        self.assertTrue(any(n.get('fixed_clog2') for n in nodes(d)))

    def test_nested_calls_keep_both_runtime_reads(self):
        d = lower('module top;logic[63:0]v;int r;initial r=$clog2($clog2(v));endmodule')
        self.assertFalse(walls(d))
        self.assertEqual(len(calls(d)),2)

    def test_unknown_literals_cannot_be_folded_away_by_surrounding_context(self):
        for value in ("8'hxx", "8'hzz", "8'b1x000000"):
            d = lower('module top;int r=($clog2('+value+')==0);endmodule')
            self.assertTrue(calls(d))
            self.assertFalse(walls(d))

    def test_unknown_elaboration_arguments_are_loud(self):
        for declaration in ("localparam int P=$clog2(8'hxx);",
                            "typedef enum int {E=$clog2(8'hxx)} T;",
                            "if($clog2(8'hxx)==0)begin:a logic v;end"):
            d = lower('module top; '+declaration+' endmodule')
            self.assertIn('$clog2:constant-context', walls(d))

    def test_unknown_count_does_not_consume_an_approximate_bound_constant(self):
        d = lower("module top;logic[7:0]v={($clog2(8'hxx)+1){1'b1}};endmodule")
        self.assertIn('Replication:constant-count', walls(d))

    def test_unevaluated_type_queries_do_not_call_the_numeric_function(self):
        d = lower("module top;localparam int W=$bits($clog2(8'hxx));logic[W-1:0]v;endmodule")
        self.assertFalse(walls(d))
        self.assertFalse(calls(d))

    def test_zero_replication_cannot_erase_a_runtime_unknown_refusal(self):
        d = lower("module top;logic[7:0]v;logic[7:0]r={{0{$clog2(v)}},8'ha5};endmodule")
        self.assertIn('Replication:operand',walls(d))

    def test_effectful_and_nonintegral_arguments_remain_loud(self):
        for declaration, argument in (('int v;','v++'),('real v;','v'),('string v;','v')):
            d = lower('module top;'+declaration+' int r;initial r=$clog2('+argument+');endmodule',require_valid=False)
            self.assertTrue(walls(d))

    def test_bad_arity_is_loud(self):
        for argument in ('','1,2'):
            self.assertTrue(walls(lower('module top;int r=$clog2('+argument+');endmodule',require_valid=False)))

    def test_runtime_marker_keeps_redefinition_warnings_loud(self):
        d = lower('module top;int v;int r=$clog2(v);logic v;endmodule',require_valid=False)
        self.assertIn('$clog2:invalid-compilation', walls(d))

    def test_symbolic_vocabulary_is_unchanged(self):
        d = symbolic('module divider #(parameter int N=8);logic[$clog2(N)-1:0]v;endmodule')
        self.assertFalse(calls(d))
        self.assertTrue(any(n.get('kind')=='SysCall' and n.get('name')=='$clog2' for n in nodes(d)))

    def test_authored_runnable_sources_are_admitted(self):
        root=Path(__file__).resolve().parents[2]/'Examples/system-verilog/runtime_clog2'
        for name in ('boundaries','widths','runtime','composition'):
            self.assertFalse(walls(lower((root/(name+'.sv')).read_text())),name)


if __name__=='__main__':
    unittest.main()
