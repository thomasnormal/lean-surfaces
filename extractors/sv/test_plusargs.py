"""Explicit input queries and stateful expression sequencing (§21.6)."""
import unittest
from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=Plusargs | origin=spec | authority=IEEE-1800-2023#21.6 | map=environment:explicit;copyback:ordered-control;refusals:unsupported-effects-and-storage


def calls(design):
    return [n for n in nodes(design) if n.get("kind") == "ValuePlusargs"]


def source(body, declarations=""):
    return "module top; int n,a,b; " + declarations + " initial begin " + body + " end endmodule"


class Plusargs(unittest.TestCase):
    def assert_refused(self, text, valid=True):
        design = lower(text, require_valid=valid)
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))
        return design

    def test_pure_test_query_preserves_input_dependency(self):
        design = lower(source('n=$test$plusargs("NAME");'))
        query, = [n for n in nodes(design) if n.get("kind") == "TestPlusargs"]
        self.assertEqual(query["format"], "NAME")
        self.assertEqual(query["width"], 32)
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_direct_copyback_keeps_format_and_target(self):
        for code in "bodhxBODHX":
            call, = calls(lower(source('n=$value$plusargs("DATA=%0'+code+'", a);')))
            self.assertEqual(call["format"], "DATA=%0"+code)
            self.assertEqual(call["target"]["name"], "a")
            self.assertEqual(call["result"]["width"], 32)

    def test_selected_and_two_state_copyback(self):
        call, = calls(lower(source('n=$value$plusargs("BYTE=%h", word[a+:8]);',
                                   'bit [15:0] word;')))
        self.assertEqual(call["target"]["kind"], "SelectTarget")
        self.assertEqual(call["target"]["width"], 8)
        self.assertTrue(call["target"]["two_state"])

    def test_short_circuit_keeps_rhs_call_in_guard(self):
        design = lower(source('if (a && $value$plusargs("A=%d",b)) n=1;'))
        guards = [n for n in nodes(design) if n.get("kind") == "If"
                  and n["cond"].get("op") == "!=="]
        guard, = guards
        self.assertEqual(len(calls(guard["then"])), 1)
        self.assertEqual(guard["cond"]["left"]["op"], "!")
        self.assertEqual(guard["cond"]["left"]["operand"]["op"], "!")

    def test_call_then_dependent_read_is_sequenced(self):
        design = lower(source('if ($value$plusargs("A=%d",a) && a==-17) n=1;'))
        self.assertEqual(len(calls(design)), 1)
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_multiple_calls_in_logical_context(self):
        design = lower(source('n=$value$plusargs("A=%d",a)||$value$plusargs("B=%d",a);'))
        self.assertEqual(len(calls(design)), 2)
        names = [n["name"] for n in nodes(design) if n.get("automatic_plusargs")]
        self.assertEqual(len(names), len(set(names)))

    def test_repeated_body_uses_existing_loop(self):
        design = lower(source('repeat(2) begin n=$value$plusargs("A=%d",a); #1; end'))
        self.assertEqual(len(calls(design)), 1)
        self.assertTrue(any(n.get("kind") == "Repeat" for n in nodes(design)))
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_unordered_dependent_reads_stay_loud(self):
        for expr in ('$value$plusargs("A=%d",a)+a',
                     'a+$value$plusargs("A=%d",a)'):
            self.assert_refused(source('n='+expr+';'))

    def test_other_effect_contexts_stay_loud(self):
        for body in ('n <= $value$plusargs("A=%d",a);',
                     '$display("%d",$value$plusargs("A=%d",a));',
                     'while ($value$plusargs("A=%d",a)) n=1;',
                     'n=a ? $value$plusargs("A=%d",b) : 0;'):
            self.assert_refused(source(body))

    def test_formats_types_and_selectors_stay_loud(self):
        for expr in ('$value$plusargs(fmt,a)', '$value$plusargs("A=%s",text)',
                     '$value$plusargs("A=%2d",a)', '$value$plusargs("A=%d!",a)',
                     '$value$plusargs("A=%d",word[b++])'):
            self.assert_refused(source('n='+expr+';',
                'string text,fmt; logic [31:0] word;'), valid=False)

    def test_storage_collision_and_invalid_compilation(self):
        design = self.assert_refused(source('n=$value$plusargs("A=%d",a);',
                                            'int \\$plusargs:1 ;'))
        self.assertTrue(any(n.get("sv_kind") == "Plusargs:storage-collision" for n in nodes(design)))
        design = self.assert_refused(source('n=$value$plusargs("A=%d",a);', 'int bad=missing;'), valid=False)
        self.assertTrue(any(n.get("sv_kind") == "Plusargs:invalid-compilation" for n in nodes(design)))

    def test_symbolic_boundary(self):
        design = symbolic('module divider; int n,a; initial n=$value$plusargs("A=%d",a); endmodule')
        self.assertFalse(calls(design))
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))


if __name__ == "__main__":
    unittest.main()
