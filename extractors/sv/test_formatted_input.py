"""Admission and target shape for the integral formatted-input statement."""
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=FormattedInput | origin=spec | authority=IEEE-1800-2023#21.3.4.3 | map=grammar:literal-format-and-exact-output-arity;targets:existing-packed-targets;refusals:unsupported-contexts-and-effects-before-folding


def scans(design):
    return [n for n in nodes(design) if n.get("kind") == "Scanf"]


def source(call, declarations="", assignment="n = "):
    return ("module top; int n, a, b; " + declarations +
            " initial begin " + assignment + call + "; end endmodule")


class FormattedInput(unittest.TestCase):
    def assert_refused(self, text, valid=True):
        design = lower(text, require_valid=valid)
        self.assertFalse(scans(design))
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_literal_input_is_packed_without_scanning(self):
        statement, = scans(lower(source('$sscanf("12 34", "%d %d", a, b)')))
        self.assertEqual(statement["format"], "%d %d")
        self.assertEqual(statement["input"]["width"], 40)
        self.assertEqual(int(statement["input"]["bits"], 2), int.from_bytes(b"12 34", "big"))
        self.assertEqual([t["name"] for t in statement["outputs"]], ["a", "b"])

    def test_runtime_input_retains_expression(self):
        statement, = scans(lower(source('$sscanf(data, "%d", a)', 'logic [63:0] data;')))
        self.assertEqual(statement["input"]["kind"], "Ident")
        self.assertEqual(statement["input"]["name"], "data")

    def test_selected_outputs_and_result_use_existing_targets(self):
        statement, = scans(lower(source('$sscanf("5 a", "%h %h", word[11:8], word[i+:4])',
            'logic [15:0] word; int i;', 'word[3:0] = ')))
        self.assertEqual([t["kind"] for t in statement["outputs"]], ["SelectTarget"] * 2)
        self.assertEqual([t["width"] for t in statement["outputs"]], [4, 4])
        self.assertEqual(statement["result"]["width"], 4)

    def test_conversion_grammar_and_suppression(self):
        for code in "bodhxcsvBODHXCSV":
            self.assertEqual(len(scans(lower(source('$sscanf("123", "%3' + code + '", a)')))), 1)
        self.assertEqual(len(scans(lower(source('$sscanf("%12 34", "%%%*2d %d", a)')))), 1)
        self.assertEqual(len(scans(lower(source('$sscanf("12", "%*d")')))), 1)

    def test_concatenated_and_two_state_targets_retain_metadata(self):
        statement, = scans(lower(source('$sscanf("123", "%h", {hi, lo})',
            'bit [3:0] hi; logic [3:0] lo;')))
        target, = statement["outputs"]
        self.assertEqual(target["kind"], "ConcatTarget")
        self.assertEqual([p["two_state"] for p in target["parts"]], [True, False])

    def test_result_resize_does_not_hide_the_call(self):
        statement, = scans(lower(source('$sscanf("1", "%d", a)',
            'logic [63:0] result;', 'result = ')))
        self.assertEqual(statement["result"]["width"], 64)

    def test_format_and_arity_boundaries(self):
        for call in ('$sscanf("1", "%f", a)', '$sscanf("1", "%0d", a)',
                     '$sscanf("1", "%d%", a)', '$sscanf("1", "%d", a, b)',
                     '$sscanf("1", "%d %d", a)', '$sscanf("1", fmt, a)'):
            self.assert_refused(source(call, 'logic [15:0] fmt;'), valid=False)

    def test_effectful_inputs_and_selectors_stay_loud(self):
        for call in ('$sscanf(data++, "%d", a)', '$sscanf(data, "%d", word[i++])'):
            self.assert_refused(source(call, 'logic [31:0] data, word; int i;'))

    def test_nonintegral_storage_stays_loud(self):
        for call in ('$sscanf(text, "%d", a)', '$sscanf("1", "%d", r)'):
            self.assert_refused(source(call, 'string text; real r;'))

    def test_other_call_contexts_stay_loud(self):
        for text in (source('$sscanf("1", "%d", a)', assignment='n <= '),
                     source('$sscanf("1", "%d", a)', assignment='n += '),
                     source('1 + $sscanf("1", "%d", a)'),
                     source('$display("%0d", $sscanf("1", "%d", a))', assignment='')):
            self.assert_refused(text)

    def test_error_barrier_and_symbolic_boundary(self):
        invalid = lower(source('$sscanf("1", "%d", a)', 'int bad = missing;'), require_valid=False)
        self.assertTrue(any(n.get("sv_kind") == "Scanf:invalid-compilation" for n in nodes(invalid)))
        design = symbolic('module divider; int n, a; initial n=$sscanf("1", "%d", a); endmodule')
        self.assertFalse(scans(design))
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))


if __name__ == "__main__":
    unittest.main()
