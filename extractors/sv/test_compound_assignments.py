"""Blocking operator assignments: bound RMW conversions and one address capture."""
import json
import tempfile
from pathlib import Path
from unittest import TestCase, main, mock

import extract
from test_bit_queries import lower, nodes
from test_division import symbolic
from test_elaborated_generate import walls

# SYNTHETIC-ORACLE: tests=CompoundAssignments | origin=spec | authority=IEEE-1800-2023#11.4.1 | map=address:one-capture;value:complete-bound-RMW;array:representable-indices;effects:pure-source-only;invalid:admission-barrier


def compound(source):
    return lower('module top; ' + source + ' endmodule')


def captures(design):
    return [n for n in nodes(design) if n.get('automatic_compound')]


class CompoundAssignments(TestCase):
    def test_wider_rhs_retains_operation_width_before_narrowing(self):
        d = compound("logic[3:0]v;initial v+=32'h11;")
        self.assertFalse(walls(d))
        resize, = [n for n in nodes(d) if n.get('kind') == 'Resize' and n['width'] == 4]
        self.assertEqual(resize['operand']['width'], 32)
        self.assertEqual(resize['operand']['op'], '+')
        self.assertEqual(resize['operand']['left']['width'], 32)

    def test_complete_operator_inventory(self):
        for op in ('+', '-', '*', '/', '%', '&', '|', '^', '<<', '>>', '<<<', '>>>'):
            d = compound('logic[7:0]v;initial v' + op + "=8'h3;")
            self.assertFalse(walls(d), op)

    def test_signed_division_remainder_and_shift_keep_the_bound_sign(self):
        d = compound("logic signed[7:0]v;initial begin v/=8'sd3;v%=8'sd5;v>>>=1;end")
        self.assertFalse(walls(d))
        self.assertEqual([n['op'] for n in nodes(d) if n.get('kind') == 'Binary'], ['s/', 's%', 's>>>'])

    def test_packed_selector_is_captured_once_and_shared_by_read_and_store(self):
        d = compound('logic[15:0]v;int i;initial v[i+1+:4]^=4\'hf;')
        self.assertFalse(walls(d))
        capture, = captures(d)
        self.assertEqual(capture['init']['op'], '+')
        store, = [n for n in nodes(d) if n.get('kind') == 'SelectTarget']
        read, = [n for n in nodes(d) if n.get('kind') == 'CompoundRead']
        self.assertEqual(store['index']['name'], capture['name'])
        self.assertEqual(read['index'], store['index'])

    def test_array_index_and_result_precede_every_write_branch(self):
        d = compound('int v[2:-1];int i;initial v[i]+=3;')
        self.assertFalse(walls(d))
        index, value = captures(d)
        self.assertTrue(index['name'].endswith(':index'))
        self.assertTrue(value['name'].endswith(':value'))
        block, = [n for n in nodes(d) if n.get('compound_assignment_lowered')]
        self.assertEqual([n['kind'] for n in block['stmts']], ['LocalDecl', 'LocalDecl', 'If'])
        stores = [n for n in nodes(block) if n.get('kind') == 'BlockingAssign']
        self.assertEqual([n['target']['name'] for n in stores], ['v[2]', 'v[1]', 'v[0]', 'v[-1]'])
        self.assertEqual({n['value']['name'] for n in stores}, {value['name']})

    def test_narrow_unsigned_indices_cannot_alias_truncated_array_positions(self):
        d = compound('bit[3:0]v[2:3];logic i;initial v[i]+=1;')
        self.assertFalse(walls(d))
        self.assertFalse(any(n.get('kind') == 'BlockingAssign' for n in nodes(d)))
        _, value = captures(d)
        self.assertTrue(any(n.get('bits') == '0000' for n in nodes(value)))

    def test_signed_one_bit_index_only_addresses_minus_one(self):
        d = compound('int v[-2:-1];logic signed i;initial v[i]+=1;')
        self.assertFalse(walls(d))
        stores = [n for n in nodes(d) if n.get('kind') == 'BlockingAssign']
        self.assertEqual([n['target']['name'] for n in stores], ['v[-1]'])

    def test_four_state_invalid_array_read_uses_unknown_default(self):
        d = compound('logic[7:0]v[0:1];int i;initial v[i]+=1;')
        self.assertFalse(walls(d))
        self.assertTrue(any(n.get('bits') == 'x'*8 for n in nodes(captures(d)[1])))

    def test_member_window_is_bounded_before_copyback(self):
        d = compound('typedef struct packed{logic[7:0]hi;logic[7:0]lo;}T;T v;int i;'
                     'initial v.hi[i+:4]^=4\'hf;')
        self.assertFalse(walls(d))
        index, member = captures(d)
        self.assertEqual(member['width'], 8)
        stores = [n for n in nodes(d) if n.get('kind') == 'BlockingAssign']
        self.assertEqual(stores[0]['target']['value']['name'], member['name'])
        self.assertEqual(stores[0]['target']['index']['name'], index['name'])
        self.assertEqual(stores[1]['value']['name'], member['name'])
        self.assertEqual(stores[1]['target']['width'], 8)

    def test_two_state_conversion_wraps_the_full_rmw(self):
        d = compound("bit[3:0]v;logic[7:0]r;initial v+=r;")
        self.assertFalse(walls(d))
        store, = [n for n in nodes(d) if n.get('kind') == 'BlockingAssign']
        self.assertEqual(store['value']['kind'], 'Squash2')
        self.assertTrue(any(n.get('kind') == 'Resize' and n['width'] == 4 for n in nodes(store['value'])))

    def test_effects_and_unsupported_lvalues_remain_loud(self):
        for source in ('logic[7:0]v;int i;initial v[i++]^=1;',
                       'logic[7:0]v;int i;initial v+=i++;',
                       'logic[3:0]a,b;initial {a,b}+=1;',
                       'real v;initial v+=1.0;'):
            self.assertTrue(walls(compound(source)), source)

    def test_delayed_statement_composes_but_intra_assignment_timing_does_not(self):
        self.assertFalse(walls(compound('logic[7:0]v;int i;initial #1 v[i]^=1;')))
        self.assertTrue(walls(lower('module top;int v;initial v+=#1 3;endmodule', require_valid=False)))

    def test_generated_storage_collision_is_loud(self):
        with mock.patch.object(extract, '_scoped_temp', return_value='$compound:collision'):
            d = compound('logic[7:0]v;int i;int \\$compound:collision ;initial v[i]^=1;')
        self.assertIn('AssignmentExpression:compound-storage-collision', walls(d))

    def test_redefinition_is_a_design_barrier(self):
        d = lower('module top;int v;initial v+=1;logic v;endmodule', require_valid=False)
        self.assertIn('AssignmentExpression:compound-invalid-compilation', walls(d))

    def test_placeholder_context_is_restored_on_conversion_failure(self):
        sentinel = object()
        with mock.patch.object(extract, '_COMPOUND_READ', sentinel):
            with mock.patch.object(extract, 'convert_expr', side_effect=ValueError('test')):
                with self.assertRaises(ValueError):
                    extract._compound_value(None, type('Expression', (), {'right': None})(), {})
            self.assertIs(extract._COMPOUND_READ, sentinel)

    def test_symbolic_compounds_remain_loud(self):
        d = symbolic('module divider #(parameter int N=8);logic[N-1:0]v;initial v+=1;endmodule')
        self.assertIn('AssignmentExpression:compound', walls(d))

    def test_authored_runnable_sources_are_admitted(self):
        root = Path(__file__).resolve().parents[2]/'Examples/system-verilog/compound_assignments'
        for name in ('scalars', 'arrays', 'windows', 'members', 'two_state', 'indices', 'runtime'):
            self.assertFalse(walls(lower((root/(name+'.sv')).read_text())), name)


def extract_source(source):
    return lower(source)


def body(source):
    design = extract_source("module top; logic [3:0] value, delta; "
                           "initial begin " + source + " end endmodule")
    return design["modules"][0]["processes"][0]["body"]["stmts"]


class ScalarCompoundAssignments(TestCase):
    def test_scalar_binary_compounds_lower_to_binary_reads(self):
        statements = body("value = 4'b0001; delta = 4'b0011; "
                           "value += delta; value -= 4'b0001; "
                           "value &= 4'b0110; value |= 4'b1000; "
                           "value ^= 4'b0011;")
        compounds = statements[2:]
        self.assertEqual([statement["kind"] for statement in compounds],
                         ["BlockingAssign"] * 5)
        self.assertEqual([statement["value"]["op"] for statement in compounds],
                         ["+", "-", "&", "|", "^"])
        self.assertTrue(all(statement["value"]["left"]["kind"] == "Ident"
                            for statement in compounds))

    def test_remainder_compound_lowers_to_binary_read(self):
        statements = body("value %= delta;")
        self.assertEqual(statements[0]["kind"], "BlockingAssign")
        self.assertEqual(statements[0]["value"]["op"], "u%")
        self.assertEqual(statements[0]["value"]["left"]["name"], "value")

    def test_conversion_wrapped_compound_retains_the_complete_operation(self):
        statement = body("value += 1;")[0]
        self.assertEqual(statement["kind"], "BlockingAssign")
        self.assertEqual(statement["value"]["kind"], "Resize")
        self.assertEqual(statement["value"]["operand"]["width"], 32)

    def test_nested_binary_rhs_is_retained(self):
        statement = body("value += (delta + 4'b0001);")[0]
        right = statement["value"]["right"]
        self.assertEqual(right["kind"], "Binary")
        self.assertEqual(right["left"]["name"], "delta")
        self.assertEqual(right["right"]["bits"], "0001")

    def test_two_state_destination_uses_existing_squash(self):
        design = extract_source("module top; bit [3:0] value; "
                                "logic [3:0] delta; "
                                "initial value &= delta; endmodule")
        statement = design["modules"][0]["processes"][0]["body"]
        self.assertEqual(statement["value"]["kind"], "Squash2")
        self.assertEqual(statement["value"]["operand"]["op"], "&")

    def test_selected_compound_target_reads_the_current_bits(self):
        design = extract_source("module top; logic [3:0] value; "
                                "initial value[0] += 1'b1; endmodule")
        statement = design["modules"][0]["processes"][0]["body"]
        self.assertEqual(statement["kind"], "BlockingAssign")
        self.assertEqual(statement["value"]["left"]["kind"], "CompoundRead")

    def test_symbolic_compound_assignments_stay_loud(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "top.sv"
            output = Path(directory) / "top.sv.json"
            source.write_text("module top; logic [3:0] value, delta; "
                              "initial value += delta; endmodule")
            extract.process_symbolic("top", [str(source)], [], str(output))
            design = json.loads(output.read_text())["design"]
            statement = design["modules"][0]["processes"][0]["body"]
            self.assertEqual(statement["sv_kind"],
                             "AssignmentExpression:compound")


if __name__ == '__main__':
    main()
