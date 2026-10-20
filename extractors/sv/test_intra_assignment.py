"""Capture-before-wait and copyback placement for blocking timed assignments."""
import unittest
from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=IntraAssignment | origin=spec | authority=IEEE-1800-2023#10.4.1,9.4.5 | map=rhs:one-capture;destination:after-wait;publication:existing-core-only


def source(body, declarations=""):
    return "module top; logic [7:0] a,b; int index,count; bit clk; " + declarations + " initial begin " + body + " end endmodule"


def captures(design):
    return [n for n in nodes(design) if n.get("intra_assignment_lowered")]


class IntraAssignment(unittest.TestCase):
    def assert_refused(self, body, declarations="", valid=True):
        design = lower(source(body, declarations), require_valid=valid)
        self.assertFalse(captures(design))
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))
        return design

    def test_capture_wait_copyback_order(self):
        lowered, = captures(lower(source('a = #3 b;')))
        capture, wait, copyback = lowered["stmts"]
        self.assertEqual(capture["init"]["name"], "b")
        self.assertTrue(capture["automatic_intra"])
        self.assertEqual(wait["kind"], "Delay")
        self.assertEqual(wait["amount"], 3)
        self.assertEqual(copyback["value"]["name"], capture["name"])
        self.assertEqual(copyback["target"]["parts"][0]["name"], "a")

    def test_selected_destination_index_is_after_wait(self):
        lowered, = captures(lower(source('a[index+:4] = #5 b[3:0];')))
        capture, wait, copyback = lowered["stmts"]
        self.assertEqual(capture["width"], 4)
        self.assertFalse(any(n.get("name") == "index" for n in nodes(capture)))
        self.assertEqual(copyback["target"]["parts"][0]["index"]["name"], "index")
        self.assertEqual(wait["amount"], 5)

    def test_zero_delay_is_a_suspension(self):
        lowered, = captures(lower(source('a = #0 b;')))
        self.assertEqual(lowered["stmts"][1]["kind"], "Delay")
        self.assertEqual(lowered["stmts"][1]["amount"], 0)

    def test_concatenated_and_two_state_destinations(self):
        lowered, = captures(lower(source('{clean,a[3:0]} = #2 b;', 'bit [3:0] clean;')))
        target = lowered["stmts"][2]["target"]["parts"][0]
        self.assertEqual(target["kind"], "ConcatTarget")
        self.assertEqual([p["two_state"] for p in target["parts"]], [True,False])

    def test_single_edges_use_existing_wait_node(self):
        for event,edge in (("posedge clk","posedge"),("negedge clk","negedge"),("clk","any")):
            lowered, = captures(lower(source('a = @('+event+') b;')))
            wait=lowered["stmts"][1]
            self.assertEqual((wait["kind"],wait["signal"],wait["edge"]),("WaitEvent","clk",edge))

    def test_repeated_count_is_existing_sampled_loop(self):
        lowered, = captures(lower(source('a = repeat(count) @(posedge clk) b;')))
        repeat=lowered["stmts"][1]
        self.assertEqual(repeat["kind"], "Repeat")
        self.assertEqual(repeat["count"]["name"], "count")
        self.assertTrue(repeat["count_signed"])
        self.assertEqual(repeat["body"]["kind"], "WaitEvent")

    def test_reentry_has_no_unmodelled_local_lifetime(self):
        design=lower(source('repeat(2) a = #1 b; for(index=0; index<2; index++) a=#1 b;'))
        self.assertEqual(len(captures(design)),2)
        self.assertFalse(any(n.get("kind")=="Unsupported" for n in nodes(design)))

    def test_unsupported_delay_inventory_stays_loud(self):
        for delay in ('count','(1+2)','-1','1ns','1.5',"4'hx","65'd18446744073709551616"):
            self.assert_refused('a = #('+delay+') b;')

    def test_effectful_sources_and_selectors_stay_loud(self):
        for body in ('a = #1 b++;','a[index++] = #1 b[0];',
                     'a = repeat(count++) @(posedge clk) b;'):
            self.assert_refused(body, valid='repeat' not in body)

    def test_nonblocking_publication_stays_loud(self):
        for body in ('a <= #0 b;', 'a <= #1 b;', 'a <= @(posedge clk) b;'):
            self.assert_refused(body)

    def test_other_event_controls_stay_loud(self):
        for control in ('@(posedge clk or negedge clk)', '@(posedge clk iff count)', '@*'):
            self.assert_refused('a = '+control+' b;', valid=False)

    def test_dynamic_unpacked_target_is_an_explicit_boundary(self):
        self.assert_refused('mem[index]=#1 b;', 'logic [7:0] mem[4];')

    def test_generated_names_and_collision(self):
        text=source('a=#1 b; a=#2 b;')
        names=lambda d: [n['name'] for n in nodes(d) if n.get('automatic_intra')]
        self.assertEqual(names(lower(text)),names(lower(text)))
        self.assertEqual(len(names(lower(text))),len(set(names(lower(text)))))
        name=names(lower(text))[0]
        design=lower(text.replace(' endmodule', ' int \\'+name+' ; endmodule'))
        self.assertTrue(any(n.get('sv_kind')=='IntraAssignment:storage-collision' for n in nodes(design)))

    def test_invalid_compilation_and_symbolic_boundary(self):
        design=lower(source('a=#1 b;', 'int bad=missing;'), require_valid=False)
        self.assertTrue(any(n.get('sv_kind')=='IntraAssignment:invalid-compilation' for n in nodes(design)))
        design=symbolic('module divider; logic a,b; initial a=#1 b; endmodule')
        self.assertFalse(captures(design))
        self.assertTrue(any(n.get('kind')=='Unsupported' for n in nodes(design)))


if __name__ == '__main__':
    unittest.main()
