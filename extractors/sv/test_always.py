"""Plain IEEE 9.2.2.1 source repetition over the retained loop interface."""
from pathlib import Path
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=PlainAlways | origin=spec | authority=IEEE-1800-2023#9.2.2.1 | map=source-process:retain-body-and-kind;boundaries:existing-waits-lifetimes-invalid-source


class PlainAlways(unittest.TestCase):
    def test_plain_source_kind_retains_entire_body(self):
        for body in ("begin #2; end", "#2;", "@(negedge signal_value);", "@(signal_value);"):
            design = lower("module top; logic signal_value; always " + body + " endmodule")
            process, = design["modules"][0]["processes"]
            self.assertEqual(process["kind"], "Always")
            self.assertTrue(process["always_lowered"])
            self.assertIn("body", process)
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_canonical_positive_edge_encoding_is_preserved(self):
        design = lower("module top; logic clk; always @(posedge clk); endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual((process["kind"], process["clock"], process["style"]), ("AlwaysPosedge", "clk", "always"))

    def test_always_ff_negative_edge_is_retained(self):
        design = lower("module top; logic clk; logic q; always_ff @(negedge clk) q <= 1'b1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual((process["kind"], process["clock"], process["style"], process["edge"]),
                         ("AlwaysPosedge", "clk", "always_ff", "neg"))

    def test_always_ff_active_high_reset_is_retained(self):
        design = lower(
            "module top; logic clk, rst, q; always_ff @(posedge clk or posedge rst) "
            "if (rst) q <= 1'b0; else q <= 1'b1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual((process["kind"], process["clock"], process["areset"]),
                         ("AlwaysPosedge", "clk", "rst"))

    def test_always_ff_scalar_iff_guard_is_retained(self):
        design = lower(
            "module top; logic clk, en, q; "
            "always_ff @(posedge clk iff en) q <= 1'b1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual((process["kind"], process["style"], process["clock"]),
                         ("AlwaysPosedge", "always_ff", "clk"))
        self.assertEqual(process["iff"]["name"], "en")

    def test_always_ff_negative_scalar_iff_guard_is_retained(self):
        design = lower(
            "module top; logic clk, en, q; "
            "always_ff @(negedge clk iff en) q <= 1'b1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual((process["kind"], process["style"], process["clock"],
                          process["edge"]),
                         ("AlwaysPosedge", "always_ff", "clk", "neg"))
        self.assertEqual(process["iff"]["name"], "en")

    def test_plain_multi_signal_event_list_is_retained(self):
        design = lower(
            "module top; logic a,b,y; always @(a or b) y = a ^ b; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["kind"], "AlwaysEvent")
        self.assertEqual(process["events"], [
            {"signal": "a", "edge": "any"},
            {"signal": "b", "edge": "any"},
        ])

    def test_plain_bare_signal_event_is_retained(self):
        design = lower(
            "module top; logic trigger, seen; always @(trigger) seen = 1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["kind"], "AlwaysEvent")
        self.assertEqual(process["events"], [{"signal": "trigger", "edge": "any"}])

    def test_plain_scalar_iff_guard_is_retained(self):
        design = lower(
            "module top; logic clk, en, seen; "
            "always @(posedge clk iff en) seen = 1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["kind"], "AlwaysEvent")
        self.assertEqual(process["events"][0]["signal"], "clk")
        self.assertEqual(process["events"][0]["edge"], "posedge")
        self.assertEqual(process["events"][0]["iff"]["name"], "en")

    def test_plain_event_list_scalar_iff_guards_are_retained(self):
        design = lower(
            "module top; logic a, b, en, seen; "
            "always @(posedge a iff en or negedge b iff en) seen = 1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["kind"], "AlwaysEvent")
        self.assertEqual([event["iff"]["name"] for event in process["events"]],
                         ["en", "en"])

    def test_comparison_iff_guard_is_retained(self):
        design = lower(
            "module top; logic clk, en, seen; "
            "always @(posedge clk iff en == 1'b1) seen = 1; endmodule",
            require_valid=False)
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["kind"], "AlwaysEvent")
        self.assertEqual(process["events"][0]["iff"]["op"], "==")

    def test_always_ff_comparison_iff_guard_is_retained(self):
        design = lower(
            "module top; logic clk, en, q; "
            "always_ff @(posedge clk iff en == 1'b1) q <= 1'b1; endmodule",
            require_valid=False)
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["kind"], "AlwaysPosedge")
        self.assertEqual(process["iff"]["op"], "==")

    def test_always_ff_async_reset_clock_iff_is_retained(self):
        design = lower(
            "module top; logic clk, rst_n, en, q; "
            "always_ff @(posedge clk iff en or negedge rst_n) "
            "if (!rst_n) q <= 1'b0; else q <= 1'b1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual((process["kind"], process["style"], process["clock"],
                          process["areset_n"]),
                         ("AlwaysPosedge", "always_ff", "clk", "rst_n"))
        self.assertEqual(process["iff"]["name"], "en")

    def test_always_ff_async_reset_vector_bit_iff_is_retained(self):
        design = lower(
            "module top; logic clk, rst_n, q; logic [1:0] en; "
            "always_ff @(posedge clk iff en[0] or negedge rst_n) "
            "if (!rst_n) q <= 1'b0; else q <= 1'b1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["iff"]["kind"], "SelectRead")
        self.assertEqual(process["iff"]["value"]["name"], "en")
        self.assertEqual(process["iff"]["index"]["bits"], "00000000000000000000000000000000")

    def test_always_ff_async_reset_active_high_clock_iff_is_retained(self):
        design = lower(
            "module top; logic clk, rst, en, q; "
            "always_ff @(posedge clk iff en or posedge rst) "
            "if (rst) q <= 1'b0; else q <= 1'b1; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual((process["kind"], process["style"], process["clock"],
                          process["areset"]),
                         ("AlwaysPosedge", "always_ff", "clk", "rst"))
        self.assertEqual(process["iff"]["name"], "en")

    def test_always_ff_async_reset_iff_on_reset_is_retained(self):
        design = lower(
            "module top; logic clk, rst_n, en, q; "
            "always_ff @(posedge clk or negedge rst_n iff en) "
            "q <= 1'b0; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["reset_iff"]["name"], "en")

    def test_always_ff_async_reset_active_high_iff_on_reset_is_retained(self):
        design = lower(
            "module top; logic clk, rst, en, q; "
            "always_ff @(posedge clk or posedge rst iff en) "
            "q <= 1'b0; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["reset_iff"]["name"], "en")

    def test_always_ff_async_reset_iff_call_stays_loud(self):
        design = lower(
            "module top; logic clk, rst_n, en, q; "
            "always_ff @(posedge clk or negedge rst_n iff f(en)) "
            "q <= 1'b0; endmodule", require_valid=False)
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_always_ff_vector_range_iff_is_retained(self):
        design = lower(
            "module top; logic clk, rst_n, q; logic [1:0] en; "
            "always_ff @(posedge clk iff en[1:0] or negedge rst_n) "
            "q <= 1'b0; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["iff"]["kind"], "SelectRead")
        self.assertEqual(process["iff"]["width"], 2)

    def test_always_ff_dynamic_vector_iff_is_retained(self):
        design = lower(
            "module top; logic clk, q; logic [3:0] en; integer i; "
            "always_ff @(posedge clk iff en[i +: 2]) q <= 1'b0; endmodule",
            require_valid=False)
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["iff"]["kind"], "SelectRead")
        self.assertEqual(process["iff"]["width"], 2)

    def test_always_ff_descending_dynamic_vector_iff_is_retained(self):
        design = lower(
            "module top; logic clk, q; logic [3:0] en; integer i; "
            "always_ff @(posedge clk iff en[i -: 2]) q <= 1'b0; endmodule",
            require_valid=False)
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["iff"]["kind"], "SelectRead")
        self.assertTrue(process["iff"]["descending"])

    def test_always_ff_concat_iff_is_retained(self):
        design = lower(
            "module top; logic clk, q; logic [1:0] en; "
            "always_ff @(posedge clk iff {en[1], en[0]}) q <= 1'b0; endmodule")
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["iff"]["kind"], "Concat")

    def test_always_ff_concat_replication_iff_stays_loud(self):
        design = lower(
            "module top; logic clk, q; logic en; "
            "always_ff @(posedge clk iff {2{en}}) q <= 1'b0; endmodule",
            require_valid=False)
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_logical_iff_guard_is_retained(self):
        design = lower(
            "module top; logic clk, en, mode, seen; "
            "always @(posedge clk iff en && mode) seen = 1; endmodule",
            require_valid=False)
        process, = design["modules"][0]["processes"]
        self.assertEqual(process["kind"], "AlwaysEvent")
        self.assertEqual(process["events"][0]["iff"]["op"], "&&")

    def test_always_ff_is_not_reinterpreted_as_general_repetition(self):
        design = lower("module top; logic q; always_ff begin #2 q=1; end endmodule", require_valid=False)
        self.assertFalse(any(n.get("kind") == "Always" for n in nodes(design)))
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_implicit_compound_and_iff_sensitivities_stay_loud(self):
        for body in ("@*;", "@(a or b);", "@(negedge a iff b);"):
            design = lower("module top; logic a,b; always " + body + " endmodule")
            self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_level_wait_is_retained_for_timed_path(self):
        design = lower(
            "module top; logic ready; always begin wait (ready); ready = 1; end endmodule"
        )
        body = design["modules"][0]["processes"][0]["body"]
        self.assertEqual(body["kind"], "Block")
        self.assertEqual(body["stmts"][0]["kind"], "WaitCond")
        self.assertEqual(body["stmts"][0]["condition"]["name"], "ready")

    def test_repeated_static_scalar_is_initialized_once(self):
        design = lower("module top; always begin int value=1; #2; value++; end endmodule")
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))
        self.assertTrue(any(n.get("static_local_storage") for n in nodes(design)))

    def test_illegal_loop_transfers_do_not_become_legal(self):
        for body in ("break;", "continue;"):
            design = lower("module top; always " + body + " endmodule", require_valid=False)
            self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_frontend_error_remains_a_design_barrier(self):
        design = lower("module top; always #2; initial missing=1; endmodule", require_valid=False)
        self.assertIn("Always:invalid-compilation", [n.get("sv_kind") for n in nodes(design)])

    def test_symbolic_path_keeps_its_existing_boundary(self):
        design = symbolic("module divider; always begin #2; end endmodule")
        self.assertFalse(any(n.get("kind") == "Always" for n in nodes(design)))
        self.assertIn("ProceduralBlockSymbol:NoEventControl", [n.get("sv_kind") for n in nodes(design)])

    def test_authored_sources_have_no_extraction_walls(self):
        root = Path(__file__).resolve().parents[2] / "Examples/system-verilog/always"
        for p in root.glob("*.sv"):
            design = lower(p.read_text())
            self.assertTrue(any(n.get("kind") == "Always" for n in nodes(design)))
            self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_same_slot_double_write_fixture_is_timed_and_clean(self):
        path = (Path(__file__).resolve().parents[2] /
                "Examples/system-verilog/always_comb_double_write/always_comb_double_write.sv")
        design = lower(path.read_text())
        processes = design["modules"][0]["processes"]
        self.assertEqual([p["kind"] for p in processes], ["AlwaysComb", "Initial"])
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_dynamic_net_resolution_fixture_retains_all_drivers(self):
        path = (Path(__file__).resolve().parents[2] /
                "Examples/system-verilog/assign_net_resolution/assign_net_resolution.sv")
        design = lower(path.read_text())
        processes = design["modules"][0]["processes"]
        self.assertEqual([p["kind"] for p in processes], ["Assign", "Assign", "Initial"])
        self.assertEqual([p["target"]["name"] for p in processes[:2]], ["y", "y"])
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))


if __name__ == "__main__":
    unittest.main()
