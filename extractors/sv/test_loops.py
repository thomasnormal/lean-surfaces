"""IEEE 12.7 source phases and count typing; runtime values are fixture-owned."""

from pathlib import Path
import unittest

from test_bit_queries import lower, nodes


class Loops(unittest.TestCase):
    def test_fixtures_are_admitted(self):
        sources = sorted((Path(__file__).resolve().parents[2] / "harness/sv/loops").glob("*.sv"))
        self.assertEqual(len(sources), 3)
        for source in sources:
            with self.subTest(source=source.name):
                design = lower(source.read_text())
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_header_order_and_omissions(self):
        design = lower("module top; integer first, second; initial begin "
                       "for(first=0,second=first;first<3;first++,second=first) ; "
                       "for(;;) break; end endmodule")
        loops = [node for node in nodes(design) if node.get("kind") == "For"]
        self.assertEqual([node["target"]["name"] for node in loops[0]["initializers"]],
                         ["first", "second"])
        self.assertEqual([node["target"]["name"] for node in loops[0]["steps"]],
                         ["first", "second"])
        self.assertEqual(loops[1]["condition"]["bits"], "1")
        self.assertEqual(loops[1]["steps"], [])

    def test_repeat_preserves_width_and_signedness(self):
        design = lower("module top; logic [63:0] wide_count; logic signed [3:0] narrow_count; "
                       "initial begin repeat(wide_count) ; repeat(narrow_count) ; end endmodule")
        loops = [node for node in nodes(design) if node.get("kind") == "Repeat"]
        self.assertEqual([loop["count"]["width"] for loop in loops], [64, 4])
        self.assertEqual([loop["count_signed"] for loop in loops], [False, True])

    def test_effectful_count_stays_loud(self):
        design = lower("module top; integer count; initial repeat(count++) ; endmodule")
        self.assertIn("RepeatLoopStatement:count", [node.get("sv_kind") for node in nodes(design)])

    def test_effectful_condition_stays_loud(self):
        design = lower("module top; integer count; initial for(;count++;) ; endmodule")
        self.assertIn("ForLoopStatement:condition", [node.get("sv_kind") for node in nodes(design)])

    def test_invalid_compilation_stays_loud(self):
        design = lower("module top; integer count; initial repeat(2) count+=1; "
                       "initial missing=1; endmodule", require_valid=False)
        self.assertIn("Loop:invalid-compilation", [node.get("sv_kind") for node in nodes(design)])

    def test_static_body_declaration_is_hoisted(self):
        design = lower("module top; initial repeat(2) begin integer value=0; value+=1; end endmodule")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))
        self.assertTrue(any(node.get("static_local_storage") for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
