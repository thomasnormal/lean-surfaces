"""Shape checks for implicit event-control repricing."""
import unittest

from implicit_event_reprice import implicit_features


class ImplicitEventReprice(unittest.TestCase):
    def test_case_and_indexed_sensitivity_shapes(self):
        source = "@(*) begin case (state[idx]) a: y = data[idx]; endcase end"
        self.assertEqual(implicit_features(source),
                         ("at-star-paren", "begin-block", "case",
                          "indexed-select", "assignment"))

    def test_nested_control_and_system_call(self):
        source = "@* begin @(posedge clk); $display(\"x\"); y = a; end"
        self.assertEqual(implicit_features(source),
                         ("at-star-bare", "begin-block", "system-call",
                          "assignment", "nested-control"))

    def test_bare_single_assignment(self):
        self.assertEqual(implicit_features("@* y = a | b;"),
                         ("at-star-bare", "assignment"))


if __name__ == "__main__":
    unittest.main()
