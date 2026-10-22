"""Shape checks for the deferred immediate-assertion instrument."""
import unittest

from immediate_assert_deferred_reprice import deferred_features


class ImmediateAssertDeferredReprice(unittest.TestCase):
    def test_observed_hash0_call_action(self):
        labels = deferred_features(
            'assert #0 (a) else $display("fail");',
            "always @(posedge clk) begin assert #0 (a); end",
        )
        self.assertIn("hash0", labels)
        self.assertIn("observed-region", labels)
        self.assertIn("single-system-call-action", labels)
        self.assertIn("always-context", labels)

    def test_final_is_postponed(self):
        labels = deferred_features(
            "assert final (done) else $display(\"fail\");", "")
        self.assertIn("final", labels)
        self.assertIn("postponed-region", labels)
        self.assertIn("static-module-context", labels)

    def test_null_and_protected_shapes(self):
        labels = deferred_features(
            "c1: cover #0 (x);",
            "`pragma protect begin\ncover #0 (x);\n`pragma protect end",
        )
        self.assertIn("cover", labels)
        self.assertIn("null-action", labels)
        self.assertIn("protected-region", labels)


if __name__ == "__main__":
    unittest.main()
