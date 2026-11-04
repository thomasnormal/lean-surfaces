"""Shape checks for elaboration-invalid repricing."""
import unittest

from elaboration_invalid_reprice import elaboration_features


class ElaborationInvalidReprice(unittest.TestCase):
    def test_name_conflict_and_nonconstant_scheme(self):
        self.assertEqual(
            elaboration_features(
                ":diagnostic_match: redefinition of 'blk'\n"
                "if (0) begin : blk end"),
            ("generate-scope-name-conflict",))
        self.assertEqual(
            elaboration_features(
                "logic dyn; if (dyn) begin : g end"),
            ("nonconstant-generate-scheme",))

    def test_region_and_genvar_shapes(self):
        self.assertEqual(
            elaboration_features("generate if (1) begin : g end"),
            ("generate-region-delimiter",))
        self.assertEqual(
            elaboration_features(
                "generate generate if (1) begin : g end "
                "endgenerate endgenerate"),
            ("nested-generate-region",))
        self.assertEqual(
            elaboration_features("genvar i; case (i) 0: logic x; endcase"),
            ("genvar-outside-loop-scheme",))

    def test_macro_port_and_end_label(self):
        self.assertEqual(
            elaboration_features("`ifndef (A && B) x `endif"),
            ("macro-conditional-expression",))
        self.assertEqual(
            elaboration_features("generate begin : g input logic p; "
                                 "end endgenerate"),
            ("generate-port-declaration",))
        self.assertEqual(
            elaboration_features("generate begin : g end : wrong "
                                 "endgenerate"),
            ("generate-end-label-mismatch",))


if __name__ == "__main__":
    unittest.main()
