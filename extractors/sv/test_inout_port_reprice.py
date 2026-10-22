"""Shape checks for PortSymbol:InOut repricing."""
import unittest

from inout_port_reprice import inout_features


class InOutPortReprice(unittest.TestCase):
    def test_initializer_and_interconnect_diagnostics(self):
        self.assertEqual(
            inout_features("module m(inout wire logic z = 1'b0); endmodule",
                           "z = 1'b0"),
            ("inout-initializer",))
        self.assertEqual(
            inout_features("module m(interconnect w = 1'b0); endmodule",
                           "w = 1'b0"),
            ("interconnect-initializer",))

    def test_ansi_port_type_reset_shapes(self):
        self.assertEqual(
            inout_features("module m(wire x, y[7:0]); endmodule", "y[7:0]"),
            ("unpacked-dimension-not-inherited",))
        self.assertEqual(
            inout_features("module m(integer x, signed [5:0] y); endmodule",
                           "y"),
            ("integer-then-signed-type-reset",))
        self.assertEqual(
            inout_features("module m([5:0] x, wire y); endmodule", "y"),
            ("packed-dimension-then-wire-reset",))

    def test_generic_interface_and_signed_interconnect(self):
        self.assertEqual(
            inout_features("module m(a, clk); interface a; input logic clk; "
                           "endmodule", ""),
            ("generic-interface-nonansi",))
        self.assertEqual(
            inout_features("module m(interconnect signed w); endmodule", "w"),
            ("interconnect-signed",))


if __name__ == "__main__":
    unittest.main()
