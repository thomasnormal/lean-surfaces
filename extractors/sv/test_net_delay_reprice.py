"""Shape checks for delayed-net repricing."""

import unittest

from net_delay_reprice import net_delay_features


class NetDelayReprice(unittest.TestCase):
    def test_declaration_continuous_assignment_and_rise_fall(self):
        self.assertEqual(
            net_delay_features(
                "w = src",
                "module top; wire [3:0] #(10, 5) w = src; endmodule",
            ),
            ("net-delay", "continuous-assign-delay", "rise-fall", "vector"),
        )

    def test_bare_net_delay_is_not_ca_delay(self):
        self.assertEqual(
            net_delay_features(
                "w",
                "module top; wire #5 w; assign w = src; endmodule",
            ),
            ("net-delay",),
        )

    def test_min_typ_max_turnoff_z_and_type(self):
        self.assertEqual(
            net_delay_features(
                "n",
                "module top; wire #(1:3:5, 2, 4) n; logic x; initial x = 1'bz; endmodule",
                "/tests/chapter-37/37.2--delaydevice-type.sv",
            ),
            ("net-delay", "rise-fall", "turnoff", "min-typ-max",
             "z-transition", "type-example"),
        )


if __name__ == "__main__":
    unittest.main()
