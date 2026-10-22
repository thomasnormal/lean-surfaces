"""Shape checks for continuous-assignment delay repricing."""

import unittest

from continuous_assign_delay_reprice import continuous_assign_delay_features


class ContinuousAssignDelayReprice(unittest.TestCase):
    def test_rise_fall_vector(self):
        self.assertEqual(
            continuous_assign_delay_features(
                "dst = src",
                "module top; logic [3:0] src; wire [3:0] dst; assign #(3,7) dst = src; endmodule",
            ),
            ("delayed-assign", "rise-fall", "vector"),
        )

    def test_inertial_and_three_delay_z(self):
        self.assertEqual(
            continuous_assign_delay_features(
                "y = src ? 4'hA : 4'hz",
                "module top; logic src; wire [3:0] y; assign #(2,3,4) y = src ? 4'hA : 4'hz; // inertial cancel\nendmodule",
            ),
            ("delayed-assign", "rise-fall", "three-delays", "inertial",
             "z-transition", "vector"),
        )

    def test_strength_and_type(self):
        self.assertEqual(
            continuous_assign_delay_features(
                "w = src",
                "module top; logic src; wire w; assign (strong1, strong0) #5 w = src; endmodule",
                "/tests/chapter-37/37.2--delayterm-type.sv",
            ),
            ("delayed-assign", "strength-before-delay", "type-example"),
        )


if __name__ == "__main__":
    unittest.main()
