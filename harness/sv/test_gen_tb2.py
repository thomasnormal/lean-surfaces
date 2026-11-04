import unittest

import gen_tb2


class NestedPortTestbench(unittest.TestCase):
    def test_reconstructs_multidimensional_flattened_ports(self):
        ports = [
            ("a[1][2]", "in", 4, True),
            ("a[1][1]", "in", 4, True),
            ("a[0][2]", "in", 4, True),
            ("a[0][1]", "in", 4, True),
            ("y[1][2]", "out", 4, True),
            ("y[1][1]", "out", 4, True),
            ("y[0][2]", "out", 4, True),
            ("y[0][1]", "out", 4, True),
        ]
        case = {
            "name": "nested",
            "signals": ["a[1][2]", "y[0][1]"],
            "stimulus": [{"a[1][2]": "1010"}],
        }
        text = gen_tb2.generate_tb2("top", ports, case)
        self.assertIn("logic signed [3:0] a [1:0] [2:1];", text)
        self.assertIn("logic signed [3:0] y [1:0] [2:1];", text)
        self.assertIn("top dut (.a(a), .y(y));", text)
        self.assertIn("a[1][2] = 4'b1010;", text)
        self.assertIn("dut.y[0][1]", text)


if __name__ == "__main__":
    unittest.main()
