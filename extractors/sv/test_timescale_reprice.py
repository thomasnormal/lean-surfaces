import unittest
from timescale_reprice import timescale_features
class TimescaleReprice(unittest.TestCase):
    def test_directive(self): self.assertIn("timescale-directive", timescale_features("`timescale 1ns/1ps\nmodule m; endmodule"))
    def test_delay(self): self.assertIn("time-observation-or-delay", timescale_features("`timescale 1ns/1ps\n#1;"))
    def test_module_time(self): self.assertIn("module-time-declaration", timescale_features("timeunit 1ns; timeprecision 1ps;"))
if __name__ == "__main__": unittest.main()
