"""Constant selected continuous drivers stay in the existing sv-0.2 window tier."""
import json
import tempfile
import unittest
from pathlib import Path

import extract


class SymbolicContinuousSelects(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())

    def test_disjoint_constant_parts_keep_windows(self):
        envelope = self.extract(
            "module top(input logic [3:0] nibble, output logic [7:0] value); "
            "assign value[3:0] = nibble; assign value[7:4] = 4'ha; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([p["target"]["kind"] for p in processes],
                         ["PartSel", "PartSel"])
        self.assertEqual([(p["target"]["msb"]["value"],
                           p["target"]["lsb"]["value"]) for p in processes],
                         [(3, 0), (7, 4)])

    def test_disjoint_constant_bits_keep_windows(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, input logic flag, "
            "output logic [7:0] value); "
            "assign value[1] = source[0]; assign value[6] = flag; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([p["target"]["kind"] for p in processes],
                         ["BitSel", "BitSel"])
        self.assertEqual([p["target"]["index"]["value"] for p in processes],
                         [1, 6])


if __name__ == "__main__":
    unittest.main()
