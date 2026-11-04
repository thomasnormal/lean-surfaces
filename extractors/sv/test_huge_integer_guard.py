"""The symbolic extractor must not cross Python's decimal digit guard."""

import json
import tempfile
import unittest
from pathlib import Path

import extract


class HugeIntegerGuard(unittest.TestCase):
    def test_svint_decimal_conversion_is_loud_instead_of_raising(self):
        class TooWide:
            def __int__(self):
                raise ValueError("Exceeds the limit (4300) for integer string conversion")

        self.assertIsNone(extract._svint_to_int(TooWide()))

    def test_wide_binary_literal_keeps_bits_without_decimal_rendering(self):
        source = ("module top(output logic [19999:0] y); assign y = 20000'b"
                  + "1" + "0" * 19999 + "; endmodule\n")
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "top.sv"
            out = Path(directory) / "top.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            envelope = json.loads(out.read_text())
        value = envelope["design"]["modules"][0]["processes"][0]["value"]
        self.assertEqual(value["kind"], "Literal")
        self.assertEqual(len(value["bits"]), 20000)


if __name__ == "__main__":
    unittest.main()
