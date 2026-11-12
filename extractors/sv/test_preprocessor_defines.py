"""`-D NAME[=VALUE]` reaches Slang's preprocessor in both modes."""

import json
import tempfile
import unittest
from pathlib import Path

import extract


class PreprocessorDefinesTests(unittest.TestCase):
    source = """\
`ifdef FEATURE
module top(input logic a, output logic y);
  assign y = a;
endmodule
`else
module top(input logic a, output logic y);
  assign y = ~a;
endmodule
`endif
"""

    def extract(self, defines):
        with tempfile.TemporaryDirectory(prefix="sv-predefine-") as td:
            src = Path(td) / "top.sv"
            out = Path(td) / "top.json"
            src.write_text(self.source, encoding="utf-8")
            self.assertEqual(
                extract.main(["--top", "top", "-o", str(out),
                              *sum((["-D", d] for d in defines), []),
                              str(src)]), 0)
            return json.loads(out.read_text(encoding="utf-8"))

    def test_symbolic_name_and_value_defines_select_the_preprocessed_node(self):
        named = self.extract(["FEATURE"])
        valued = self.extract(["FEATURE=1"])
        absent = self.extract([])
        named_value = named["design"]["modules"][0]["processes"][0]["value"]
        valued_value = valued["design"]["modules"][0]["processes"][0]["value"]
        absent_value = absent["design"]["modules"][0]["processes"][0]["value"]
        self.assertEqual(named_value["kind"], "Ident")
        self.assertEqual(valued_value, named_value)
        self.assertEqual(absent_value["kind"], "Unary")
        self.assertEqual(absent_value["op"], "~")

    def test_flat_mode_accepts_a_define(self):
        with tempfile.TemporaryDirectory(prefix="sv-predefine-flat-") as td:
            src = Path(td) / "top.sv"
            src.write_text(self.source, encoding="utf-8")
            self.assertEqual(extract.main(["-D", "FEATURE=1", str(src)]), 0)
            envelope = json.loads((Path(str(src) + ".json")).read_text())
            self.assertEqual(envelope["design"]["modules"][0]["name"], "top")

    def test_probe_reextraction_keeps_the_define(self):
        source = """\
`ifdef FEATURE
module top #(parameter int N = 1)(output logic y);
  assign y = N[0];
endmodule
`else
module top #(parameter int N = 1)(output logic y);
  assign y = 1'b0;
endmodule
`endif
"""
        with tempfile.TemporaryDirectory(prefix="sv-predefine-probe-") as td:
            src = Path(td) / "top.sv"
            out = Path(td) / "top.json"
            src.write_text(source, encoding="utf-8")
            self.assertEqual(
                extract.main(["--top", "top", "-D", "FEATURE",
                              "--probe-points", "N=1", "-o", str(out),
                              str(src)]), 0)
            side = json.loads(Path(str(out)[:-5] + ".probes.json").read_text())
            self.assertEqual(side["points"][0]["module"]["processes"][0]
                             ["value"]["kind"], "BitSel")


if __name__ == "__main__":
    unittest.main()
