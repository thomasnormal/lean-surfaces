"""Package enum metadata in sv-0.2 parameter defaults."""

import json
import tempfile
import unittest
from pathlib import Path

import extract


class SymbolicPackageEnumDefaults(unittest.TestCase):
    def test_qualified_enum_default_stays_source_shaped(self):
        source = (
            "package p; typedef enum logic [1:0] {IDLE=0, RUN=1} state_t; "
            "endpackage module top #(parameter p::state_t S = p::RUN) ("
            "input logic [1:0] a, output logic [1:0] y); "
            "always_comb if (a == S) y = p::RUN; else y = p::IDLE; endmodule"
        )
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "top.sv"
            out = Path(directory) / "top.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]

        param = module["params"][0]
        self.assertEqual(param["type"]["kind"], "TypeRef")
        self.assertEqual(param["type"]["from_package"], "p")
        self.assertEqual(param["default"]["kind"], "EnumRef")
        self.assertEqual(param["default"]["from_package"], "p")
        self.assertEqual(param["default"]["member"], "RUN")
        self.assertEqual([(t["name"], t["from_package"])
                          for t in module["types"]], [("state_t", "p")])
        self.assertFalse(any(n.get("kind") == "Unsupported"
                             for n in module["processes"]))


if __name__ == "__main__":
    unittest.main()
