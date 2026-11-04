import json
import tempfile
import unittest
from pathlib import Path

import extract


class CountonesLowering(unittest.TestCase):
    def test_fixed_four_state_vector_is_lowered(self):
        source = """module t (input logic [7:0] a, output logic [31:0] y);
          assign y = $countones(a);
        endmodule"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "t.sv"
            out = Path(directory) / "t.sv.json"
            src.write_text(source)
            extract.process_symbolic("t", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]
        process = module["processes"][0]
        self.assertEqual(module["others"], [])
        self.assertTrue(process["value"].get("countones_lowered"))
        self.assertEqual(process["value"]["width"], 32)

    def test_parameter_dependent_width_stays_loud(self):
        source = """module t #(parameter int N = 8) (input logic [N-1:0] a,
          output logic [31:0] y);
          assign y = $countones(a);
        endmodule"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "t.sv"
            out = Path(directory) / "t.sv.json"
            src.write_text(source)
            extract.process_symbolic("t", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]
        def has_unsupported(node):
            if isinstance(node, dict):
                return (node.get("kind") == "Unsupported"
                        or any(has_unsupported(value) for value in node.values()))
            if isinstance(node, list):
                return any(has_unsupported(value) for value in node)
            return False
        self.assertTrue(has_unsupported(module["processes"]))

    def test_fixed_onehot_queries_are_lowered(self):
        source = """module t (input logic [7:0] a, output logic one, output logic zero);
          assign one = $onehot(a);
          assign zero = $onehot0(a);
        endmodule"""
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "t.sv"
            out = Path(directory) / "t.sv.json"
            src.write_text(source)
            extract.process_symbolic("t", [str(src)], [], str(out))
            module = json.loads(out.read_text())["design"]["modules"][0]
        values = [p["value"] for p in module["processes"]]
        self.assertEqual([v.get("onehot_lowered") for v in values],
                         ["$onehot", "$onehot0"])
        self.assertTrue(all(v["width"] == 1 for v in values))


if __name__ == "__main__":
    unittest.main()
