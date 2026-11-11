import json
import tempfile
import unittest
from pathlib import Path

import extract


class ReadmemhArguments(unittest.TestCase):
    def extract(self, source, words="00\n11\n"):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src = root / "fixture.sv"
            rom = root / "rom.hex"
            out = root / "fixture.sv.json"
            src.write_text(source)
            rom.write_text(words)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    def readmemh_nodes(self, module):
        found = []

        def walk(node):
            if isinstance(node, dict):
                if node.get("sv_kind", "").startswith("SystemTask:readmemh"):
                    found.append(node)
                for value in node.values():
                    walk(value)
            elif isinstance(node, list):
                for value in node:
                    walk(value)

        walk(module)
        return found

    def test_literal_filename_is_retained(self):
        module = self.extract(
            'module top; logic [7:0] rom [0:1]; '
            'initial $readmemh("rom.hex", rom); endmodule')
        nodes = self.readmemh_nodes(module)
        self.assertEqual(len(nodes), 1)
        self.assertEqual(nodes[0]["text"], "file=rom.hex;target=rom;data=00,11")

    def test_string_parameter_uses_elaborated_constant(self):
        module = self.extract(
            'module top #(parameter string FILE = "rom.hex"); '
            'logic [7:0] rom [0:1]; '
            'initial $readmemh(FILE, rom); endmodule')
        nodes = self.readmemh_nodes(module)
        self.assertEqual(len(nodes), 1)
        self.assertEqual(nodes[0]["text"], "file=rom.hex;target=rom;data=00,11")

    def test_dynamic_filename_stays_loud(self):
        module = self.extract(
            'module top; string FILE; logic [7:0] rom [0:1]; '
            'initial $readmemh(FILE, rom); endmodule')
        nodes = self.readmemh_nodes(module)
        self.assertEqual(len(nodes), 1)
        self.assertEqual(nodes[0]["sv_kind"], "SystemTask:readmemh:shape")
        self.assertIn("literal file", nodes[0]["text"])


if __name__ == "__main__":
    unittest.main()
