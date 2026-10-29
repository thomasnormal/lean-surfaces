"""The local two-state declaration fixture stays on the self-check path."""
import json
import unittest
from pathlib import Path

import census
import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "Examples/system-verilog/local_2state_declarations/local_2state_declarations.sv"


class LocalTwoStateFixture(unittest.TestCase):
    def test_envelope_has_local_decls_without_unsupported_nodes(self):
        envelope = json.loads(Path(str(SOURCE) + ".json").read_text())
        body = envelope["design"]["modules"][0]["processes"][0]["body"]
        self.assertEqual(body["kind"], "Block")
        self.assertEqual([s["kind"] for s in body["stmts"]],
                         ["Empty", "Empty", "SysCall", "SysCall"])
        decls = envelope["design"]["modules"][0]["decls"]
        self.assertEqual([d["name"] for d in decls], ["flag", "nibble"])
        self.assertTrue(all(d["static_local_storage"] for d in decls))

    def test_adapter_fixture_has_no_residual_blockers(self):
        source = SOURCE.read_text()
        tree = SyntaxTree.fromText(source, name=str(SOURCE))
        compilation = Compilation()
        compilation.addSyntaxTree(tree)
        extract._SOURCE_BYTES = source.encode()
        census.extract = extract
        self.assertEqual(census.adapter_design_blockers(tree.sourceManager, compilation), [])


if __name__ == "__main__":
    unittest.main()
