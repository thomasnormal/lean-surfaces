#!/usr/bin/env python3
"""Regression tests for the OpenVAF-backed Verilog-A extractor."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from extract import MANIFEST, ROOT, argument_path, extract


RESISTOR = ROOT / "Examples/verilog-a/resistor/resistor.va"
REVISION = "b4517adc0a21ef42e03b396373553a41174444c4"


class ExtractorTests(unittest.TestCase):
    def test_resistor_is_deterministic_and_exact(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.json"
            second = Path(directory) / "second.json"
            extract(RESISTOR, first)
            extract(RESISTOR, second)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            envelope = json.loads(first.read_text())
            self.assertEqual(envelope["frontend"]["name"], "OpenVAF Reloaded")
            self.assertEqual(envelope["frontend"]["revision"], REVISION)
            self.assertEqual(
                envelope["module"]["parameters"][0]["default"], "1k"
            )
            self.assertEqual(
                envelope["module"]["contributions"][0]["target"]["kind"], "flow"
            )

    def test_openvaf_rejects_malformed_source(self) -> None:
        self.assert_rejected("module broken(p, n); analog I(p,n) <+ ; endmodule\n")

    def test_projection_rejects_unsupported_call(self) -> None:
        self.assert_rejected(
            '`include "disciplines.vams"\n'
            "module unsupported(p, n);\n"
            "  inout p, n; electrical p, n;\n"
            "  analog I(p,n) <+ sin(V(p,n));\n"
            "endmodule\n"
        )

    def assert_rejected(self, source_text: str) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "bad.va"
            output = Path(directory) / "bad.json"
            source.write_text(source_text)
            environment = os.environ.copy()
            environment["CARGO_NET_GIT_FETCH_WITH_CLI"] = "true"
            result = subprocess.run(
                [
                    "cargo",
                    "run",
                    "--quiet",
                    "--manifest-path",
                    str(MANIFEST),
                    "--",
                    argument_path(source),
                    argument_path(output),
                ],
                cwd=ROOT,
                env=environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
