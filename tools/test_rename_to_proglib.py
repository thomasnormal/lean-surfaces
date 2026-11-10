#!/usr/bin/env python3
"""test_rename_to_proglib.py -- tests of tools/rename_to_proglib.py (no Lean, no network).

Run from anywhere: python3 tools/test_rename_to_proglib.py

The script's own --self-test builds a fixture repository covering every file class, rule, fixup,
refusal and both transplant modes; this file runs it, and checks the pieces that do not need a
repository: the map, the globs, and that the committed allowlist parses with a reason on every entry.
"""

import os
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True

import rename_to_proglib as r  # noqa: E402


class MapTest(unittest.TestCase):
    def test_spellings(self):
        self.assertEqual(r.rename_bytes(b"import LeanModels.Core"), b"import " + r.LIB.encode() + b".Core")
        self.assertEqual(r.rename_bytes(b"lake exe leanmodels-run"), b"lake exe " + r.EXE.encode())
        self.assertEqual(r.rename_bytes(b'name = "lean-models"'), b'name = "' + r.PKG.encode() + b'"')
        self.assertEqual(r.rename_bytes("\u00ablean-models\u00bb".encode("utf-8")), r.PKG.encode())
        self.assertEqual(r.rename_bytes(b"\\nLeanModels/Ada"), b"\\n" + r.LIB.encode() + b"/Ada")

    def test_idempotent(self):
        once = r.rename_bytes(b"LeanModels leanmodels-x lean_models lean-models")
        self.assertEqual(r.rename_bytes(once), once)

    def test_one_constant(self):
        self.assertEqual(r.PKG, r.LIB.lower())
        self.assertEqual(r.EXE, r.PKG + "-run")

    def test_globs(self):
        g = r.glob_to_re("**/*.sv")
        self.assertTrue(g.match("x.sv") and g.match("a/b/x.sv"))
        self.assertFalse(r.glob_to_re("docs/*.md").match("docs/a/b.md"))
        e = r.Entry("path", "LeanModels/VerilogA/Envelope.lean", None, "x", 1)
        self.assertTrue(e.matches("LeanModels/VerilogA/Envelope.lean"))
        self.assertTrue(e.matches(r.LIB + "/VerilogA/Envelope.lean"))

    def test_allowlist(self):
        rules = r.Rules.load(r.ALLOW_PATH)
        self.assertTrue(rules.entries)
        self.assertTrue(all(e.reason for e in rules.entries))
        self.assertTrue(rules.path_entry("docs/backlog/qol.md"))
        self.assertIsNone(rules.path_entry("docs/reference.md"))
        self.assertIsNotNone(rules.path_entry("tools/rename_to_proglib.py"))
        self.assertIsNotNone(rules.path_entry("docs/sv-onboarding.pdf"))
        # records keep every byte: fixup F5 (marker paths inside records) is not enabled
        self.assertFalse(rules.has_class("record-marker-paths"))

    def test_hidden_pdf_text(self):
        pdf = r._pdf(b"BT (LeanModels/Sv/**) Tj (LeanModels/Rv/**) Tj ET")
        self.assertTrue(r.is_binary(pdf))
        self.assertEqual(r.CHECK_RE.findall(pdf), [])
        self.assertEqual(r.hidden_hits(pdf), 2)
        self.assertEqual(r.hidden_hits(b"plain LeanModels text"), 0)


class SelfTest(unittest.TestCase):
    def test_self_test(self):
        p = subprocess.run([sys.executable, os.path.join(HERE, "rename_to_proglib.py"), "--self-test"],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        self.assertEqual(p.returncode, 0, p.stdout.decode("utf-8", "replace"))


if __name__ == "__main__":
    unittest.main()
