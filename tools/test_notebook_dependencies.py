#!/usr/bin/env python3
"""Exercise dependency invalidation with real, isolated Lean object files."""

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from notebook_cache import file_hash, header_key


ROOT = Path(__file__).resolve().parent.parent


@unittest.skipUnless(shutil.which("lake"), "Lake is not installed")
class CompiledDependencyTests(unittest.TestCase):
    def test_transitive_constructor_change_invalidates_an_unchanged_root(self):
        environment = dict(os.environ)
        captured = subprocess.run(
            ["lake", "env"], cwd=str(ROOT), capture_output=True,
            text=True, check=True, timeout=120,
        )
        for line in captured.stdout.splitlines():
            if "=" in line:
                name, value = line.split("=", 1)
                environment[name] = value
        compiler = shutil.which("lean", path=environment.get("PATH"))
        self.assertIsNotNone(compiler)
        with tempfile.TemporaryDirectory(prefix="notebook-dependencies-") as directory:
            root = Path(directory)
            environment["LEAN_PATH"] = directory + os.pathsep + environment.get("LEAN_PATH", "")
            leaf = root / "CacheLeaf.lean"
            entry = root / "LeanModels.lean"
            envelope = root / "program.json"
            leaf.write_text("inductive Token where\n  | none\n  | integer (value : Int)\n", encoding="utf-8")
            entry.write_text("import CacheLeaf\n", encoding="utf-8")
            envelope.write_text("{}", encoding="utf-8")

            def compile_module(source):
                completed = subprocess.run(
                    [compiler, "--root=" + directory, "-o", str(source.with_suffix(".olean")), str(source)],
                    cwd=directory, env=environment, capture_output=True,
                    text=True, timeout=120,
                )
                self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)

            compile_module(leaf)
            compile_module(entry)
            previous_root = file_hash(entry.with_suffix(".olean"))
            previous_key = header_key([("program", envelope)], compiler, environment, root)
            self.assertIsNotNone(previous_key)
            leaf.write_text(
                "inductive Token where\n  | none\n  | ellipsis\n  | integer (value : Int)\n",
                encoding="utf-8",
            )
            compile_module(leaf)
            self.assertEqual(previous_root, file_hash(entry.with_suffix(".olean")))
            current_key = header_key([("program", envelope)], compiler, environment, root)
            self.assertIsNotNone(current_key)
            self.assertNotEqual(previous_key, current_key)


if __name__ == "__main__":
    unittest.main()
