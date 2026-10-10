#!/usr/bin/env python3
"""Check header invalidation without Lean; wiring tests skip without IPython."""

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

import notebook_cache


class NotebookCacheTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.compiler = self.root / "lean"
        self.compiler.write_bytes(b"compiler-a")
        self.dependency = self.root / "transitive.olean"
        self.dependency.write_bytes(b"definition-a")
        self.envelope = self.root / "program.json"
        self.envelope.write_text('{"module": {"body": []}}', encoding="utf-8")
        self.artifact = self.root / "NotebookHeader.olean"
        self.artifact.write_bytes(b"header-a")
        self.metadata = self.root / "header_cache.meta"
        self.environment = {"LEAN_PATH": str(self.root)}
        self.completed = subprocess.CompletedProcess(
            [], 0, json.dumps([str(self.dependency)]), "",
        )
        probe_patch = patch("notebook_cache.subprocess.run", return_value=self.completed)
        self.probe = probe_patch.start()
        self.addCleanup(probe_patch.stop)

    def key(self, envelopes=None, compiler=None):
        return notebook_cache.header_key(
            envelopes if envelopes is not None else [("program", self.envelope)],
            str(self.compiler) if compiler is None else compiler,
            self.environment, self.root,
        )

    def replace_preserving_metadata(self, path, data):
        previous = path.stat()
        self.assertEqual(len(data), previous.st_size)
        path.write_bytes(data)
        os.utime(path, ns=(previous.st_atime_ns, previous.st_mtime_ns))

    def test_unchanged_inputs_reuse_the_header(self):
        key = self.key()
        self.assertIsNotNone(key)
        self.assertEqual(key, self.key())
        notebook_cache.store_header(self.metadata, key, self.artifact)
        self.assertTrue(notebook_cache.cached_header(self.metadata, key, self.artifact))

    def test_transitive_content_change_invalidates_even_with_same_size_and_time(self):
        previous = self.key()
        self.replace_preserving_metadata(self.dependency, b"definition-b")
        self.assertNotEqual(previous, self.key())

    def test_compiler_content_change_invalidates_the_header(self):
        previous = self.key()
        self.replace_preserving_metadata(self.compiler, b"compiler-b")
        self.assertNotEqual(previous, self.key())

    def test_split_objects_ir_and_native_runtime_contents_are_hashed(self):
        for name in ("transitive.olean.private", "transitive.ir.sig", "transitive.ir", "runtime.so"):
            with self.subTest(name=name):
                artifact = self.root / name
                artifact.write_bytes(b"part-a")
                self.completed.stdout = json.dumps([str(self.dependency), str(artifact)])
                previous = self.key()
                self.replace_preserving_metadata(artifact, b"part-b")
                self.assertNotEqual(previous, self.key())

    def test_resolved_import_path_is_part_of_the_key(self):
        previous = self.key()
        shadow = self.root / "shadow.olean"
        shadow.write_bytes(self.dependency.read_bytes())
        self.completed.stdout = json.dumps([str(shadow)])
        self.assertNotEqual(previous, self.key())

    def test_relative_import_paths_resolve_from_the_compiler_working_directory(self):
        previous = self.key()
        self.completed.stdout = json.dumps([self.dependency.name])
        self.assertEqual(previous, self.key())

    def test_dependency_order_and_duplicates_do_not_change_the_key(self):
        previous = self.key()
        self.completed.stdout = json.dumps([str(self.dependency), str(self.dependency)])
        self.assertEqual(previous, self.key())

    def test_envelope_contents_invalidate_the_header(self):
        previous = self.key()
        self.envelope.write_text('{"module": {"body": [1]}}', encoding="utf-8")
        self.assertNotEqual(previous, self.key())

    def test_envelope_binding_name_is_part_of_the_key(self):
        self.assertNotEqual(self.key(), self.key([("renamed", self.envelope)]))

    def test_probe_uses_the_selected_compiler_and_environment(self):
        self.key()
        arguments, options = self.probe.call_args
        self.assertEqual(arguments[0], [str(self.compiler), "--run", str(notebook_cache.DEPENDENCY_PROBE)])
        self.assertEqual(options["cwd"], str(self.root))
        self.assertIs(options["env"], self.environment)

    def test_unknown_compiler_never_produces_a_cache_key(self):
        self.assertIsNone(self.key(compiler=""))
        self.probe.assert_not_called()

    def test_failed_dependency_probe_never_produces_a_cache_key(self):
        self.completed.returncode = 1
        self.assertIsNone(self.key())

    def test_timeout_never_produces_a_cache_key(self):
        self.probe.side_effect = subprocess.TimeoutExpired("lean", 120)
        self.assertIsNone(self.key())

    def test_malformed_dependency_inventory_never_produces_a_cache_key(self):
        for payload in ("not JSON", "null", "{}", '"path"', "[]", "[null]", '[""]'):
            with self.subTest(payload=payload):
                self.completed.stdout = payload
                self.assertIsNone(self.key())

    def test_missing_compiled_dependency_never_produces_a_cache_key(self):
        self.dependency.unlink()
        self.assertIsNone(self.key())

    def test_corrupted_header_invalidates_even_with_same_size_and_time(self):
        key = self.key()
        notebook_cache.store_header(self.metadata, key, self.artifact)
        self.replace_preserving_metadata(self.artifact, b"header-b")
        self.assertFalse(notebook_cache.cached_header(self.metadata, key, self.artifact))

    def test_changed_dependency_key_rejects_old_metadata(self):
        previous = self.key()
        notebook_cache.store_header(self.metadata, previous, self.artifact)
        self.dependency.write_bytes(b"changed")
        self.assertFalse(notebook_cache.cached_header(self.metadata, self.key(), self.artifact))

    def test_unknown_dependency_key_rejects_existing_metadata(self):
        notebook_cache.store_header(self.metadata, self.key(), self.artifact)
        self.assertFalse(notebook_cache.cached_header(self.metadata, None, self.artifact))

    def test_old_or_partial_metadata_is_a_cache_miss(self):
        key = self.key()
        for payload in ("program old-hash", "{", "null", "[]", '{"version": 0}'):
            with self.subTest(payload=payload):
                self.metadata.write_text(payload, encoding="utf-8")
                self.assertFalse(notebook_cache.cached_header(self.metadata, key, self.artifact))

    def test_missing_header_is_a_cache_miss(self):
        key = self.key()
        notebook_cache.store_header(self.metadata, key, self.artifact)
        self.artifact.unlink()
        self.assertFalse(notebook_cache.cached_header(self.metadata, key, self.artifact))


class HeaderWiringTests(unittest.TestCase):
    def setUp(self):
        try:
            import lean_magic
        except ImportError:
            self.skipTest("IPython is not installed")
        self.magic_module = lean_magic
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.work = self.root / "work"
        self.metadata = self.work / "header_cache.meta"
        self.artifact = self.work / "NotebookHeader.olean"
        overrides = patch.multiple(
            lean_magic, REPO_ROOT=self.root, WORK_DIR=self.work,
            CELLS_DIR=self.work / "cells", HEADER_CACHE=self.metadata, _show=Mock(),
        )
        overrides.start()
        self.addCleanup(overrides.stop)
        self.magics = lean_magic.LeanMagics(None)
        (self.work / "program.json").write_text("{}", encoding="utf-8")
        self.magics._header_key = Mock(return_value="dependencies-a")
        self.magics._run_lean = Mock(side_effect=self.compile_header)

    def compile_header(self, path, extra_args=()):
        if "-o" in extra_args:
            Path(extra_args[extra_args.index("-o") + 1]).write_bytes(b"compiled-header")
        return 0, "", 0.0

    def test_verified_header_is_reused(self):
        self.assertEqual(self.magics._rebuild_header(report=False), "compiled")
        self.assertEqual(self.magics._rebuild_header(report=False), "cached")
        self.magics._run_lean.assert_called_once()

    def test_live_lean_cell_rechecks_dependencies_even_when_header_was_ok(self):
        self.magics._rebuild_header(report=False)
        self.assertTrue(self.magics._header_ok)
        self.magics._header_key.return_value = "dependencies-b"
        self.magics.lean("live", "#guard true")
        self.assertEqual(self.magics._run_lean.call_count, 3)
        self.assertTrue(notebook_cache.cached_header(
            self.metadata, "dependencies-b", self.artifact,
        ))

    def test_failed_compilation_removes_previous_cache_admission(self):
        self.magics._rebuild_header(report=False)
        self.magics._header_key.return_value = "dependencies-b"
        self.magics._run_lean.side_effect = None
        self.magics._run_lean.return_value = (1, "compilation failed", 0.0)
        self.assertEqual(self.magics._rebuild_header(report=False), "failed")
        self.assertFalse(self.metadata.exists())
        self.assertFalse(self.magics._header_ok)

    def test_dependency_change_during_compilation_never_publishes_metadata(self):
        self.magics._header_key.side_effect = ["dependencies-a", "dependencies-b"]
        self.assertEqual(self.magics._rebuild_header(report=False), "failed")
        self.assertFalse(self.metadata.exists())
        self.assertFalse(self.magics._header_ok)

    def test_unverifiable_imports_use_direct_envelope_loading(self):
        self.magics._rebuild_header(report=False)
        self.magics._header_key.return_value = None
        self.magics._run_lean.reset_mock()
        self.magics.lean("direct", "#guard true")
        self.magics._run_lean.assert_called_once()
        self.assertFalse(self.metadata.exists())
        self.assertFalse(self.magics._header_ok)
        source = (self.work / "cells" / "direct.lean").read_text(encoding="utf-8")
        self.assertIn("import LeanModels", source)
        self.assertIn('load_program program from "work/program.json"', source)
        self.assertNotIn("import NotebookHeader", source)

    def test_empty_envelope_set_does_not_admit_a_header(self):
        self.magics._header_ok = True
        (self.work / "program.json").unlink()
        self.assertEqual(self.magics._rebuild_header(report=False), "empty")
        self.assertFalse(self.magics._header_ok)
        self.magics._header_key.assert_not_called()


if __name__ == "__main__":
    unittest.main()
