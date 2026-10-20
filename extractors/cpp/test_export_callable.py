#!/usr/bin/env python3
"""Whole-probe export and literal compilation controls; no CI registration."""
import copy
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]


class CallableExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if os.environ.get("LEANCPP_TEST_LEAN") != "1":
            raise unittest.SkipTest("set LEANCPP_TEST_LEAN=1")
        requested, library = os.environ.get("LEANCPP_CLANG"), os.environ.get("LEANCPP_PROBE_LIBRARY")
        if not requested or not library:
            raise unittest.SkipTest("set matching LEANCPP_CLANG and LEANCPP_PROBE_LIBRARY")
        cls.clang, cls.lake = shutil.which(requested), shutil.which("lake")
        cls.library = pathlib.Path(library).resolve()
        if cls.clang is None or cls.lake is None or not cls.library.is_file():
            raise RuntimeError("selected tools must exist")

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cpp-callable-export-")
        self.addCleanup(temporary.cleanup)
        self.work = pathlib.Path(temporary.name)
        source = self.work / "input.cpp"
        source.write_text('''struct Example {
  static int plus(int value) { return value + 1; }
  int instance(int value) { return value; }
};
int unrelated(int value) { return value * 2; }
''', encoding="utf-8")
        result = subprocess.run([self.clang, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", str(source), "-Xclang", "-load", "-Xclang", str(self.library),
            "-Xclang", "-plugin", "-Xclang", "leancpp-canonical-probe"],
            cwd=self.work, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.probe = json.loads(result.stdout)
        self.paths = {}
        pending = [(self.probe["ast"], [])]
        while pending:
            node, path = pending.pop()
            if node.get("kind") == "CXXMethodDecl" and node.get("name") in {"plus", "instance"}:
                self.paths[node["name"]] = path
            pending.extend((child, path + [index]) for index, child in enumerate(node.get("inner", [])))

    def export(self, contents=None, path=None, namespace="CppExportFixture"):
        probe = self.work / "probe.json"
        if contents is not None:
            probe.write_bytes(contents if isinstance(contents, bytes) else contents.encode("utf-8"))
        elif not probe.exists():
            probe.write_text(json.dumps(self.probe), encoding="utf-8")
        return subprocess.run([self.lake, "env", "lean", "-j", "1", "--run",
            "extractors/cpp/export_callable.lean", str(probe),
            ",".join(map(str, path if path is not None else self.paths["plus"])), namespace],
            cwd=ROOT, capture_output=True, text=True, timeout=120)

    def test_exported_literal_has_kernel_reducible_execution(self):
        result = self.export(namespace="CppExportFixture.end")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("DO NOT EDIT", result.stdout)
        output = self.work / "Literal.lean"
        output.write_text(result.stdout + '''
open LeanModels.Cpp CppExportFixture.«end»
example : function.occurrence.name = some "plus" := rfl
example : evaluateCallable 16 .lp64 function [⟨.signed 32, 4⟩] =
    .ok (.ok ⟨.signed 32, 5⟩) := rfl
''', encoding="utf-8")
        checked = subprocess.run([self.lake, "env", "lean", "-j", "1", str(output)],
                                 cwd=ROOT, capture_output=True, text=True, timeout=120)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_unrelated_whole_probe_error_and_selected_admission_errors_emit_no_literal(self):
        derived = copy.deepcopy(self.probe)
        row = next(row for row in derived["metadata"]["expression_evidence"] if row["operator"] == "*")
        row["operator"] = "+"
        controls = [(json.dumps(derived), None, "binary-evidence"),
                    (json.dumps(self.probe), self.paths["instance"], "admission"),
                    (json.dumps(self.probe), [999999], "admission")]
        for contents, path, stage in controls:
            with self.subTest(stage=stage, path=path):
                result = self.export(contents, path)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertEqual(result.stdout, "")
                self.assertIn("export_callable: " + stage + ":", result.stderr)

    def test_pre_read_byte_bound_and_strict_utf8(self):
        probe = self.work / "probe.json"
        with probe.open("wb") as output:
            output.truncate(128 * 1024 * 1024 + 1)
        result = self.export()
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertIn("input-byte-bound", result.stderr)
        result = self.export(b"\xff")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertIn("invalid UTF-8", result.stderr)


if __name__ == "__main__":
    unittest.main()
