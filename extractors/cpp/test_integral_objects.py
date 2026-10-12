#!/usr/bin/env python3
"""Defined integral-object traces, not AST or whole-program admission."""

import itertools
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

from test_integral import FORMATS, serialize, values


ROOT = pathlib.Path(__file__).resolve().parents[2]


class IntegralObjectDifferentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.compiler = shutil.which(os.environ.get("LEANCPP_CLANG", "clang++"))
        cls.lake = shutil.which("lake")
        if cls.compiler is None or cls.lake is None:
            raise unittest.SkipTest("integral object differential requires Clang and Lake")
        cls.directory = tempfile.TemporaryDirectory(prefix="leancpp-integral-objects-")
        cls.addClassCleanup(cls.directory.cleanup)
        cls.root = pathlib.Path(cls.directory.name)
        print(subprocess.check_output([cls.compiler, "--version"], text=True).splitlines()[0])
        print("target:", subprocess.check_output([cls.compiler, "-dumpmachine"], text=True).strip())
        cls.checked_run([cls.lake, "build", "LeanModels.Cpp.IntegralObjects"])
        cls.checked_run([cls.lake, "build", "LeanModels.Cpp.IntegralObjectStatements"])
        cls.binaries = {}
        for optimization in ("-O0", "-O2"):
            binary = cls.root / optimization[1:]
            cls.checked_run([
                cls.compiler, "--no-default-config", "-std=c++23", "-pedantic-errors",
                optimization, "-fsanitize=undefined", "-fno-sanitize-recover=all",
                "-static-libstdc++", "-static-libgcc",
                str(ROOT / "extractors/cpp/integral_object_oracle.cpp"), "-o", str(binary),
            ])
            cls.binaries[optimization] = binary

        cls.statement_binaries = {}
        statement_oracle = ROOT / "extractors/cpp/integral_object_statement_oracle.cpp"
        for optimization in ("-O0", "-O2"):
            binary = cls.root / f"statements{optimization[1:]}"
            cls.checked_run([
                cls.compiler, "--no-default-config", "-std=c++23", "-pedantic-errors",
                optimization, "-fsanitize=undefined", "-fno-sanitize-recover=all",
                "-static-libstdc++", "-static-libgcc", str(statement_oracle), "-o", str(binary),
            ])
            cls.statement_binaries[optimization] = binary

    @staticmethod
    def checked_run(command, input_text=None):
        result = subprocess.run(command, input=input_text, text=True, capture_output=True,
                                cwd=ROOT, timeout=120)
        if result.returncode != 0:
            raise AssertionError(f"command failed: {command}\n{result.stdout}\n{result.stderr}")
        return result.stdout.splitlines()

    def test_defined_object_traces(self):
        rows = [(format_name, initial, replacement) for format_name in FORMATS
                for initial, replacement in itertools.product(values(format_name), repeat=2)]
        input_text = serialize(rows)
        model = self.checked_run([
            self.lake, "env", "lean", "--run",
            str(ROOT / "extractors/cpp/run_integral_objects.lean"),
        ], input_text)
        self.assertEqual(len(model), len(rows))
        for optimization, binary in self.binaries.items():
            with self.subTest(optimization=optimization):
                oracle = self.checked_run([str(binary)], input_text)
                self.assertEqual(len(oracle), len(rows))
                self.assertEqual(model, oracle)
        print(f"integral object differential: {len(rows)} traces at -O0/-O2")

    def test_converted_object_traces(self):
        formats = ("b", "s16", "u16", "s32", "u32")
        rows = [(destination, source, initial, replacement)
                for destination in formats
                for source in formats
                for initial, replacement in itertools.product(values(source), repeat=2)]
        input_text = "".join("\t".join(map(str, row)) + "\n" for row in rows)
        model = self.checked_run([
            self.lake, "env", "lean", "--run",
            str(ROOT / "extractors/cpp/run_integral_object_conversions.lean"),
        ], input_text)
        oracle_source = ROOT / "extractors/cpp/integral_object_conversion_oracle.cpp"
        binaries = {}
        for optimization in ("-O0", "-O2"):
            binary = self.root / f"convert{optimization[1:]}"
            self.checked_run([
                self.compiler, "--no-default-config", "-std=c++23", "-pedantic-errors",
                optimization, "-fsanitize=undefined", "-fno-sanitize-recover=all",
                "-static-libstdc++", "-static-libgcc", str(oracle_source), "-o", str(binary),
            ])
            binaries[optimization] = binary
        self.assertEqual(len(model), len(rows))
        for optimization, binary in binaries.items():
            with self.subTest(optimization=optimization):
                self.assertEqual(model, self.checked_run([str(binary)], input_text))
        print(f"integral object conversion differential: {len(rows)} traces at -O0/-O2")

    def test_statement_traces(self):
        rows = [(mode, initial, delta)
                for mode in ("add", "branch", "loop", "for", "sequence")
                for initial in range(17)
                for delta in range(-8, 9)]
        input_text = "".join("\t".join(map(str, row)) + "\n" for row in rows)
        model = self.checked_run([
            self.lake, "env", "lean", "--run",
            str(ROOT / "extractors/cpp/run_integral_object_statements.lean"),
        ], input_text)
        self.assertEqual(len(model), len(rows))
        for optimization, binary in self.statement_binaries.items():
            with self.subTest(optimization=optimization):
                self.assertEqual(model, self.checked_run([str(binary)], input_text))
        print(f"integral object statement differential: {len(rows)} traces at -O0/-O2")


if __name__ == "__main__":
    unittest.main()
