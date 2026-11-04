#!/usr/bin/env python3
"""Target-profile type-resolution checks against C++23 Clang expressions."""

import os
import pathlib
import shutil
import subprocess
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]


class TypeResolutionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler_name = os.environ.get("LEANCPP_CLANG", "clang++")
        cls.compiler = shutil.which(compiler_name)
        cls.lake = shutil.which("lake")
        if cls.compiler is None or cls.lake is None:
            raise unittest.SkipTest("type-resolution checks require Clang and Lake")
        version = subprocess.check_output([cls.compiler, "--version"], text=True).splitlines()[0]
        target = subprocess.check_output([cls.compiler, "-dumpmachine"], text=True).strip()
        print(version)
        print("target:", target)

    def checked(self, command):
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_kernel_type_resolution_guards(self):
        self.checked([self.lake, "build", "LeanModels.Cpp.TypeTests"])

    def test_clang_lp64_cpp23_type_rules(self):
        self.checked([
            self.compiler, "--no-default-config", "-std=c++23", "-pedantic-errors",
            "-fsyntax-only", str(ROOT / "extractors/cpp/type_resolution_oracle.cpp"),
        ])
        print("C++23 LP64 promotion and usual-arithmetic static assertions passed")


if __name__ == "__main__":
    unittest.main()
