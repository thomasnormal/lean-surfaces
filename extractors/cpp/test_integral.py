#!/usr/bin/env python3
"""C++23 integral value operations against compiled Clang execution.

This tests the value kernel, not AST admission or whole-program execution.
The oracle's static assertions check the widths and promotions used by its
32/64-bit operands; conversions additionally cover 8/16-bit values and bool.
No CI registration occurs here. Missing tools are named skips, not matches.
"""

import itertools
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[2]
FORMATS = ("b", "s8", "u8", "s16", "u16", "s32", "u32", "s64", "u64")
OPERATIONS = ("add", "sub", "mul", "div", "rem", "and", "or", "xor",
              "eq", "ne", "lt", "le", "gt", "ge")


def bounds(format_name):
    if format_name == "b":
        return 0, 1
    width = int(format_name[1:])
    if format_name.startswith("s"):
        return -(1 << (width - 1)), (1 << (width - 1)) - 1
    return 0, (1 << width) - 1


def values(format_name):
    minimum, maximum = bounds(format_name)
    return sorted({value for value in
                   (minimum, minimum + 1, -257, -7, -1, 0, 1, 2, 7, 255,
                    256, maximum // 2, maximum - 1, maximum)
                   if minimum <= value <= maximum})


def is_defined(operation, format_name, left, right):
    minimum, maximum = bounds(format_name)
    if operation in ("div", "rem"):
        return right != 0 and not (format_name.startswith("s") and
                                  left == minimum and right == -1)
    if operation in ("add", "sub", "mul") and format_name.startswith("s"):
        result = {"add": lambda: left + right, "sub": lambda: left - right,
                  "mul": lambda: left * right}[operation]()
        return minimum <= result <= maximum
    return True


def defined_rows():
    rows = []
    for source, destination in itertools.product(FORMATS, repeat=2):
        for value in values(source):
            rows.append(("convert", source, value, destination, 0))
    for format_name in ("s32", "u32", "s64", "u64"):
        for value in values(format_name):
            for operation in ("plus", "neg", "not", "compl"):
                if operation == "neg" and format_name.startswith("s") and value == bounds(format_name)[0]:
                    continue
                rows.append((operation, format_name, value, format_name, 0))
            for count in sorted({0, 1, 7, int(format_name[1:]) - 1}):
                for count_format in ("s32", "u64"):
                    for operation in ("shl", "shr"):
                        rows.append((operation, format_name, value, count_format, count))
        for left, right, operation in itertools.product(values(format_name), values(format_name), OPERATIONS):
            if is_defined(operation, format_name, left, right):
                rows.append((operation, format_name, left, format_name, right))
    rows.extend([("not", "b", 0, "b", 0), ("not", "b", 1, "b", 0)])
    return rows


def serialize(rows):
    return "".join("\t".join(map(str, row)) + "\n" for row in rows)


class IntegralDifferentialTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.compiler = shutil.which(os.environ.get("LEANCPP_CLANG", "clang++"))
        cls.lake = shutil.which("lake")
        if cls.compiler is None or cls.lake is None:
            raise unittest.SkipTest("integral differential requires Clang and Lake")
        cls.directory = tempfile.TemporaryDirectory(prefix="leancpp-integral-")
        cls.addClassCleanup(cls.directory.cleanup)
        cls.root = pathlib.Path(cls.directory.name)
        cls.binaries = {}
        print(subprocess.check_output([cls.compiler, "--version"], text=True).splitlines()[0])
        print("target:", subprocess.check_output([cls.compiler, "-dumpmachine"], text=True).strip())
        cls.checked_run([cls.lake, "build", "LeanModels.Cpp.Integral"])
        for optimization in ("-O0", "-O2"):
            binary = cls.root / optimization[1:]
            cls.checked_run([cls.compiler, "--no-default-config", "-std=c++23", "-pedantic-errors",
                             optimization, "-fsanitize=undefined", "-fno-sanitize-recover=all",
                             "-static-libstdc++", "-static-libgcc",
                             str(ROOT / "extractors/cpp/integral_oracle.cpp"), "-o", str(binary)])
            cls.binaries[optimization] = binary
            cls.checked_run([str(binary)], "plus\ts32\t0\ts32\t0\n")

    @staticmethod
    def checked_run(command, input_text=None):
        result = subprocess.run(command, input=input_text, text=True, capture_output=True,
                                cwd=ROOT, timeout=120)
        if result.returncode != 0:
            raise AssertionError(f"command failed: {command}\n{result.stdout}\n{result.stderr}")
        return result.stdout.splitlines()

    def model(self, rows):
        output = self.checked_run([self.lake, "env", "lean", "--run",
                                  str(ROOT / "extractors/cpp/run_integral.lean")], serialize(rows))
        self.assertEqual(len(output), len(rows), "model dropped or duplicated rows")
        return output

    def test_defined_values_conv_integral_expr_unary_mul_add_shift_bit_compare(self):
        rows = defined_rows()
        model = self.model(rows)
        self.assertTrue(all(result.startswith("ok ") for result in model))
        for optimization, binary in self.binaries.items():
            oracle = self.checked_run([str(binary)], serialize(rows))
            self.assertEqual(len(oracle), len(rows), "oracle dropped or duplicated rows")
            mismatches = [(row, actual, expected) for row, actual, expected in zip(rows, model, oracle)
                          if actual != expected]
            self.assertEqual(mismatches, [], f"mismatches at {optimization}")
        print(f"integral defined: {len(rows)} rows, two optimization levels, zero mismatches")

    def test_undefined_expr_pre_mul_shift(self):
        rows = []
        for format_name in ("s32", "s64"):
            minimum, maximum = bounds(format_name)
            rows.extend([
                ("add", format_name, maximum, format_name, 1),
                ("sub", format_name, minimum, format_name, 1),
                ("mul", format_name, maximum, format_name, 2),
                ("neg", format_name, minimum, format_name, 0),
                ("div", format_name, minimum, format_name, -1),
                ("rem", format_name, minimum, format_name, -1),
            ])
        for format_name in ("s32", "u32", "s64", "u64"):
            for operation in ("div", "rem"):
                rows.append((operation, format_name, 1, format_name, 0))
            for operation in ("shl", "shr"):
                rows.append((operation, format_name, 1, "s32", -1))
                rows.append((operation, format_name, 1, "u64", int(format_name[1:])))
        self.assertEqual(self.model(rows), ["ub"] * len(rows))
        failures = []
        for row in rows:
            result = subprocess.run([str(self.binaries["-O0"])], input=serialize([row]),
                                    text=True, capture_output=True, timeout=10)
            if result.returncode == 0 or "runtime error:" not in result.stderr:
                failures.append((row, result.returncode, result.stdout, result.stderr))
        self.assertEqual(failures, [])
        print(f"integral undefined: {len(rows)} rows, separate UBSan witnesses, no value matches claimed")

    def test_invalid_values_and_unresolved_promotions(self):
        rows = [
            ("plus", "s0", 0, "s32", 0),
            ("add", "s32", 0, "s0", 0),
            ("convert", "s32", 0, "u0", 0),
            ("convert", "b", 2, "s32", 0),
            ("add", "s8", 128, "s8", 0),
            ("plus", "b", 1, "b", 0),
            ("add", "s32", -1, "u32", 1),
            ("eq", "s32", -1, "u32", 1),
            ("shl", "b", 1, "s32", 1),
        ]
        self.assertEqual(self.model(rows), ["invalid"] * 5 + ["unsupported"] * 4)


if __name__ == "__main__":
    unittest.main()
