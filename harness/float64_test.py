#!/usr/bin/env python3
"""Check pure binary64 rounding and decimal rendering against the pinned oracle."""

import argparse
import json
import math
import os
import operator
from pathlib import Path
import random
import shutil
import struct
import subprocess
import sys
import tempfile
import unicodedata


ROOT = Path(__file__).resolve().parent.parent


def pin_oracle():
    if os.environ.get("LEANPY_NO_REEXEC"):
        return
    requested = os.environ.get("LEANPY_CPYTHON", "python3.9")
    executable = shutil.which(requested)
    if executable is None:
        raise RuntimeError("pinned oracle is unavailable: " + requested)
    if os.path.realpath(executable) != os.path.realpath(sys.executable):
        os.environ["LEANPY_NO_REEXEC"] = "1"
        os.execv(executable, [executable, str(Path(__file__).resolve())] + sys.argv[1:])


def bits_of(value):
    return struct.unpack(">Q", struct.pack(">d", value))[0]


def oracle_output(value):
    return {"bits": str(bits_of(value)), "repr": repr(value)}


def arithmetic_output(operation):
    try:
        return oracle_output(operation())
    except (ZeroDivisionError, OverflowError) as error:
        return {"error": type(error).__name__, "message": str(error)}

def binary_arithmetic_output(operation):
    try:
        result = operation()
        if math.isnan(result):
            return {"refused": "nan-payload"}
        return oracle_output(result)
    except OverflowError as error:
        return {"error": type(error).__name__, "message": str(error)}


def comparison_output(left, right):
    return {"equal": left == right, "less": left < right, "greater": left > right}


def constructor_rows(generator, samples):
    zeroes = [code for code in range(0x110000)
              if unicodedata.decimal(chr(code), None) == 0]
    records = [{"kind": "decimal_zeroes"}]
    expected = [zeroes]
    texts = [
        "", " ", ".", "+", "-", "0", "-0", "+0.0", ".1", "1.",
        "1.e2", "1_2.3_4e+5_6", "1._0", "._1", "_1", "1_", "1__2",
        "1e", "1e+", "1e_2", "1e2_", "1e1.0", "1 2", "1\x002",
        "0x1p0", "Infinity", "+INF", "-inFiniTy", "nan", "-NaN", "+nAn",
        "in_f", "na_n", "NaN(1)", "\x1c1\x1c", "\x851\x85", "\u3000-1\u3000",
        "٠.١", "１２.３４e٥", "²", "\t\n\r\v\f 1 \t\n\r\v\f",
        "1e999999999999999999999999", "-0e999999999999999999999999",
        "-1e-999999999999999999999999", "1.7976931348623157e308",
        "1.7976931348623158e308", "1.7976931348623159e308",
        "2.4703282292062327e-324", "2.4703282292062328e-324",
        "4.9406564584124654e-324", "1" + "0" * 1000 + "e-1000",
        "0." + "0" * 1000 + "1e1001", "0" * 1000 + ".1",
        "1.00000000000000011102230246251565404236316680908203125",
        "1.00000000000000033306690738754696212708950042724609375",
    ]
    for zero in zeroes:
        texts.extend(chr(zero + digit) + "." + chr(zero + 9 - digit)
                     for digit in range(10))
        texts.append(chr(zero + 1) + "_" + chr(zero + 2) + "e" + chr(zero + 3))
    whitespace = [code for code in range(0x110000) if chr(code).isspace()]
    for code in whitespace:
        texts.append(chr(code) + "-1.5" + chr(code))
    for _ in range(samples):
        coefficient = str(generator.randrange(10 ** generator.randrange(1, 100)))
        position = generator.randrange(len(coefficient) + 1)
        text = coefficient[:position] + "." + coefficient[position:]
        if generator.randrange(2):
            text = "-" + text
        texts.append(text + "e" + str(generator.randrange(-500, 501)))
        texts.append("".join(generator.choice("0123456789eE+-. _")
                             for _ in range(generator.randrange(1, 30))))
    for text in texts:
        records.append({"kind": "text", "text": text})
        try:
            value = float(text)
            expected.append({"refused": "nan-payload"} if math.isnan(value)
                            else oracle_output(value))
        except ValueError:
            expected.append({"invalid": True})
    for code in whitespace:
        records.append({"kind": "decimal_character", "code": str(code)})
        expected.append({"normalized": 32 if code >= 128 else code})
    return records, expected


def rows(samples):
    generator = random.Random(30953)
    records = []
    expected = []
    operators = (("add", operator.add), ("sub", operator.sub), ("mult", operator.mul))
    bit_patterns = {0, 1, 2, (1 << 52) - 1, 1 << 52, (1 << 52) + 1,
                    0x3FB999999999999A, 0x3FEFFFFFFFFFFFFF,
                    0x3FF0000000000000, 0x3FF0000000000001,
                    0x7FEFFFFFFFFFFFFF, 0x7FF0000000000000,
                    0x7FF0000000000001, 0x7FF8000000000000}
    for exponent in range(2047):
        for fraction in (0, 1, (1 << 52) - 1):
            bit_patterns.add((exponent << 52) | fraction)
    bit_patterns |= {word | (1 << 63) for word in tuple(bit_patterns)}
    bit_patterns |= {generator.getrandbits(64) for _ in range(samples)}
    for word in sorted(bit_patterns):
        value = struct.unpack(">d", struct.pack(">Q", word))[0]
        records.append({"kind": "repr", "bits": str(word)})
        expected.append({"bits": str(word), "repr": repr(value)})
        records.append({"kind": "neg", "bits": str(word)})
        expected.append(oracle_output(-value))
        records.append({"kind": "integer_conversion", "bits": str(word)})
        if math.isfinite(value):
            expected.append({"integer": str(int(value)),
                             "integral": str(int(value)) if value.is_integer() else None})
        else:
            expected.append({"integer": None, "integral": None})
        for integer in (0, 9007199254740993, -10 ** 400):
            records.append({"kind": "int_compare", "left": str(word), "right": str(integer)})
            expected.append(comparison_output(value, integer))
        right_word = generator.getrandbits(64)
        right = struct.unpack(">d", struct.pack(">Q", right_word))[0]
        records.append({"kind": "float_compare", "left": str(word), "right": str(right_word)})
        expected.append(comparison_output(value, right))
        for name, operation in operators:
            records.append({"kind": "float_arithmetic", "operator": name,
                            "left": str(word), "right": str(right_word)})
            expected.append(binary_arithmetic_output(lambda: operation(value, right)))

    special_arithmetic = [
        (0.1, 0.2), (0.0, -0.0), (-0.0, -0.0), (-1.0, -1.0),
        (1.0, 2.0 ** -53), (1.0 + 2.0 ** -52, 2.0 ** -53),
        (float.fromhex("0x0.0000000000001p-1022"), 0.5),
        (float.fromhex("0x0.0000000000003p-1022"), 0.5),
        (float.fromhex("0x1.fffffffffffffp1023"), 2.0),
        (math.inf, math.inf), (math.inf, -math.inf), (-math.inf, -math.inf),
        (math.inf, 0.0), (-math.inf, -0.0), (0.0, -math.inf),
        (math.nan, 1.0), (1.0, math.nan),
    ]
    for left, right in special_arithmetic:
        for name, operation in operators:
            records.append({"kind": "float_arithmetic", "operator": name,
                            "left": str(bits_of(left)), "right": str(bits_of(right))})
            expected.append(binary_arithmetic_output(lambda: operation(left, right)))

    integers = [0, 1, -1, 9007199254740993, -9007199254740993,
                10 ** 400, -10 ** 400, 2 ** 1024 - 2 ** 970,
                2 ** 1024 - 2 ** 970 - 1]
    integers.extend(generator.getrandbits(generator.randrange(1501)) * generator.choice((-1, 1))
                    for _ in range(samples))
    for integer in integers:
        records.append({"kind": "conversion", "integer": str(integer)})
        expected.append(arithmetic_output(lambda: float(integer)))

    division_pairs = [(1.0, 10.0), (0.0, -2.0), (-0.0, -2.0), (1.0, 0.0),
                      (1.0, -0.0), (1e300, 1e-300), (1e-300, -1e300),
                      (math.inf, 0.0), (math.nan, -0.0)]
    for _ in range(samples):
        left_word = generator.getrandbits(64)
        right_word = generator.getrandbits(64)
        left = struct.unpack(">d", struct.pack(">Q", left_word))[0]
        right = struct.unpack(">d", struct.pack(">Q", right_word))[0]
        if math.isfinite(left) and math.isfinite(right):
            division_pairs.append((left, right))
    for left, right in division_pairs:
        records.append({"kind": "float_division", "left": str(bits_of(left)),
                        "right": str(bits_of(right))})
        expected.append(arithmetic_output(lambda: left / right))

    mixed_pairs = [(10 ** 400, 0.0), (10 ** 400, 1.0), (0, -2.0), (-5, 2.0),
                   (2 ** 53 + 1, 3.0), (-10 ** 400, -0.0)]
    for integer in integers:
        word = generator.getrandbits(64)
        value = struct.unpack(">d", struct.pack(">Q", word))[0]
        if math.isfinite(value):
            mixed_pairs.append((integer, value))
    for integer, value in mixed_pairs:
        records.append({"kind": "int_float_division", "left": str(integer),
                        "right": str(bits_of(value))})
        expected.append(arithmetic_output(lambda: integer / value))
        records.append({"kind": "float_int_division", "left": str(bits_of(value)),
                        "right": str(integer)})
        expected.append(arithmetic_output(lambda: value / integer))

    mixed_arithmetic = mixed_pairs + [
        (10 ** 400, math.nan), (10 ** 400, math.inf), (-10 ** 400, -math.inf),
        (0, math.inf), (0, math.nan), (2 ** 53 + 1, 1.0),
    ]
    for integer, value in mixed_arithmetic:
        for name, operation in operators:
            records.append({"kind": "int_float_arithmetic", "operator": name,
                            "left": str(integer), "right": str(bits_of(value))})
            expected.append(binary_arithmetic_output(lambda: operation(integer, value)))
            records.append({"kind": "float_int_arithmetic", "operator": name,
                            "left": str(bits_of(value)), "right": str(integer)})
            expected.append(binary_arithmetic_output(lambda: operation(value, integer)))

    fractions = [(1, 10), (5, 2), (0, 2), (1, 2 ** 1075),
                 (3, 2 ** 1075), (10 ** 400, 10 ** 400),
                 ((2 ** 53 - 1) * 2 ** 971, 1),
                 (2 ** 1024 - 2 ** 970, 1), (2 ** 1024, 1)]
    for power in range(-1075, 1025, 11):
        numerator = 2 ** max(power, 0)
        denominator = 2 ** max(-power, 0)
        fractions.extend([(numerator, denominator),
                          (numerator * (2 ** 54 - 1), denominator * 2 ** 54),
                          (numerator * (2 ** 54 + 1), denominator * 2 ** 54)])
    for _ in range(samples):
        fractions.append((generator.getrandbits(generator.randrange(1501)),
                          generator.getrandbits(generator.randrange(1, 1501)) + 1))
    for numerator, denominator in fractions:
        for negative in (False, True):
            records.append({"kind": "ratio", "negative": negative,
                            "numerator": str(numerator), "denominator": str(denominator)})
            signed_denominator = -denominator if negative else denominator
            try:
                value = numerator / signed_denominator
            except OverflowError:
                value = -math.inf if negative else math.inf
            expected.append(oracle_output(value))
            records.append({"kind": "division", "left": str(numerator),
                            "right": str(signed_denominator)})
            try:
                expected.append(oracle_output(numerator / signed_denominator))
            except (ZeroDivisionError, OverflowError) as error:
                expected.append({"error": type(error).__name__, "message": str(error)})
    records.append({"kind": "ratio", "negative": False, "numerator": "1", "denominator": "0"})
    expected.append({"bits": None, "repr": None})
    records.append({"kind": "division", "left": "1", "right": "0"})
    expected.append({"error": "ZeroDivisionError", "message": "division by zero"})
    for left, right in [(-5, 2), (-5, -2), (-1, 2 ** 1075),
                        (-2 ** 1024, 1), (-10 ** 400, 10 ** 400)]:
        records.append({"kind": "division", "left": str(left), "right": str(right)})
        try:
            expected.append(oracle_output(left / right))
        except (ZeroDivisionError, OverflowError) as error:
            expected.append({"error": type(error).__name__, "message": str(error)})
    text_records, text_expected = constructor_rows(generator, samples)
    return records + text_records, expected + text_expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=4096)
    parser.add_argument("--no-build", action="store_true")
    arguments = parser.parse_args()
    if arguments.samples < 0:
        parser.error("--samples must be nonnegative")
    print("float64 oracle:", sys.implementation.name, sys.version.split()[0], sys.executable,
          "Unicode", unicodedata.unidata_version, flush=True)
    if not arguments.no_build:
        subprocess.run(["lake", "build", "LeanModels.Python.Float64Tests"], cwd=ROOT, check=True)
    records, expected = rows(arguments.samples)
    with tempfile.TemporaryDirectory(prefix="float64-check-") as directory:
        source = Path(directory) / "rows.json"
        source.write_text(json.dumps(records), encoding="utf-8")
        completed = subprocess.run(
            ["lake", "env", "lean", "--run", "harness/float64_check.lean", str(source)],
            cwd=ROOT, text=True, capture_output=True, timeout=600,
        )
    if completed.returncode != 0:
        print(completed.stdout, end="")
        print(completed.stderr, end="", file=sys.stderr)
        return 1
    actual = [json.loads(line) for line in completed.stdout.splitlines()]
    if len(actual) != len(expected):
        print("wrong result count:", len(actual), "expected", len(expected))
        return 1
    failures = 0
    for index, (oracle, model) in enumerate(zip(expected, actual)):
        if oracle != model:
            failures += 1
            if failures <= 10:
                print("MISMATCH", records[index], "oracle", oracle, "model", model)
    refusals = sum("refused" in result for result in actual)
    print("float64: %d rows, %d failed, %d explicit NaN-payload refusals" %
          (len(records), failures, refusals))
    return 1 if failures else 0


if __name__ == "__main__":
    pin_oracle()
    raise SystemExit(main())
