#!/usr/bin/env python3
"""Double-run the parser-native C floating-literal observation probe.

The probe records Clang's already-rounded APFloat bit pattern.  This harness
checks that the observation is deterministic for the same pinned frontend and
that its records retain the source span and width needed to join them to the
C envelope.  It never interprets a C literal spelling.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def run(clang, plugin, source):
    command = [clang, "--no-default-config", "-std=c23", "-fsyntax-only",
               "-Xclang", "-load", "-Xclang", plugin,
               "-Xclang", "-plugin", "-Xclang", "lean-c-floating-bits",
               str(source)]
    result = subprocess.run(command, capture_output=True, text=False)
    if result.returncode:
        raise RuntimeError(result.stderr.decode("utf-8", "replace"))
    try:
        document = json.loads(result.stdout.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise RuntimeError(f"probe output is not one JSON document: {error}")
    if not isinstance(document, list):
        raise RuntimeError("probe output is not a record array")
    for record in document:
        if not isinstance(record, dict) or record.get("kind") != "FloatingLiteral":
            raise RuntimeError(f"invalid FloatingLiteral record: {record!r}")
        if (type(record.get("offset")) is not int or record["offset"] < 0 or
                type(record.get("token_length")) is not int or
                record["token_length"] <= 0 or
                type(record.get("bit_width")) is not int or
                record["bit_width"] <= 0 or
                type(record.get("bits_hex")) is not str or
                not record["bits_hex"] or
                any(char not in "0123456789abcdefABCDEF"
                    for char in record["bits_hex"]) or
                type(record.get("type")) is not str or not record["type"]):
            raise RuntimeError(f"invalid FloatingLiteral record: {record!r}")
    return result.stdout, document


def self_test(clang, plugin):
    fixture = "int main(void) { float x = 1.5f; double y = 2.0; return x == y; }\n"
    with tempfile.NamedTemporaryFile("w", suffix=".c", delete=False) as handle:
        handle.write(fixture)
        source = Path(handle.name)
    try:
        _, records = run(clang, plugin, source)
    finally:
        source.unlink(missing_ok=True)
    if len(records) != 2 or [r["bit_width"] for r in records] != [32, 64]:
        raise RuntimeError(f"self-test expected one binary32 and one binary64 record: {records!r}")
    print("c_floating_bits_determinism: self-test ok")
    return 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path, nargs="?")
    parser.add_argument("--plugin", required=True)
    parser.add_argument("--clang", default=os.environ.get("LEAN_C_CLANG", "clang"))
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    try:
        if args.self_test:
            return self_test(args.clang, args.plugin)
        if args.source is None:
            parser.error("source is required unless --self-test is used")
        first_bytes, first = run(args.clang, args.plugin, args.source)
        second_bytes, second = run(args.clang, args.plugin, args.source)
    except RuntimeError as error:
        print(f"c_floating_bits_determinism: {error}", file=sys.stderr)
        return 1
    if first_bytes != second_bytes or first != second:
        print("c_floating_bits_determinism: two probe runs differ", file=sys.stderr)
        return 1
    print(f"c_floating_bits_determinism: ok ({len(first)} FloatingLiteral records)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
