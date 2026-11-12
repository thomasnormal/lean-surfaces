#!/usr/bin/env python3
"""Double-run the parser-native C StringLiteral byte probe.

The probe is deliberately separate from the C envelope until its byte records
are joined by source offset.  This check makes the frontend observation itself
part of the determinism contract: the same source and pinned Clang must emit
the same decoded bytes and metadata twice.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys


def run(clang, plugin, source):
    command = [clang, "--no-default-config", "-std=c23", "-fsyntax-only",
               "-Xclang", "-load", "-Xclang", plugin,
               "-Xclang", "-plugin", "-Xclang", "lean-c-string-bytes",
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
        if (not isinstance(record, dict) or record.get("kind") != "StringLiteral" or
                not isinstance(record.get("offset"), int) or
                not isinstance(record.get("bytes"), list) or
                any(type(byte) is not int or byte < 0 or byte > 255
                    for byte in record["bytes"])):
            raise RuntimeError(f"invalid StringLiteral byte record: {record!r}")
    return result.stdout, document


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--plugin", required=True)
    parser.add_argument("--clang", default=os.environ.get("LEAN_C_CLANG", "clang"))
    args = parser.parse_args()
    try:
        first_bytes, first = run(args.clang, args.plugin, args.source)
        second_bytes, second = run(args.clang, args.plugin, args.source)
    except RuntimeError as error:
        print(f"c_string_bytes_determinism: {error}", file=sys.stderr)
        return 1
    if first_bytes != second_bytes or first != second:
        print("c_string_bytes_determinism: two probe runs differ", file=sys.stderr)
        return 1
    print(f"c_string_bytes_determinism: ok ({len(first)} StringLiteral records)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
