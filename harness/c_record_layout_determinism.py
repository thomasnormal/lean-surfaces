#!/usr/bin/env python3
"""Double-run the parser-native C record-layout observation probe."""

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
               "-Xclang", "-plugin", "-Xclang", "lean-c-record-layout",
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
        if not isinstance(record, dict) or record.get("kind") not in ("RecordLayout", "TypeLayout"):
            raise RuntimeError(f"invalid layout record: {record!r}")
        if record.get("kind") == "TypeLayout":
            if (type(record.get("offset")) is not int or record["offset"] < 0 or
                    type(record.get("token_length")) is not int or record["token_length"] <= 0 or
                    type(record.get("type")) is not str or not record["type"] or
                    type(record.get("size_bytes")) is not int or record["size_bytes"] < 0 or
                    type(record.get("alignment_bytes")) is not int or record["alignment_bytes"] < 0):
                raise RuntimeError(f"invalid TypeLayout record: {record!r}")
            continue
        if (type(record.get("offset")) is not int or record["offset"] < 0 or
                type(record.get("token_length")) is not int or
                record["token_length"] <= 0 or
                record.get("tag_kind") not in ("struct", "union") or
                type(record.get("size_bytes")) is not int or
                record["size_bytes"] < 0 or
                type(record.get("alignment_bytes")) is not int or
                record["alignment_bytes"] < 0 or
                not isinstance(record.get("fields"), list)):
            raise RuntimeError(f"invalid RecordLayout record: {record!r}")
        for field in record["fields"]:
            if (not isinstance(field, dict) or type(field.get("name")) is not str or
                    type(field.get("offset_bits")) is not int or
                    field["offset_bits"] < 0 or
                    type(field.get("bitfield")) is not bool):
                raise RuntimeError(f"invalid record field: {field!r}")
            if field["bitfield"] and (
                    type(field.get("width_bits")) is not int or
                    field["width_bits"] < 0):
                raise RuntimeError(f"bit-field has no width: {field!r}")
    return result.stdout, document


def self_test(clang, plugin):
    fixture = ("struct S { char c; int i; unsigned b : 3; };\n"
               "union U { int i; char c; };\n"
               "struct F { int n; int tail[]; };\n"
               "int main(void) { struct S s; return (int)sizeof(s); }\n")
    with tempfile.NamedTemporaryFile("w", suffix=".c", delete=False) as handle:
        handle.write(fixture)
        source = Path(handle.name)
    try:
        _, records = run(clang, plugin, source)
    finally:
        source.unlink(missing_ok=True)
    record_layouts = [r for r in records if r["kind"] == "RecordLayout"]
    type_layouts = [r for r in records if r["kind"] == "TypeLayout"]
    if (len(record_layouts) != 3 or record_layouts[0]["tag_kind"] != "struct" or
            record_layouts[1]["tag_kind"] != "union" or record_layouts[2]["tag_kind"] != "struct"):
        raise RuntimeError(f"self-test expected struct and union records: {records!r}")
    if record_layouts[0]["size_bytes"] != 12 or record_layouts[0]["fields"][2].get("width_bits") != 3:
        raise RuntimeError(f"self-test layout values were not parser-native: {records!r}")
    if record_layouts[2]["fields"][1].get("incomplete_array") is not True:
        raise RuntimeError(f"self-test flexible-array marker was not parser-native: {records!r}")
    if len(type_layouts) != 1 or type_layouts[0]["type"] != "struct S":
        raise RuntimeError(f"self-test type layout was not parser-native: {records!r}")
    print("c_record_layout_determinism: self-test ok")
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
        print(f"c_record_layout_determinism: {error}", file=sys.stderr)
        return 1
    if first_bytes != second_bytes or first != second:
        print("c_record_layout_determinism: two probe runs differ", file=sys.stderr)
        return 1
    print(f"c_record_layout_determinism: ok ({len(first)} RecordLayout records)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
