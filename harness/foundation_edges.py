#!/usr/bin/env python3
"""Generate and exercise the protocol foundation edge pool.

The foundation battery is generated from shared edge pools rather than from
one hand-picked row per finding.  ``--check`` proves the checked-in manifest
is current; ``--diff`` runs that generated manifest through both interpreters.
"""

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "harness" / "foundation_edges.json"
SOURCE = "harness/foundation_probe.py"

NAN_POOL = [
    {"t": "float", "bits": "9221120237041090560"},
]
HUGE_POOL = [2**63, -(2**63) - 1]
BOUNDARY_POOL = [2**63 - 1, -2**63]


def row(function, args, expect="match", note="generated edge-pool row", file=SOURCE):
    return {"file": file, "function": function, "args": args,
            "expect": expect, "note": note}


def generated_rows():
    rows = []
    for function in (
        "nan_contains", "nan_list_equal", "nan_tuple_order", "nan_sorted",
        "nan_max", "nan_dict_key",
    ):
        rows.append(row(function, [[value] for value in NAN_POOL], "unsupported",
                          "RichCompareBool edge pool: non-finite float identity is loud."))
    rows.append(row("int_pow_negative", [[base, 1] for base in (23, 2**53 + 1)],
                    "unsupported", "platform pow edge pool: non-unit integer bases are loud."))
    rows.append(row("int_pow_negative", [[base, exponent]
                                          for base, exponent in ((2, 1), (-2, 3))],
                    "match", "exact binary-base control pool."))
    for function in ("list_insert_huge", "list_pop_huge", "list_pop_empty_huge",
                     "list_subscript_huge", "tuple_subscript_huge",
                     "string_subscript_huge", "bytes_subscript_huge",
                     "range_subscript_huge"):
        rows.append(row(function, [[index] for index in HUGE_POOL],
                        "match", "raising Py_ssize_t edge pool."))
    for function in ("list_insert_boundary", "list_pop_boundary"):
        rows.append(row(function, [[index] for index in BOUNDARY_POOL],
                        "match", "signed Py_ssize_t endpoint pool."))
    for function in ("list_subscript_huge", "tuple_subscript_huge",
                     "string_subscript_huge", "bytes_subscript_huge",
                     "range_subscript_huge", "list_slice_huge",
                     "string_slice_huge"):
        rows.append(row(function, [[index] for index in BOUNDARY_POOL],
                        "match", "signed Py_ssize_t endpoint pool."))
    rows.extend([
        row("range_len_huge", [[]], "match", "range length conversion control."),
        row("bisect_fallback_negative_hi", [[]], "match", "pure fallback control."),
        row("depth_compare", [[100], [1000]], "match", "recursion-limit edge pool.",
            "harness/recursion_limit_probe.py"),
        row("deep_linear", [[100], [1000], [1100]], "match",
            "linear recursion-limit edge pool."),
    ])
    return rows


def manifest_text():
    return json.dumps(generated_rows(), indent=2, sort_keys=True) + "\n"


def check_manifest():
    actual = OUT.read_text(encoding="utf-8")
    expected = manifest_text()
    if actual != expected:
        sys.stderr.write("foundation_edges: manifest is stale; run --write\n")
        return 1
    print("foundation_edges: %d generated rows are current" % len(generated_rows()))
    return 0


def run_diff(proof=False):
    command = [sys.executable, str(ROOT / "harness" / "diff_test.py"),
               "--cases", str(OUT), "--no-build", "--runner",
               str(ROOT / ".lake" / "build" / "bin" / "leanmodels-run")]
    if proof:
        command.append("--proof-interpreter")
    return subprocess.call(command, cwd=str(ROOT))


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--diff", action="store_true")
    options = parser.parse_args(argv)
    if options.write:
        OUT.write_text(manifest_text(), encoding="utf-8")
    if options.check or not (options.write or options.diff):
        if check_manifest():
            return 1
    if options.diff:
        return max(run_diff(False), run_diff(True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
