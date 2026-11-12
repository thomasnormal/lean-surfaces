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

# F7's protocol pools.  Keep them as structured values so the generator can
# cross the same domains in every row without reparsing Python source.
INT_POOL = [
    0, 1, -1, 2**31 - 1, 2**31, 2**31 + 1,
    -(2**31) - 1, 2**63 - 1, 2**63, 2**63 + 1,
    -(2**63) - 1, 2**53 + 1, 2**1024, 2**1100,
]
FLOAT_POOL = [
    {"t": "float", "bits": "9221120237041090560"},  # nan
    {"t": "float", "bits": "9218868437227405312"},  # inf
    {"t": "float", "bits": "18442240474082181120"}, # -inf
    0.0, -0.0,
    {"t": "float", "bits": "1"},                     # min subnormal
    {"t": "float", "bits": "9218868437227405311"},  # max finite
    2**53,
]
STR_POOL = ["", "x", "héllo", "x" * 300]
CONTAINER_POOL = [[], [1], [[1]], ["self-ref-domain"]]
NAN_POOL = FLOAT_POOL[:1]
INFINITY_POOL = FLOAT_POOL[1:3]
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
    for function in ("nan_sorted", "nan_max"):
        rows.append(row(function, [[value] for value in INFINITY_POOL], "match",
                          "F7 infinity pool: ordered numeric infinities remain decided."))
    rows.append(row("int_pow_negative", [[base, 1] for base in (23, 2**53 + 1)],
                    "unsupported", "platform pow edge pool: non-unit integer bases are loud."))
    rows.append(row("int_pow_negative", [[base, exponent]
                                          for base, exponent in ((2, 1), (-2, 3))],
                    "match", "exact binary-base control pool."))
    for function in ("list_insert_huge", "list_pop_huge", "list_pop_empty_huge",
                     "list_subscript_huge", "tuple_subscript_huge",
                     "string_subscript_huge", "bytes_subscript_huge",
                     "range_subscript_huge"):
        rows.append(row(function, [[index] for index in INT_POOL],
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
        row("nested_equal", [[990], [999]], "match",
            "nested RichCompareBool recursion boundary."),
        row("nested_mismatch", [[999]], "match",
            "early container mismatch avoids descending to the recursion limit."),
        row("nested_tuple_order", [[990]], "match",
            "tuple ordering recursion boundary through RichCompareBool equality probes."),
        row("nested_print", [[510]], "match",
            "recursive rendering control below the fixed repr budget."),
        row("nested_print", [[513], [999]], "unsupported",
            "recursive rendering remains loud beyond the fixed repr budget."),
        row("nested_repr", [[510]], "match",
            "repr recursion control below the fixed rendering budget."),
        row("nested_repr", [[513], [999]], "unsupported",
            "repr recursion remains loud beyond the fixed rendering budget."),
        row("nested_str", [[510]], "match",
            "str recursion control below the fixed rendering budget."),
        row("nested_str", [[513], [999]], "unsupported",
            "str recursion remains loud beyond the fixed rendering budget."),
        row("percent_width", [["x"], [3]], "match",
            "percent-format width flag over admitted scalar conversions."),
        row("percent_zero_width", [[3], [-3]], "match",
            "percent-format zero-padding flag over integer conversions."),
        row("percent_left_width", [["x"], [3]], "match",
            "percent-format left-alignment flag over admitted conversions."),
        row("percent_wide", [["x"], [3]], "match",
            "arbitrary decimal width for percent-format scalar conversions."),
        row("percent_wide_left", [[3], [-3]], "match",
            "arbitrary decimal width with left alignment."),
        row("percent_precision", [["abcdef"], ["x"]], "match",
            "string percent-format precision truncation."),
        row("percent_precision_repr", [["abcdef"], [3]], "match",
            "repr percent-format precision truncation."),
        row("percent_numeric_precision", [[3], [-3]], "match",
            "numeric percent-format precision with sign-aware zero padding."),
        row("percent_hex_precision", [[3], [255]], "match",
            "hexadecimal percent-format precision."),
        row("percent_plus", [[3], [-3]], "match",
            "numeric percent-format plus sign flag."),
        row("percent_space", [[3], [-3]], "match",
            "numeric percent-format space sign flag."),
        row("percent_alternate_hex", [[3], [-3]], "match",
            "hexadecimal percent-format alternate form."),
        row("percent_alternate_oct", [[3], [-3]], "match",
            "octal percent-format alternate form."),
        row("percent_plus_width", [[3], [-3]], "match",
            "space-padded percent-format plus flag with width."),
        row("percent_space_width", [[3], [-3]], "match",
            "space-padded percent-format space flag with width."),
        row("percent_alternate_width", [[3], [-3]], "match",
            "space-padded percent-format alternate flag with width."),
        row("percent_plus_alternate_width", [[3], [-3]], "match",
            "space-padded percent-format sign and alternate flags with width."),
        row("percent_space_alternate_width", [[3], [-3]], "match",
            "space-padded percent-format space and alternate flags with width."),
        row("percent_zero_plus_width", [[3], [-3]], "unsupported",
            "zero padding combined with a sign flag remains loud."),
        row("percent_zero_alternate_width", [[3], [-3]], "unsupported",
            "zero padding combined with an alternate flag remains loud."),
        row("percent_dynamic_width", [[5, 3], [-5, 3]], "match",
            "dynamic percent-format width with positive and negative widths."),
        row("percent_dynamic_precision", [[3, "abcdef"], [0, "x"]], "match",
            "dynamic percent-format precision over scalar text."),
        row("float_power_special", [[0.0, 0.0], [-0.0, 2.0], [1.0, 3.5]],
            "match", "portable float-power special-case pool."),
        row("float_power_special", [[-1.0, 0.5]], "unsupported",
            "complex-result float power remains loud."),
        row("float_power_big_zero", [[]], "match",
            "integer-to-double conversion precedes zero exponent."),
        row("mixed_div_left_overflow", [[]], "match",
            "left integer conversion precedes mixed division."),
        row("mixed_div_right_overflow", [[]], "match",
            "right integer conversion precedes mixed division."),
        row("integer_div_huge_ratio", [[]], "match",
            "integer true division retains its exact-ratio path."),
        row("negative_pow_exponent_boundary", [[1023], [1024]], "match",
            "integer exponent conversion boundary."),
        row("negative_pow_exponent_overflow", [[0], [2]], "match",
            "negative-power exponent conversion boundary."),
        row("negative_pow_base_overflow", [[1], [2]], "match",
            "negative-power base conversion boundary."),
        row("float_pow_base_overflow", [[]], "match",
            "mixed float-power base conversion boundary."),
        row("float_pow_exponent_overflow", [[]], "match",
            "mixed float-power exponent conversion boundary."),
    ])
    # The scalar rendering sites share the string pool, including the
    # non-ASCII and long-run boundaries.  `%s` is the admitted raw-string
    # conversion; `%r`/container rendering keep their separate loud rows.
    for function in ("percent_width", "percent_wide", "percent_precision",
                     "percent_dynamic_precision"):
        rows.extend(row(function, [[value] for value in STR_POOL], "match",
                         "F7 string pool: empty, ASCII, non-ASCII, and 300-char run.")
                     for _ in [0])
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


def self_test():
    """Check the generator's declared pools and deterministic cross-product."""
    assert 2**1024 in INT_POOL and 2**1100 in INT_POOL
    assert any(x.get("bits") == "1" for x in FLOAT_POOL if isinstance(x, dict))
    assert "héllo" in STR_POOL and "x" * 300 in STR_POOL
    assert [] in CONTAINER_POOL and [[1]] in CONTAINER_POOL
    rows = generated_rows()
    assert rows == json.loads(json.dumps(rows, sort_keys=True))
    assert len(rows) == len({(r["file"], r["function"], json.dumps(r["args"], sort_keys=True), r["expect"])
                            for r in rows})
    print("foundation_edges: self-test passed (%d rows, %d pools)" %
          (len(rows), 4))
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
    parser.add_argument("--self-test", action="store_true")
    options = parser.parse_args(argv)
    if options.self_test:
        return self_test()
    if options.write:
        OUT.write_text(manifest_text(), encoding="utf-8")
    if options.check or not (options.write or options.diff):
        if check_manifest():
            return 1
    if options.diff:
        if self_test():
            return 1
        return max(run_diff(False), run_diff(True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
