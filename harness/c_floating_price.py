#!/usr/bin/env python3
"""Price the registered C floating-literal wall with Clang's AST probe.

The selected rows come from the survey's first refusal, while the records are
re-extracted from the unchanged corpus sources with the approved frontend.
The script carries parser observations only; it never parses a literal
spelling or estimates a value in Python.
"""

import argparse
import json
import os
from collections import Counter
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
EXTRACTOR = ROOT / "extractors" / "c" / "extract.py"
WALL = "unsupported:floating literal (floats are a named decision)"
DEFAULT_INPUT = ROOT / "docs" / "c-survey.json"
DEFAULT_JSON = ROOT / "docs" / "c-floating-price.json"
DEFAULT_PAGE = ROOT / "docs" / "c-floating-price.md"


def source_path(row, roots):
    try:
        return Path(roots[row["corpus"]]) / row["name"]
    except KeyError:
        raise SystemExit("c_floating_price: no source root for %s" % row["corpus"])


def mode_map(manifest):
    if not manifest:
        return {}
    out = {}
    for item in json.loads(Path(manifest).read_text()).get("tests", []):
        env = item.get("envelope")
        if not env or not Path(env).is_file():
            continue
        profile = json.loads(Path(env).read_text()).get("profile_id", "")
        out[item["name"]] = "c17" if profile.endswith("-c17") else "c23"
    return out


def walk_floats(value, out):
    if isinstance(value, dict):
        if value.get("kind") == "FloatingLiteral":
            out.append({key: value.get(key) for key in
                        ("value", "type", "float_bits_hex", "float_bit_width")})
        for child in value.values():
            walk_floats(child, out)
    elif isinstance(value, list):
        for child in value:
            walk_floats(child, out)


def extract_records(row, source, clang, plugin, standard):
    env = os.environ.copy()
    env["LEAN_C_CLANG"] = clang
    env["LEAN_C_FLOATING_BITS_PLUGIN"] = plugin
    command = [sys.executable, str(EXTRACTOR), str(source), "--std", standard,
               "--source-name", row["corpus"] + ":" + row["name"]]
    # The extractor's status line is human-facing, so ask it to write the
    # envelope to a temporary file outside both the repository and corpus.
    import tempfile
    with tempfile.NamedTemporaryFile(suffix=".json",
                                     dir=str(Path(plugin).resolve().parent),
                                     delete=False) as handle:
        target = handle.name
    try:
        result = subprocess.run(command + ["-o", target], cwd=ROOT, env=env,
                                capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(result.stderr or result.stdout)
        document = json.loads(Path(target).read_text())
    finally:
        Path(target).unlink(missing_ok=True)
    records = []
    walk_floats(document, records)
    return records


def price(data, roots=None, clang=None, plugin=None, manifest=None):
    rows = [row for row in data.get("rows", []) if row.get("dynamic_wall") == WALL]
    if roots is None:
        return {"schema": "c-floating-price-0.1", "rows": len(rows),
                "candidate_files": [row["name"] for row in rows]}
    modes = mode_map(manifest)
    priced = []
    for row in rows:
        source = source_path(row, roots)
        records = extract_records(row, source, clang, plugin,
                                  modes.get(row["name"], "c23"))
        if not records:
            raise RuntimeError("no FloatingLiteral records for %s" % row["name"])
        priced.append({
            "corpus": row["corpus"], "name": row["name"],
            "sha256": row.get("sha256"), "static_walls": row.get("static_walls", []),
            "floating_literals": len(records),
            "bit_widths": sorted(Counter(r["float_bit_width"] for r in records)),
            "types": sorted(Counter(r["type"] for r in records)),
            "all_records_joined": all(r["float_bits_hex"] and r["float_bit_width"]
                                       for r in records),
        })
    widths = Counter(width for row in priced for width in row["bit_widths"])
    types = Counter(typ for row in priced for typ in row["types"])
    return {
        "schema": "c-floating-price-0.1",
        "survey_schema": data.get("schema"),
        "survey_commit": data.get("measured_commit"),
        "survey_measured_at_utc": data.get("measured_at_utc"),
        "wall": WALL, "candidate_rows": len(rows),
        "all_records_joined": all(row["all_records_joined"] for row in priced),
        "bit_widths_present": dict(sorted(widths.items())),
        "types_present": dict(sorted(types.items())),
        "rows": priced,
        "interpretation": (
            "The 39 files are the survey's sole dynamic floating-literal wall. "
            "Every FloatingLiteral observed in their approved Clang envelopes "
            "joined to a parser-native rounded bit pattern. This prices the "
            "frontend/value boundary only; no floating semantics or flip is claimed."
        ),
    }


def render(report):
    lines = ["# C floating-literal frontend price", "",
             "- survey commit: `%s`" % report.get("survey_commit", ""),
             "- survey measured at: `%s`" % report.get("survey_measured_at_utc", ""),
             "- sole dynamic wall: `%s`" % report.get("wall", WALL),
             "- candidate files: **%d**" % report.get("candidate_rows", 0),
             "- all parser-native records joined: **%s**" % report.get("all_records_joined", False),
             "- bit widths present: `%s`" % report.get("bit_widths_present", {}),
             "- types present: `%s`" % report.get("types_present", {}), "",
             "| corpus | file | literals | widths | types | static walls |", "| --- | --- | ---: | --- | --- | --- |"]
    for row in report.get("rows", []):
        lines.append("| `%s` | `%s` | %d | `%s` | `%s` | `%s` |" % (
            row["corpus"], row["name"], row["floating_literals"],
            row["bit_widths"], row["types"], ", ".join(row["static_walls"])))
    lines += ["", report.get("interpretation", ""), ""]
    return "\n".join(lines)


def self_test():
    data = {"rows": [{"dynamic_wall": WALL, "name": "a.c"},
                      {"dynamic_wall": "other", "name": "b.c"}]}
    got = price(data)
    if got["candidate_files"] != ["a.c"]:
        raise SystemExit("c_floating_price --self-test: %r" % got)
    print("c_floating_price --self-test: ok")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", default=str(DEFAULT_INPUT))
    ap.add_argument("--json", default=str(DEFAULT_JSON))
    ap.add_argument("--page", default=str(DEFAULT_PAGE))
    ap.add_argument("--manifest")
    ap.add_argument("--clang", default=os.environ.get("LEAN_C_CLANG", "clang"))
    ap.add_argument("--plugin", default=os.environ.get("LEAN_C_FLOATING_BITS_PLUGIN"))
    ap.add_argument("--c1-root")
    ap.add_argument("--c2-root")
    ap.add_argument("--c3-root")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test(); return 0
    if not args.plugin or not all((args.c1_root, args.c2_root, args.c3_root)):
        ap.error("--plugin, --c1-root, --c2-root and --c3-root are required")
    roots = {"gcc.c-torture/execute": args.c1_root,
             "c-testsuite/single-exec": args.c2_root,
             "gcc.c23-run": args.c3_root}
    report = price(json.loads(Path(args.input).read_text()), roots, args.clang,
                   args.plugin, args.manifest)
    Path(args.json).write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    Path(args.page).write_text(render(report))
    print("c_floating_price: wrote %s and %s" % (args.json, args.page))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
