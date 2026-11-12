#!/usr/bin/env python3
"""Rank the observed PY-REAL walls and expose their measured price.

The library survey records one first refusal for each manifest module.  This
small instrument turns those rows into a stable ranking.  ``sole`` is counted
only when the census wall set contains the observed wall and no other wall;
unpredicted messages remain visible with a zero sole count instead of being
silently folded into a named tier.  The price is the measured surface exposed
by the rows (modules, public functions, and driven calls), not a promise that
all of it will flip.

No source is parsed here: the input is the structured JSON produced by
``library_survey.py``.
"""

import argparse
import json
import sys


def wall_name(row):
    observed = row.get("observed_wall") or ""
    if observed == "class-creation" or observed == "import":
        return observed
    if observed == "node:ImportFrom:accelerator-unmeasured":
        return "accelerator-unmeasured"
    if observed == "node:ImportFrom:accelerator-outside-domain":
        return "accelerator-outside-domain"
    if observed.startswith("msg:a function body reaches a module definition"):
        return "definition-order"
    if observed.startswith("msg:binary '+' on a heap object"):
        return "heap-plus"
    if observed.startswith("msg:try/except uses unsupported features"):
        return "try-except"
    if observed.startswith("msg:builtin 'frozenset'"):
        return "frozenset"
    if observed.startswith("node:"):
        return observed
    if observed.startswith("msg:"):
        return observed[4:].split(" (")[0][:80]
    return observed


def canonical_census(wall):
    if wall in ("accelerator-unmeasured", "accelerator-outside-domain"):
        return "import"
    return wall


def rank(rows):
    buckets = {}
    for row in rows:
        wall = wall_name(row)
        if not wall:
            continue
        item = buckets.setdefault(wall, {
            "wall": wall,
            "present": 0,
            "sole": 0,
            "modules": [],
            "public_functions": 0,
            "driven_calls": 0,
            "matched_calls": 0,
            "all_calls_match_rows": 0,
            "potential_verified_rows": 0,
            "verdicts": {},
        })
        item["present"] += 1
        module = row.get("module") or row.get("file") or "?"
        item["modules"].append(module)
        item["public_functions"] += int(row.get("nfunctions") or 0)
        item["driven_calls"] += int(row.get("ncalls") or 0)
        item["matched_calls"] += int(row.get("nmatched") or 0)
        verdict = row.get("verdict") or "BODY-REFUSED"
        item["verdicts"][verdict] = item["verdicts"].get(verdict, 0) + 1
        if row.get("ncalls") and row.get("nmatched") == row.get("ncalls"):
            item["all_calls_match_rows"] += 1
            if verdict == "REFUSED":
                item["potential_verified_rows"] += 1
        census = {canonical_census(w) for w in (row.get("census_walls") or [])}
        if census == {canonical_census(wall)}:
            item["sole"] += 1
    for item in buckets.values():
        item["modules"] = sorted(set(item["modules"]))
        item["module_count"] = len(item["modules"])
        del item["modules"]
    return sorted(buckets.values(), key=lambda x: (-x["sole"], -x["present"], x["wall"]))


def load_rows(paths, provenance=None):
    rows = []
    seen = set()
    for path in paths:
        with open(path, encoding="utf-8") as stream:
            data = json.load(stream)
        for row in data.get("rows", []):
            if provenance is not None and row.get("provenance") != provenance:
                continue
            key = (row.get("provenance"), row.get("file"), row.get("module"))
            if key in seen:
                raise ValueError("duplicate survey row: %s" % (key,))
            seen.add(key)
            rows.append(row)
    return rows


def self_test():
    rows = [
        {"module": "a", "observed_wall": "import", "census_walls": ["import"],
         "nfunctions": 2, "ncalls": 4, "nmatched": 4, "verdict": "REFUSED"},
        {"module": "b", "observed_wall": "import", "census_walls": ["import", "class-creation"],
         "nfunctions": 3, "ncalls": 5},
        {"module": "c", "observed_wall": "class-creation", "census_walls": ["class-creation"],
         "nfunctions": 1, "ncalls": 2},
        {"module": "d", "observed_wall": "msg:builtin 'frozenset' exists", "census_walls": [],
         "nfunctions": 4, "ncalls": 0},
    ]
    got = rank(rows)
    assert [x["wall"] for x in got] == ["import", "class-creation", "frozenset"]
    assert got[0]["sole"] == 1 and got[0]["present"] == 2
    assert got[1]["sole"] == 1 and got[1]["driven_calls"] == 2
    assert got[2]["sole"] == 0
    print("library_rank self-test: 3 walls, 0 failures")


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--json", dest="json_out")
    parser.add_argument("--provenance", default=None,
                        help="include only rows with this provenance (for example census:library)")
    parser.add_argument("inputs", nargs="*")
    opts = parser.parse_args(argv)
    if opts.self_test:
        self_test()
        return 0
    if not opts.inputs:
        parser.error("provide one or more library_survey JSON files")
    try:
        rows = load_rows(opts.inputs, opts.provenance)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print("library_rank: %s" % exc, file=sys.stderr)
        return 2
    result = {"rows": len(rows), "ranking": rank(rows)}
    if opts.json_out:
        with open(opts.json_out, "w", encoding="utf-8") as stream:
            json.dump(result, stream, indent=2, sort_keys=True)
            stream.write("\n")
    print("wall ranking: %d survey rows" % len(rows))
    for item in result["ranking"]:
        print("  %-28s sole=%3d present=%3d modules=%3d functions=%4d calls=%5d matched=%5d potential_verified=%3d" % (
            item["wall"], item["sole"], item["present"], item["module_count"],
            item["public_functions"], item["driven_calls"], item["matched_calls"],
            item["potential_verified_rows"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
