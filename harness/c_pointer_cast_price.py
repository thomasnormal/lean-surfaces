#!/usr/bin/env python3
"""Price parser-native pointer/integer refusal shapes in the C survey."""

import argparse
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_INPUT = ROOT / "docs" / "c-survey.json"
DEFAULT_JSON = ROOT / "docs" / "c-pointer-cast-price.json"
DEFAULT_PAGE = ROOT / "docs" / "c-pointer-cast-price.md"
WALL = "pointer used as an integer"


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def classify(env):
    casts = Counter()
    pointer_types = Counter()
    pointer_arithmetic = []
    for node in walk(env):
        kind = node.get("kind")
        if kind in ("ImplicitCastExpr", "CStyleCastExpr"):
            cast = node.get("cast")
            typ = node.get("type") or ""
            if cast in ("PointerToIntegral", "IntegralToPointer", "BitCast",
                        "BuiltinFnToFnPtr", "FunctionToPointerDecay"):
                casts[cast] += 1
            if "*" in typ:
                pointer_types[typ] += 1
        if kind == "BinaryOperator" and node.get("op") in ("+", "-"):
            typ = node.get("type") or ""
            if "*" in typ:
                pointer_arithmetic.append({"op": node.get("op"), "type": typ})
    if casts.get("PointerToIntegral"):
        primary = "explicit-pointer-to-integer"
    elif casts.get("IntegralToPointer"):
        primary = "explicit-integer-to-pointer"
    elif casts.get("BitCast"):
        primary = "pointer-bit-cast"
    elif pointer_arithmetic:
        primary = "pointer-arithmetic"
    elif pointer_types:
        primary = "implicit-pointer-read-or-use"
    else:
        primary = "no-pointer-node-found"
    return {"primary": primary, "casts": dict(casts),
            "pointer_types": dict(pointer_types),
            "pointer_arithmetic": pointer_arithmetic}


def price(data, manifest_path):
    manifest = json.loads(Path(manifest_path).read_text())
    by_name = {item["name"]: item for item in manifest.get("tests", [])}
    rows = []
    for row in data.get("rows", []):
        if WALL not in (row.get("dynamic_wall") or ""):
            continue
        item = by_name.get(row["name"], {})
        env_path = item.get("envelope")
        if not env_path or not Path(env_path).is_file():
            continue
        shape = classify(json.loads(Path(env_path).read_text()))
        rows.append({"name": row["name"], "corpus": row.get("corpus"),
                     "detail": row.get("detail"), **shape})
    counts = Counter(row["primary"] for row in rows)
    return {"schema": "c-pointer-cast-price-0.1",
            "survey_commit": data.get("measured_commit"),
            "survey_measured_at_utc": data.get("measured_at_utc"),
            "rows": sorted(rows, key=lambda row: row["name"]),
            "counts": dict(counts),
            "interpretation": (
                "Every classification is derived from Clang AST envelope nodes; "
                "no pointer address or type spelling is invented. A missing node "
                "is priced as a tool gap rather than admitted as a conversion."
            )}


def render(report):
    lines = ["# C pointer/integer wall price", "",
             "- survey commit: `%s`" % report.get("survey_commit", ""),
             "- rows priced: %d" % len(report.get("rows", [])), "",
             "| shape | files |", "| --- | ---: |"]
    for shape, count in sorted(report.get("counts", {}).items()):
        lines.append("| `%s` | %d |" % (shape, count))
    lines += ["", report["interpretation"], "",
              "| file | shape | AST evidence |", "| --- | --- | --- |"]
    for row in report.get("rows", []):
        evidence = "; ".join("%s=%s" % (key, value)
                             for key, value in row["casts"].items())
        if row["pointer_arithmetic"]:
            evidence += ("; arithmetic=" + repr(row["pointer_arithmetic"]))
        lines.append("| `%s` | `%s` | %s |" %
                     (row["name"], row["primary"], evidence or "pointer type only"))
    return "\n".join(lines) + "\n"


def self_test():
    env = {"translation_unit": {"kind": "TranslationUnit", "decls": [
        {"kind": "ImplicitCastExpr", "cast": "PointerToIntegral", "type": "long"},
        {"kind": "BinaryOperator", "op": "+", "type": "int *"}]}}
    result = classify(env)
    if result["primary"] != "explicit-pointer-to-integer":
        raise SystemExit("c_pointer_cast_price --self-test: wrong priority")
    print("c_pointer_cast_price --self-test: ok")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default=str(DEFAULT_INPUT))
    parser.add_argument("--manifest", required=False)
    parser.add_argument("--json", default=str(DEFAULT_JSON))
    parser.add_argument("--page", default=str(DEFAULT_PAGE))
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if not args.manifest:
        parser.error("--manifest is required")
    report = price(json.loads(Path(args.input).read_text()), args.manifest)
    Path(args.json).write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    Path(args.page).write_text(render(report))
    print("c_pointer_cast_price: wrote %s and %s" % (args.json, args.page))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
