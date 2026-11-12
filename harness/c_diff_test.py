#!/usr/bin/env python3
"""Pinned Clang/Lean differential rows for the C tier.

Every row compiles the unchanged source with the exact pinned compiler and
profile flags, extracts the same source with that compiler, and runs the
resulting envelope through the C model. Missing or mismatched oracle inputs are
ORACLE, never a green match.  A native assertion/UB result is a refusal or
divergence according to the row, never an unavailable oracle.
"""

from __future__ import print_function

import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CASES = ROOT / "harness" / "c_cases.json"
_extract_spec = importlib.util.spec_from_file_location(
    "c_extractor_pin", ROOT / "extractors" / "c" / "extract.py")
_extract = importlib.util.module_from_spec(_extract_spec)
_extract_spec.loader.exec_module(_extract)
PINNED_VERSION = _extract.PINNED_FRONTEND_VERSION
PROFILE_FLAGS = ["-std=c23", "-D_FORTIFY_SOURCE=0"]
COMPILE_FLAGS = ["--no-default-config", "-std=c23", "-O0", "-g",
                 "-D_FORTIFY_SOURCE=0", "-fno-strict-aliasing"]


def run(args, env=None, timeout=120):
    return subprocess.run(args, cwd=str(ROOT), env=env, text=True,
                          capture_output=True, timeout=timeout)


def oracle():
    requested = os.environ.get("LEAN_C_CLANG", "clang")
    executable = shutil.which(requested) if os.path.basename(requested) == requested else requested
    if not executable or not os.path.exists(executable):
        return None, "set LEAN_C_CLANG to the pinned compiler"
    probed = run([executable, "--version"])
    first = probed.stdout.splitlines()[0] if probed.stdout else ""
    if probed.returncode != 0 or first != PINNED_VERSION:
        return None, "expected %s, got %s" % (PINNED_VERSION, first or "<none>")
    return executable, first


def model_env(clang):
    env = dict(os.environ)
    env["LEAN_C_CLANG"] = clang
    return env


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def check_envelope(payload, checks, name):
    nodes = list(walk(payload))
    for check in checks:
        if check == "array_filler":
            if not any(n.get("kind") == "InitListExpr" and
                       "array_filler" in n for n in nodes):
                return name + ": missing required array_filler field"
        elif check == "compound_promotion":
            compounds = [n for n in nodes
                         if n.get("kind") == "CompoundAssignOperator"]
            if not compounds or any(not n.get("compute_lhs_type") or
                                    not n.get("compute_result_type")
                                    for n in compounds):
                return name + ": missing Clang compound promotion evidence"
        elif check == "record_attributes":
            wanted = {"P": "MaxFieldAlignmentAttr", "Q": "PackedAttr",
                      "R": "AlignedAttr"}
            records = {n.get("name"): n for n in nodes
                       if n.get("kind") == "RecordDecl"}
            for record, attr in wanted.items():
                fields = records.get(record, {}).get("fields", [])
                found = {f.get("c_kind") for f in fields
                         if f.get("kind") == "Unsupported"}
                if attr not in found:
                    return name + ": attribute was dropped: " + record
        else:
            return name + ": unknown envelope check " + check
    return None


def classify(row, clang, work):
    source = work / (row["id"] + ".c")
    source.write_text(row["source"] + "\n", encoding="utf-8")
    native = work / row["id"]
    flags = list(COMPILE_FLAGS)
    if row.get("sanitize"):
        flags += ["-fsanitize=undefined", "-fno-sanitize-recover=all"]
    compiled = run([clang] + flags + [str(source), "-o", str(native)])
    if compiled.returncode:
        return "ORACLE", "native compile failed: " + compiled.stderr[-800:]
    native_run = run([str(native)], timeout=30)

    envelope = work / (row["id"] + ".json")
    extracted = run([sys.executable, "extractors/c/extract.py", str(source),
                     "-o", str(envelope)], env=model_env(clang))
    if extracted.returncode:
        return "EXTRACT", extracted.stderr[-800:]
    payload = json.loads(envelope.read_text(encoding="utf-8"))
    problem = check_envelope(payload, row.get("envelope_checks", []), row["id"])
    if problem:
        return "EXTRACT", problem
    version = payload.get("frontend", {}).get("version")
    if version != PINNED_VERSION:
        return "EXTRACT", "envelope frontend.version is not pinned: %r" % version

    runner = ROOT / ".lake" / "build" / "bin" / "c-torture-run"
    command = [str(runner)] if runner.exists() else ["lake", "exe", "c-torture-run"]
    model = run(command + ["--single", str(envelope), "512"],
                env=model_env(clang), timeout=180)
    if row["expect"] == "refuse":
        if model.returncode == 3:
            detail = model.stderr.strip() or "native exit %d" % native_run.returncode
            expected_error = row.get("error")
            if expected_error and expected_error not in detail:
                return "DIVERGE", "expected refusal %r, got %r" % (expected_error, detail)
            return "REFUSE", detail
        if model.returncode == 0:
            return "DIVERGE", "model returned %s for a refusal row" % model.stdout.strip()
        return "ORACLE", "model runner failed: " + (model.stderr or model.stdout)[-800:]

    if model.returncode != 0:
        return "DIVERGE", "model refused: " + (model.stderr or model.stdout)[-800:]
    try:
        line = next((x for x in reversed(model.stdout.splitlines())
                     if x.startswith("ok\t")), "")
        value = int(line.split("\t", 1)[1])
    except (ValueError, IndexError):
        return "DIVERGE", "model did not print an integer: %r" % model.stdout
    expected = int(row["return_value"])
    native_value = native_run.returncode if native_run.returncode >= 0 else None
    if value != expected or native_value != (expected % 256):
        return "DIVERGE", "model=%d native_exit=%r expected=%d" % (value, native_value, expected)
    return "MATCH", "model=%d native_exit=%d" % (value, native_value)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--allow-oracle", action="store_true",
                    help="report exploratory ORACLE rows without failing")
    ap.add_argument("--json", type=Path)
    args = ap.parse_args()
    rows = json.loads(CASES.read_text(encoding="utf-8"))
    clang, detail = oracle()
    print("C oracle:", detail)
    if clang is None:
        counts = {"ORACLE": len(rows)}
        for row in rows:
            print(row["id"] + ": ORACLE " + detail)
        if args.json:
            args.json.write_text(json.dumps({"compiler": detail, "counts": counts}, indent=2) + "\n")
        return 0 if args.allow_oracle else 2
    counts = {}
    results = {}
    with tempfile.TemporaryDirectory(prefix="c-diff-") as temp:
        work = Path(temp)
        for row in rows:
            verdict, why = classify(row, clang, work)
            counts[verdict] = counts.get(verdict, 0) + 1
            results[row["id"]] = {"verdict": verdict, "detail": why}
            print(row["id"] + ": " + verdict + " " + why)
    if args.json:
        args.json.write_text(json.dumps({"compiler": detail, "counts": counts,
                                         "rows": results}, indent=2, sort_keys=True) + "\n")
    if counts.get("DIVERGE") or counts.get("EXTRACT") or counts.get("TIMEOUT"):
        return 1
    if counts.get("ORACLE") and not args.allow_oracle:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
