#!/usr/bin/env python3
"""Compare the exact Lean DC solver with ngspice `.op` results."""

import argparse
import json
import math
import re
import shutil
import subprocess
import tempfile
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CASES = Path(__file__).with_name("cases.json")


def ngspice_path():
    found = shutil.which("ngspice")
    if found:
        return found
    local = Path.home() / ".local/bin/ngspice"
    if local.exists():
        return str(local)
    raise SystemExit("ngspice not found on PATH or at ~/.local/bin/ngspice")


def materialize(case, directory):
    source = (ROOT / case["source"]).read_text()
    for name, value in case.get("drives", {}).items():
        pattern = rf"(?im)^({re.escape(name)}\s+\S+\s+0\s+(?:dc\s+)?)\S+"
        source, count = re.subn(pattern, rf"\g<1>{value}", source)
        if count != 1:
            raise RuntimeError(f"{case['name']}: could not replace drive {name}")
    deck = directory / f"{case['name']}.cir"
    deck.write_text(source)
    subprocess.run(
        ["python3", str(ROOT / "extractors/spice/extract.py"), str(deck)],
        cwd=ROOT, check=True, capture_output=True, text=True)
    # Ask ngspice for enough digits to support the documented 1e-6 relative
    # comparison. The exact envelope is generated first because `.options`
    # is deliberately outside the M0 semantic card vocabulary.
    lines = deck.read_text().splitlines()
    deck.write_text("\n".join([lines[0], ".options numdgt=15", *lines[1:]]) + "\n")
    return deck, deck.with_suffix(".json")


def parse_ngspice(text, probe):
    label = probe[1:] + "#branch" if probe.startswith("@") else probe
    match = re.search(
        rf"(?im)^\s*{re.escape(label)}\s+([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[-+]?\d+)?)\s*$",
        text)
    if not match:
        raise RuntimeError(f"ngspice output has no value for {label}")
    return float(match.group(1))


def run_lean(json_path, probes, no_build):
    if not no_build:
        subprocess.run(["lake", "build", "LeanModels.Spice.Tests"], cwd=ROOT, check=True)
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "harness/spice/Runner.lean",
         str(json_path), *probes], cwd=ROOT, check=True, capture_output=True, text=True)
    values = {}
    for line in result.stdout.splitlines():
        name, numerator, denominator = line.split("\t")
        values[name] = Fraction(int(numerator), int(denominator))
    return values


def run_lean_raw(json_path, probes, no_build):
    if not no_build:
        subprocess.run(["lake", "build", "LeanModels.Spice.Tests"], cwd=ROOT, check=True)
    return subprocess.run(
        ["lake", "env", "lean", "--run", "harness/spice/Runner.lean",
         str(json_path), *probes], cwd=ROOT, capture_output=True, text=True)


def close(exact, approximate):
    target = float(exact)
    # ngspice's human-readable source-current table is rounded more heavily
    # than its node table; the absolute floor covers that printed precision.
    return math.isclose(target, approximate, rel_tol=1e-6, abs_tol=1e-8)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-build", action="store_true")
    args = parser.parse_args()
    cases = json.loads(CASES.read_text())
    spice = ngspice_path()
    failures = 0
    print(f"{'case/probe':28} {'Lean exact':>16} {'ngspice':>16}  verdict")
    print("-" * 72)
    with tempfile.TemporaryDirectory(prefix="leanmodels-spice-") as tmp:
        directory = Path(tmp)
        built = args.no_build
        for case in cases:
            deck, envelope = materialize(case, directory)
            run = subprocess.run([spice, "-b", str(deck)], cwd=ROOT,
                                 check=True, capture_output=True, text=True)
            probes = list(case["probes"])
            if case.get("expect_error") == "singular":
                lean_run = run_lean_raw(envelope, probes, built)
                built = True
                lean_singular = (lean_run.returncode != 0 and
                                 "singular" in lean_run.stderr.lower())
                ngspice_singular = "singular matrix" in (
                    run.stdout + run.stderr).lower()
                ok = lean_singular and ngspice_singular
                failures += not ok
                verdict = "MATCH (singular)" if ok else "MISMATCH"
                print(f"{case['name']:28} {'singular':>16} {'singular':>16}  {verdict}")
                continue
            lean = run_lean(envelope, probes, built)
            built = True
            for probe, expected_text in case["probes"].items():
                expected = Fraction(expected_text)
                exact = lean[probe]
                approximate = parse_ngspice(run.stdout + run.stderr, probe)
                ok = exact == expected and close(exact, approximate)
                failures += not ok
                verdict = "MATCH" if ok else "MISMATCH"
                print(f"{case['name'] + '/' + probe:28} {str(exact):>16} "
                      f"{approximate:16.9g}  {verdict}")
    print("-" * 72)
    print(f"{len(cases)} cases: {failures} failed")
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
