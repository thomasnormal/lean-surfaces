#!/usr/bin/env python3
"""Compare the direct typed Lean DC frontend with ngspice.

Unlike the legacy JSON harness, this invokes the same Lean parser, hierarchy
flattener, and exact solver used by `load_circuit`.
"""

from __future__ import annotations

from fractions import Fraction
import math
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / "LeanModels/Circuit/DCRunner.lean"
CASES = (
    (
        ROOT / "Examples/spice/typed_divider/typed_divider.cir",
        ("in", "out"),
    ),
    (
        ROOT / "Examples/spice/robust_divider/robust_divider.cir",
        ("in", "out"),
    ),
    (
        ROOT / "Examples/spice/loaded_rc/loaded_rc.cir",
        ("in", "out"),
    ),
    (
        ROOT / "Examples/spice/chain/chain.cir",
        ("in", "out1", "out2", "out3"),
    ),
    (
        ROOT / "Examples/spice/rlc_discharge/rlc_discharge.cir",
        ("n1", "n2"),
    ),
)


def ngspice_path() -> str:
    found = shutil.which("ngspice")
    if found is not None:
        return found
    local = Path.home() / ".local/bin/ngspice"
    if local.exists():
        return str(local)
    raise SystemExit("ngspice not found")


def lean_values(deck: Path, probes: tuple[str, ...]) -> dict[str, Fraction]:
    run = subprocess.run(
        ["lake", "env", "lean", "--run", str(RUNNER), str(deck), *probes],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    values: dict[str, Fraction] = {}
    for line in run.stdout.splitlines():
        name, numerator, denominator = line.split("\t")
        values[name.lower()] = Fraction(int(numerator), int(denominator))
    return values


def ngspice_values(
    executable: str, deck: Path, directory: Path
) -> dict[str, float]:
    lines = deck.read_text().splitlines()
    materialized = directory / deck.name
    materialized.write_text(
        "\n".join([lines[0], ".options numdgt=15", *lines[1:]]) + "\n"
    )
    run = subprocess.run(
        [executable, "-b", str(materialized)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )
    values: dict[str, float] = {}
    pattern = re.compile(
        r"(?im)^\s*([a-z_][a-z0-9_.]*)\s+"
        r"([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[-+]?\d+)?)\s*$"
    )
    for name, value in pattern.findall(run.stdout + run.stderr):
        values[name.lower()] = float(value)
    return values


def main() -> int:
    executable = ngspice_path()
    failures = 0
    print(f"{'case/probe':30} {'Lean exact':>16} {'ngspice':>16}  verdict")
    print("-" * 76)
    with tempfile.TemporaryDirectory(prefix="leanmodels-typed-ngspice-") as tmp:
        directory = Path(tmp)
        for deck, probes in CASES:
            exact = lean_values(deck, probes)
            approximate = ngspice_values(executable, deck, directory)
            for probe in probes:
                observed = approximate.get(probe.lower())
                ok = observed is not None and math.isclose(
                    float(exact[probe]), observed,
                    # ngspice's batch node table is printed to about seven
                    # significant digits even with `numdgt`; compare at the
                    # established legacy-harness tolerance.
                    rel_tol=1e-6, abs_tol=1e-9,
                )
                failures += not ok
                verdict = "MATCH" if ok else "MISMATCH"
                shown = float("nan") if observed is None else observed
                print(
                    f"{deck.parent.name + '/' + probe:30} "
                    f"{str(exact[probe]):>16} {shown:16.9g}  {verdict}"
                )
    print("-" * 76)
    print(f"{len(CASES)} typed DC decks: {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
