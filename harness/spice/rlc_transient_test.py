#!/usr/bin/env python3
"""Compare ngspice's RLC transient with the trajectory proved in Lean."""

from __future__ import annotations

import math
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "Examples/spice/rlc_discharge/rlc_discharge.cir"


def ngspice_path() -> str:
    found = shutil.which("ngspice")
    if found:
        return found
    local = Path.home() / ".local/bin/ngspice"
    if local.exists():
        return str(local)
    raise SystemExit("ngspice not found")


def transient_deck(directory: Path) -> Path:
    source = SOURCE.read_text()
    source, count = re.subn(
        r"(?im)^lpath n1 n2 1u\s*$",
        "lpath n1 n2 1u ic=0",
        source,
        count=1,
    )
    if count != 1:
        raise RuntimeError("RLC deck has no unique lpath card")
    source, count = re.subn(
        r"(?im)^\.op\s*$",
        ".ic v(n1)=5 v(n2)=0\n"
        ".tran 10n 10u uic\n"
        ".print tran v(n1) v(n2) i(lpath)",
        source,
        count=1,
    )
    if count != 1:
        raise RuntimeError("RLC deck has no unique .op card")
    deck = directory / "rlc_transient.cir"
    deck.write_text(source)
    return deck


def parse_trace(output: str) -> list[tuple[float, float, float, float]]:
    rows: list[tuple[float, float, float, float]] = []
    number = r"([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[-+]?\d+)?)"
    pattern = re.compile(
        rf"^\s*\d+\s+{number}\s+{number}\s+{number}\s+{number}\s*$",
        re.IGNORECASE,
    )
    for line in output.splitlines():
        match = pattern.match(line)
        if match:
            rows.append(tuple(float(value) for value in match.groups()))
    if not rows:
        raise RuntimeError("ngspice emitted no RLC transient rows")
    return rows


def analytic(time: float) -> tuple[float, float, float]:
    decay = math.exp(-1_000_000.0 * time)
    storage = 5.0 * (1.0 + 1_000_000.0 * time) * decay
    current = 5_000_000.0 * time * decay
    return storage, 2.0 * current, current


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="leanmodels-rlc-") as tmp:
        deck = transient_deck(Path(tmp))
        run = subprocess.run(
            [ngspice_path(), "-b", str(deck)],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
            timeout=60,
        )
        rows = parse_trace(run.stdout + run.stderr)

    failures = 0
    previous_energy = math.inf
    for _, storage, _load, current in rows:
        energy = 0.5e-6 * (storage * storage + current * current)
        if energy > previous_energy + 1e-10:
            failures += 1
            break
        previous_energy = energy

    print(
        f"{'time':>10} {'Lean n1':>13} {'ngspice n1':>13} "
        f"{'Lean n2':>13} {'ngspice n2':>13}"
    )
    print("-" * 68)
    for target in (0.2e-6, 0.5e-6, 1e-6, 2e-6, 5e-6):
        time, storage, load, _current = min(
            rows, key=lambda row: abs(row[0] - target)
        )
        expected_storage, expected_load, _ = analytic(time)
        relative = max(
            abs(storage - expected_storage) / max(abs(expected_storage), 1e-12),
            abs(load - expected_load) / max(abs(expected_load), 1e-12),
        )
        if relative > 0.01:
            failures += 1
        print(
            f"{time:10.3g} {expected_storage:13.7g} {storage:13.7g} "
            f"{expected_load:13.7g} {load:13.7g}"
        )
    print("-" * 68)
    print(f"energy envelope and analytic comparison: {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
