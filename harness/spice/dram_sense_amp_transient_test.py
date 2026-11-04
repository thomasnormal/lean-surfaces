#!/usr/bin/env python3
"""Validate the source-backed differential sense amplifier externally.

The committed source is a component deck. This harness adds the supply and
initial-condition stimulus only in a temporary testbench. Ngspice and Spectre
are independent numerical evidence; neither appears in a Lean premise.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import tempfile

import loaded_inverter_transient_test as common

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "Examples/spice/dram_sense_amp/dram_sense_amp.cir"
STEP = 10e-12
HORIZON = 50e-9


def materialize(
    directory: Path, simulator: str, true_wins: bool
) -> tuple[Path, Path | None]:
    source = SOURCE.read_text()
    source, count = re.subn(r"(?im)^\.end\s*$", "", source, count=1)
    if count != 1:
        raise RuntimeError("sense-amplifier source has no unique .end")
    q0, qb0 = (2.55, 2.45) if true_wins else (2.45, 2.55)
    stem = "dram_sense_true" if true_wins else "dram_sense_false"
    data = directory / f"{stem}.data" if simulator == "ngspice" else None
    lines = [
        source.rstrip(),
        "vddsrc vdd 0 dc 5",
        f".ic v(q)={q0:g} v(qb)={qb0:g}",
        f".tran {STEP:g} {HORIZON:g} uic",
    ]
    if data is not None:
        lines.extend(
            [
                ".control",
                "run",
                f"wrdata {data} v(q) v(qb)",
                ".endc",
            ]
        )
    lines.append(".end")
    deck = directory / f"{stem}.cir"
    deck.write_text("\n".join(lines) + "\n")
    return deck, data


def run_ngspice(
    executable: str, deck: Path, data: Path
) -> list[tuple[float, float, float]]:
    run = subprocess.run(
        [executable, "-b", str(deck)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )
    if run.returncode:
        raise RuntimeError(
            f"ngspice failed for {deck.name}:\n{run.stdout}\n{run.stderr}"
        )
    rows = []
    for line in data.read_text().splitlines():
        fields = [float(value) for value in line.split()]
        if len(fields) != 4:
            raise RuntimeError(f"unexpected ngspice wrdata row: {line}")
        if abs(fields[0] - fields[2]) > 1e-18:
            raise RuntimeError("ngspice emitted inconsistent time columns")
        rows.append((fields[0], fields[1], fields[3]))
    if not rows:
        raise RuntimeError("ngspice emitted no sense-amplifier samples")
    return rows


def run_spectre(
    executable: str, deck: Path, directory: Path
) -> list[tuple[float, float, float]]:
    raw = directory / f"{deck.stem}.raw"
    run = subprocess.run(
        [
            executable,
            "-log",
            "-format",
            "nutascii",
            "-raw",
            str(raw),
            "-outdir",
            str(directory),
            str(deck),
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=60,
    )
    if run.returncode:
        raise RuntimeError(
            f"Spectre failed for {deck.name}:\n{run.stdout}\n{run.stderr}"
        )
    names, values = common.parse_nutascii(raw)
    time_index = names.index("time")
    q_index = names.index("q")
    qb_index = names.index("qb")
    return [
        (row[time_index], row[q_index], row[qb_index])
        for row in values
    ]


def check(
    simulator: str,
    rows: list[tuple[float, float, float]],
    true_wins: bool,
) -> int:
    failures = 0
    for _time, q, qb in rows:
        if not (-2e-4 <= q <= 5.0002 and -2e-4 <= qb <= 5.0002):
            failures += 1
            break
    initial_difference = rows[0][1] - rows[0][2]
    early = min(rows, key=lambda row: abs(row[0] - 1e-9))
    early_difference = early[1] - early[2]
    q_final, qb_final = rows[-1][1], rows[-1][2]
    if true_wins:
        failures += int(initial_difference <= 0)
        failures += int(early_difference <= initial_difference)
        failures += int(q_final < 4.98 or qb_final > 0.02)
    else:
        failures += int(initial_difference >= 0)
        failures += int(early_difference >= initial_difference)
        failures += int(q_final > 0.02 or qb_final < 4.98)
    verdict = "MATCH" if failures == 0 else "MISMATCH"
    direction = "q" if true_wins else "qb"
    print(
        f"{simulator:7} {direction} wins: "
        f"d0={initial_difference:.6g} d1ns={early_difference:.6g} "
        f"q={q_final:.9g} qb={qb_final:.9g} {verdict}"
    )
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sim", choices=("ngspice", "spectre"), required=True)
    args = parser.parse_args()
    executable = common.executable(args.sim)
    failures = 0
    with tempfile.TemporaryDirectory(
        prefix=f"leanmodels-dram-sense-{args.sim}-"
    ) as tmp:
        directory = Path(tmp)
        for true_wins in (True, False):
            deck, data = materialize(directory, args.sim, true_wins)
            rows = (
                run_ngspice(executable, deck, data)
                if args.sim == "ngspice"
                else run_spectre(executable, deck, directory)
            )
            failures += check(args.sim, rows, true_wins)
    print(f"{args.sim}: differential sense amplifier: {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
