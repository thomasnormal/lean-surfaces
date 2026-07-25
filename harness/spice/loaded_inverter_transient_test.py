#!/usr/bin/env python3
"""Validate the proved loaded-inverter transient with ngspice or Spectre.

The checked source is an open component. This harness adds supply/input
drivers and initial conditions only to a temporary testbench. Simulator
agreement is validation; the Lean theorem depends on neither simulator.
"""

from __future__ import annotations

import argparse
import math
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "Examples/spice/loaded_inverter/loaded_inverter.cir"
SUPPLY = 5.0
HORIZON = 100e-9
STEP = 0.2e-9


def executable(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    if name == "ngspice":
        local = Path.home() / ".local/bin/ngspice"
        if local.exists():
            return str(local)
    raise SystemExit(f"{name} not found")


def materialize(directory: Path, rising: bool) -> Path:
    source = SOURCE.read_text()
    source, count = re.subn(r"(?im)^\.end\s*$", "", source, count=1)
    if count != 1:
        raise RuntimeError("loaded inverter source has no unique .end")
    input_voltage = 0 if rising else 5
    initial_voltage = 0 if rising else 5
    name = "rise" if rising else "fall"
    deck = directory / f"loaded_inverter_{name}.cir"
    deck.write_text(
        source.rstrip()
        + "\n"
        + f"vddsrc vdd 0 dc {SUPPLY:g}\n"
        + f"vin in 0 dc {input_voltage:g}\n"
        + f".ic v(out)={initial_voltage:g}\n"
        + f".tran {STEP:g} {HORIZON:g} uic\n"
        + ".print tran v(out)\n"
        + ".end\n"
    )
    return deck


def parse_ngspice(text: str) -> list[tuple[float, float]]:
    pattern = re.compile(
        r"^\s*\d+\s+"
        r"([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[-+]?\d+)?)\s+"
        r"([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[-+]?\d+)?)\s*$",
        re.IGNORECASE,
    )
    rows = []
    for line in text.splitlines():
        match = pattern.match(line)
        if match:
            rows.append((float(match.group(1)), float(match.group(2))))
    if not rows:
        raise RuntimeError("ngspice emitted no transient rows")
    return rows


def parse_nutascii(path: Path) -> tuple[list[str], list[list[float]]]:
    text = path.read_text()
    header, values_text = text.split("Values:", maxsplit=1)
    match = re.search(
        r"No\. Variables:\s*(\d+).*?Variables:(.*)", header, re.DOTALL
    )
    if match is None:
        raise RuntimeError("Spectre output has no variable table")
    count = int(match.group(1))
    names = []
    for line in match.group(2).splitlines():
        fields = line.split()
        if len(fields) >= 2 and fields[0].isdigit():
            names.append(fields[1].lower())
    tokens = values_text.split()
    stride = count + 1
    if len(names) != count or not tokens or len(tokens) % stride:
        raise RuntimeError("Spectre transient result is malformed")
    rows = []
    for offset in range(0, len(tokens), stride):
        rows.append(
            [float(value) for value in tokens[offset + 1 : offset + stride]]
        )
    return names, rows


def run_ngspice(exe: str, deck: Path) -> list[tuple[float, float]]:
    run = subprocess.run(
        [exe, "-b", str(deck)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )
    return parse_ngspice(run.stdout + run.stderr)


def run_spectre(
    exe: str, deck: Path, directory: Path, probe: str = "out"
) -> list[tuple[float, float]]:
    raw = directory / f"{deck.stem}.raw"
    run = subprocess.run(
        [
            exe,
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
    names, values = parse_nutascii(raw)
    try:
        time_index = names.index("time")
        output_index = names.index(probe)
    except ValueError as error:
        raise RuntimeError(
            f"Spectre variables omit time/{probe}: {names}"
        ) from error
    return [(row[time_index], row[output_index]) for row in values]


def check(rows: list[tuple[float, float]], rising: bool) -> int:
    failures = 0
    previous = rows[0][1]
    rate = 80e6 if rising else 160e6
    initial_error = SUPPLY
    for time, voltage in rows:
        bounded = -2e-5 <= voltage <= SUPPLY + 2e-5
        monotone = (
            voltage + 2e-5 >= previous
            if rising
            else voltage <= previous + 2e-5
        )
        error = SUPPLY - voltage if rising else voltage
        proved_envelope = initial_error * math.exp(-rate * max(time, 0.0))
        # Numerical integration and simulator device conventions need a small
        # absolute allowance around the exact model theorem.
        envelope_ok = error <= proved_envelope + 2e-2
        if not (bounded and monotone and envelope_ok):
            failures += 1
            break
        previous = voltage
    endpoint = rows[-1][1]
    if rising and endpoint < 4.98:
        failures += 1
    if not rising and endpoint > 0.02:
        failures += 1
    direction = "rise" if rising else "fall"
    print(
        f"{direction:>5}: {len(rows):4} points, "
        f"v(out)={endpoint:.9g}, "
        f"bounded/monotone/enclosed={'yes' if failures == 0 else 'NO'}"
    )
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sim", choices=("ngspice", "spectre"), required=True)
    args = parser.parse_args()
    exe = executable(args.sim)
    failures = 0
    with tempfile.TemporaryDirectory(
        prefix=f"leanmodels-inverter-{args.sim}-"
    ) as tmp:
        directory = Path(tmp)
        for rising in (True, False):
            deck = materialize(directory, rising)
            rows = (
                run_ngspice(exe, deck)
                if args.sim == "ngspice"
                else run_spectre(exe, deck, directory)
            )
            failures += check(rows, rising)
    print(f"{args.sim}: loaded-inverter transient: {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
