#!/usr/bin/env python3
"""Validate the exact Gaussian-rational AC theorem against a simulator."""

from __future__ import annotations

import argparse
import math
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "Examples/spice/ac_lowpass/ac_lowpass.cir"
FREQUENCY_HZ = 1500.0 / (2.0 * math.pi)
EXPECTED = complex(1.0 / 3.0, -1.0 / 3.0)


def executable(name: str) -> str:
    found = shutil.which(name)
    if found is not None:
        return found
    if name == "ngspice":
        local = Path.home() / ".local/bin/ngspice"
        if local.exists():
            return str(local)
    raise SystemExit(f"{name} not found")


def materialize(directory: Path, points: int) -> Path:
    source = SOURCE.read_text()
    source, count = re.subn(
        r"(?im)^vdrive in 0 dc 0\s*$",
        "vdrive in 0 dc 0 ac 1",
        source,
        count=1,
    )
    if count != 1:
        raise RuntimeError("AC deck has no unique vdrive card")
    stop = FREQUENCY_HZ if points == 1 else FREQUENCY_HZ + 1e-12
    source, count = re.subn(
        r"(?im)^\.op\s*$",
        f".ac lin {points} {FREQUENCY_HZ:.15g} {stop:.15g}\n"
        ".print ac vr(out) vi(out)",
        source,
        count=1,
    )
    if count != 1:
        raise RuntimeError("AC deck has no unique .op card")
    deck = directory / "ac_lowpass_validation.cir"
    deck.write_text(source)
    return deck


def run_ngspice(directory: Path) -> complex:
    deck = materialize(directory, 1)
    run = subprocess.run(
        [executable("ngspice"), "-b", str(deck)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )
    number = r"([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[-+]?\d+)?)"
    pattern = re.compile(
        rf"^\s*0\s+{number}\s+{number}\s+{number}\s*$",
        re.IGNORECASE | re.MULTILINE,
    )
    match = pattern.search(run.stdout + run.stderr)
    if match is None:
        raise RuntimeError("ngspice emitted no AC output row")
    _frequency, real, imaginary = match.groups()
    return complex(float(real), float(imaginary))


def run_spectre(directory: Path) -> complex:
    deck = materialize(directory, 2)
    raw = directory / "ac_lowpass_validation.raw"
    run = subprocess.run(
        [
            executable("spectre"),
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
    if run.returncode != 0:
        raise RuntimeError(
            f"Spectre AC failed:\n{run.stdout}\n{run.stderr}"
        )
    text = raw.read_text()
    output = re.search(
        r"(?m)^\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?),"
        r"([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?)\s*$",
        text.split("Values:", maxsplit=1)[1],
    )
    if output is None:
        raise RuntimeError("Spectre emitted no complex AC value")
    # The first complex row is frequency. The third is `out`; parse records
    # rather than relying on a human-readable print suffix.
    complex_values = [
        complex(float(real), float(imaginary))
        for real, imaginary in re.findall(
            r"(?m)^\s*(?:\d+\s+)?"
            r"([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?),"
            r"([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?)\s*$",
            text.split("Values:", maxsplit=1)[1],
        )
    ]
    if len(complex_values) < 3:
        raise RuntimeError("Spectre AC record is truncated")
    return complex_values[2]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sim", choices=("ngspice", "spectre"), required=True)
    arguments = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix=f"leanmodels-{arguments.sim}-ac-") as tmp:
        observed = (
            run_ngspice(Path(tmp))
            if arguments.sim == "ngspice"
            else run_spectre(Path(tmp))
        )
    error = abs(observed - EXPECTED)
    ok = error <= 1e-6
    print(
        f"{arguments.sim}: Lean exact = 1/3 - j/3, "
        f"observed = {observed.real:.12g} {observed.imag:+.12g}j, "
        f"|error| = {error:.3g}: {'MATCH' if ok else 'MISMATCH'}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
