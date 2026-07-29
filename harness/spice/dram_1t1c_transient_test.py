#!/usr/bin/env python3
"""Validate the proved hold, write-zero, and write-one 1T1C phases."""

from __future__ import annotations

import argparse
import math
from pathlib import Path
import re
import tempfile

import loaded_inverter_transient_test as common

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "Examples/spice/dram_1t1c/dram_1t1c.cir"
HORIZON = 5e-9
STEP = 5e-12
WRITE_RATE = (100e-6 * 4.0**2) / (2.0 * 30e-15 * 5.0)
WRITE_ONE_RATE = 100e-6 / (2.0 * 30e-15)


def materialize(directory: Path, mode: str) -> Path:
    source = SOURCE.read_text()
    source, count = re.subn(r"(?im)^\.end\s*$", "", source, count=1)
    if count != 1:
        raise RuntimeError("1T1C source has no unique .end")
    if mode == "hold":
        word, bit, initial = 0, 0, 3
    elif mode == "write_zero":
        word, bit, initial = 5, 0, 5
    elif mode == "write_one":
        word, bit, initial = 5, 5, 0
    else:
        raise ValueError(f"unsupported 1T1C mode: {mode}")
    deck = directory / f"dram_1t1c_{mode}.cir"
    deck.write_text(
        source.rstrip()
        + "\n"
        + f"vword word 0 dc {word}\n"
        + f"vbit bit 0 dc {bit}\n"
        + f".ic v(store)={initial}\n"
        + f".tran {STEP:g} {HORIZON:g} uic\n"
        + ".print tran v(store)\n"
        + ".end\n"
    )
    return deck


def run(
    simulator: str, executable: str, deck: Path, directory: Path
) -> list[tuple[float, float]]:
    if simulator == "ngspice":
        return common.run_ngspice(executable, deck)
    return common.run_spectre(executable, deck, directory, "store")


def check_hold(rows: list[tuple[float, float]]) -> int:
    deviation = max(abs(voltage - 3.0) for _, voltage in rows)
    ok = deviation <= 2e-5
    print(
        f" hold: {len(rows):4} points, max retention error={deviation:.3g}, "
        f"retained={'yes' if ok else 'NO'}"
    )
    return 0 if ok else 1


def check_write(rows: list[tuple[float, float]]) -> int:
    failures = 0
    previous = rows[0][1]
    for time, voltage in rows:
        envelope = 5.0 * math.exp(-WRITE_RATE * max(time, 0.0))
        if (
            voltage < -2e-5
            or voltage > 5.0 + 2e-5
            or voltage > previous + 2e-5
            or voltage > envelope + 2e-2
        ):
            failures += 1
            break
        previous = voltage
    endpoint = rows[-1][1]
    if endpoint > 0.02:
        failures += 1
    print(
        f"write: {len(rows):4} points, v(store)={endpoint:.9g}, "
        f"bounded/monotone/enclosed={'yes' if failures == 0 else 'NO'}"
    )
    return failures


def write_one_trace(time: float) -> float:
    return 4.0 - 4.0 / (1.0 + WRITE_ONE_RATE * 4.0 * max(time, 0.0))


def check_write_one(rows: list[tuple[float, float]]) -> int:
    failures = 0
    previous = rows[0][1]
    at_one_ns = None
    max_model_error = 0.0
    for time, voltage in rows:
        expected = write_one_trace(time)
        max_model_error = max(max_model_error, abs(voltage - expected))
        if time >= 1e-9 and at_one_ns is None:
            at_one_ns = voltage
        if (
            voltage < -2e-5
            or voltage > 4.0 + 2e-5
            or voltage + 2e-5 < previous
            or abs(voltage - expected) > 2e-2
        ):
            failures += 1
            break
        previous = voltage
    endpoint = rows[-1][1]
    if at_one_ns is None or not (3.0 - 2e-2 <= at_one_ns <= 4.0 + 2e-5):
        failures += 1
    print(
        f"write-one: {len(rows):4} points, v(store)={endpoint:.9g}, "
        f"max closed-form error={max_model_error:.3g}, "
        f"bounded/monotone/in-band={'yes' if failures == 0 else 'NO'}"
    )
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sim", choices=("ngspice", "spectre"), required=True)
    args = parser.parse_args()
    executable = common.executable(args.sim)
    failures = 0
    with tempfile.TemporaryDirectory(
        prefix=f"leanmodels-dram-1t1c-{args.sim}-"
    ) as tmp:
        directory = Path(tmp)
        failures += check_hold(
            run(args.sim, executable, materialize(directory, "hold"), directory)
        )
        failures += check_write(
            run(
                args.sim,
                executable,
                materialize(directory, "write_zero"),
                directory,
            )
        )
        failures += check_write_one(
            run(
                args.sim,
                executable,
                materialize(directory, "write_one"),
                directory,
            )
        )
    print(f"{args.sim}: 1T1C hold/write-zero/write-one: {failures} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
