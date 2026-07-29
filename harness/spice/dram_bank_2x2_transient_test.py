#!/usr/bin/env python3
"""Exercise the source-bound 2x2 DRAM bank with ngspice or Spectre.

The committed deck is an open component.  This harness adds drivers, phase
timing, and initial charge only in a temporary testbench.  Simulator traces
are independent evidence; none is a premise of the Lean assurance theorem.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import tempfile

import loaded_inverter_transient_test as common

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "Examples/spice/dram_bank_2x2/dram_bank_2x2.cir"
PROBES = (
    "xbank.bit0",
    "xbank.bit1",
    "xbank.sensed0",
    "xbank.sensed1",
    "xbank.writebus",
    "dout",
    "xbank.store00",
    "xbank.store01",
    "xbank.store10",
    "xbank.store11",
)
PRECHARGE_SAMPLE = 10e-9
SENSE_SAMPLE = 19e-9
FINAL_SAMPLE = 40e-9
WRITE_FINAL_SAMPLE = 70e-9


def stored_voltage(bit: bool) -> float:
    return 4.0 if bit else 0.0


def materialize(
    directory: Path,
    simulator: str,
    row: int,
    column: int,
    bits: tuple[tuple[bool, bool], tuple[bool, bool]],
    operation: str = "read",
    write_value: bool = False,
) -> tuple[Path, Path | None]:
    source = SOURCE.read_text()
    source, count = re.subn(r"(?im)^\.end\s*$", "", source, count=1)
    if count != 1:
        raise RuntimeError("DRAM bank source has no unique .end")
    row_voltage = 5 if row else 0
    column_voltage = 5 if column else 0
    if operation == "write":
        restore = "pwl(0 0 20n 0 20.1n 5 45n 5 45.1n 0 75n 0)"
        restoreb = "pwl(0 5 20n 5 20.1n 0 45n 0 45.1n 5 75n 5)"
        write = "pwl(0 0 47n 0 47.1n 5 75n 5)"
        writeb = "pwl(0 5 47n 5 47.1n 0 75n 0)"
        final_time = "75n"
    else:
        restore = "pwl(0 0 20n 0 20.1n 5 50n 5)"
        restoreb = "pwl(0 5 20n 5 20.1n 0 50n 0)"
        write = "0"
        writeb = "5"
        final_time = "40n"
    testbench = [
        source.rstrip(),
        "vvdd vdd 0 5",
        "vvpre vpre 0 2.5",
        f"vrow row 0 {row_voltage}",
        f"vrowb rowb 0 {5 - row_voltage}",
        f"vcol col 0 {column_voltage}",
        f"vcolb colb 0 {5 - column_voltage}",
        "vprectl precharge 0 pwl(0 5 10n 5 10.1n 0 50n 0)",
        "vact activate 0 pwl(0 0 12n 0 12.1n 5 50n 5)",
        f"vrestore restore 0 {restore}",
        f"vrestoreb restoreb 0 {restoreb}",
        f"vwrite write 0 {write}",
        f"vwriteb writeb 0 {writeb}",
        f"vdin din 0 {5 if write_value else 0}",
        ".ic "
        + " ".join(
            f"v(xbank.store{r}{c})={stored_voltage(bits[r][c]):g}"
            for r in range(2)
            for c in range(2)
        ),
        f".tran 50p {final_time} uic",
    ]
    data_path = None
    if simulator == "ngspice":
        data_path = directory / (
            f"dram_bank_{operation}_r{row}c{column}"
            f"{int(write_value) if operation == 'write' else ''}.data"
        )
        testbench.extend(
            [
                ".control",
                "run",
                f"wrdata {data_path} " + " ".join(f"v({p})" for p in PROBES),
                ".endc",
            ]
        )
    testbench.append(".end")
    deck = directory / (
        f"dram_bank_{operation}_r{row}c{column}"
        f"{int(write_value) if operation == 'write' else ''}.cir"
    )
    deck.write_text("\n".join(testbench) + "\n")
    return deck, data_path


def run_ngspice(
    executable: str, deck: Path, data_path: Path
) -> dict[str, list[tuple[float, float]]]:
    subprocess.run(
        [executable, "-b", str(deck)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )
    traces = {probe: [] for probe in PROBES}
    for line in data_path.read_text().splitlines():
        fields = [float(value) for value in line.split()]
        if len(fields) != 2 * len(PROBES):
            raise RuntimeError(f"unexpected ngspice wrdata row: {line}")
        for index, probe in enumerate(PROBES):
            traces[probe].append((fields[2 * index], fields[2 * index + 1]))
    if not traces[PROBES[0]]:
        raise RuntimeError("ngspice emitted no DRAM transient rows")
    return traces


def run_spectre(
    executable: str, deck: Path, directory: Path
) -> dict[str, list[tuple[float, float]]]:
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
    names, rows = common.parse_nutascii(raw)
    time_index = names.index("time")
    traces = {}
    for probe in PROBES:
        probe_index = names.index(probe)
        traces[probe] = [
            (row[time_index], row[probe_index])
            for row in rows
        ]
    return traces


def sample(trace: list[tuple[float, float]], time: float) -> float:
    return min(trace, key=lambda row: abs(row[0] - time))[1]


def check(
    simulator: str,
    traces: dict[str, list[tuple[float, float]]],
    row: int,
    column: int,
    bits: tuple[tuple[bool, bool], tuple[bool, bool]],
) -> int:
    failures = 0

    precharged = [
        sample(traces[f"xbank.bit{c}"], PRECHARGE_SAMPLE)
        for c in range(2)
    ]
    if any(abs(voltage - 2.5) > 0.03 for voltage in precharged):
        failures += 1

    shared = [
        sample(traces[f"xbank.bit{c}"], SENSE_SAMPLE)
        for c in range(2)
    ]
    for c, voltage in enumerate(shared):
        expected = 29 / 11 if bits[row][c] else 25 / 11
        if abs(voltage - expected) > 0.03:
            failures += 1

    sensed = [
        sample(traces[f"xbank.sensed{c}"], SENSE_SAMPLE)
        for c in range(2)
    ]
    for c, voltage in enumerate(sensed):
        if bits[row][c] and voltage < 4.9:
            failures += 1
        if not bits[row][c] and voltage > 0.1:
            failures += 1

    data_out = sample(traces["dout"], SENSE_SAMPLE)
    if bits[row][column] and data_out < 4.9:
        failures += 1
    if not bits[row][column] and data_out > 0.1:
        failures += 1

    final_storage = [
        [
            sample(traces[f"xbank.store{r}{c}"], FINAL_SAMPLE)
            for c in range(2)
        ]
        for r in range(2)
    ]
    for r in range(2):
        for c in range(2):
            tolerance = 0.05 if r == row else 0.005
            if abs(final_storage[r][c] - stored_voltage(bits[r][c])) > tolerance:
                failures += 1

    verdict = "MATCH" if failures == 0 else "MISMATCH"
    print(
        f"{simulator:7} read r{row}c{column}: "
        f"pre=({precharged[0]:.5g},{precharged[1]:.5g}) "
        f"shared=({shared[0]:.5g},{shared[1]:.5g}) "
        f"dout={data_out:.5g} restore="
        f"({final_storage[row][0]:.5g},{final_storage[row][1]:.5g}) "
        f"{verdict}"
    )
    return failures


def check_write(
    simulator: str,
    traces: dict[str, list[tuple[float, float]]],
    row: int,
    column: int,
    value: bool,
    bits: tuple[tuple[bool, bool], tuple[bool, bool]],
) -> int:
    failures = 0
    write_bus = sample(traces["xbank.writebus"], WRITE_FINAL_SAMPLE)
    expected_write = stored_voltage(value)
    if abs(write_bus - (5.0 if value else 0.0)) > 0.05:
        failures += 1

    final_storage = [
        [
            sample(traces[f"xbank.store{r}{c}"], WRITE_FINAL_SAMPLE)
            for c in range(2)
        ]
        for r in range(2)
    ]
    for r in range(2):
        for c in range(2):
            expected = (
                expected_write if (r, c) == (row, column)
                else stored_voltage(bits[r][c])
            )
            tolerance = 0.08 if r == row else 0.005
            if abs(final_storage[r][c] - expected) > tolerance:
                failures += 1

    verdict = "MATCH" if failures == 0 else "MISMATCH"
    print(
        f"{simulator:7} write r{row}c{column}={int(value)}: "
        f"writebus={write_bus:.5g} storage="
        f"({final_storage[0][0]:.5g},{final_storage[0][1]:.5g};"
        f"{final_storage[1][0]:.5g},{final_storage[1][1]:.5g}) "
        f"{verdict}"
    )
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sim", choices=("ngspice", "spectre"), required=True)
    args = parser.parse_args()
    executable = common.executable(args.sim)
    bits = ((True, False), (False, True))
    failures = 0
    with tempfile.TemporaryDirectory(
        prefix=f"leanmodels-dram-bank-{args.sim}-"
    ) as tmp:
        directory = Path(tmp)
        for row, column in ((0, 0), (1, 0)):
            deck, data_path = materialize(
                directory, args.sim, row, column, bits
            )
            traces = (
                run_ngspice(executable, deck, data_path)
                if args.sim == "ngspice"
                else run_spectre(executable, deck, directory)
            )
            failures += check(args.sim, traces, row, column, bits)
        for row, column, value in ((0, 1, True), (1, 1, False)):
            deck, data_path = materialize(
                directory, args.sim, row, column, bits, "write", value
            )
            traces = (
                run_ngspice(executable, deck, data_path)
                if args.sim == "ngspice"
                else run_spectre(executable, deck, directory)
            )
            failures += check_write(
                args.sim, traces, row, column, value, bits
            )
    print(
        f"{args.sim}: 2x2 DRAM bank read/write transient: "
        f"{failures} failed"
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
