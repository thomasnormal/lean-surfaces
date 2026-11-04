#!/usr/bin/env python3
"""Exercise the concrete 256x32 DRAM bank with ngspice or Spectre.

The committed deck is an open component. This harness supplies one-hot row
and column controls, phase timing, and initial charge in a temporary
testbench. Simulator traces are validation evidence, never Lean premises.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import tempfile

import loaded_inverter_transient_test as common

ROOT = Path(__file__).resolve().parents[2]
SOURCE = (
    ROOT
    / "Examples/spice/dram_bank_256x32/dram_bank_256x32.cir"
)
ROWS = 256
COLUMNS = 32
SUBARRAY_ROWS = 16
PRECHARGE_SAMPLE = 10e-9
CHARGE_SHARE_SAMPLE = 17e-9
SENSE_SAMPLE = 40e-9
READ_FINAL_SAMPLE = 40e-9
WRITE_FINAL_SAMPLE = 70e-9


def stored_voltage(bit: bool) -> float:
    return 4.0 if bit else 0.0


def storage_probe(row: int, column: int) -> str:
    subarray, local_row = divmod(row, SUBARRAY_ROWS)
    return (
        f"xbank.xsub{subarray}.xrow{local_row}.store{column}"
    )


def probes(row: int, column: int) -> tuple[str, ...]:
    adjacent_column = (column + 1) % COLUMNS
    return (
        f"xbank.bit{column}",
        f"xbank.xcolumn{column}.ref",
        f"xbank.xcolumn{column}.q",
        f"xbank.xcolumn{column}.qb",
        "xbank.writebus",
        "dout",
        storage_probe(row, column),
        storage_probe(row, adjacent_column),
        storage_probe(7, 3),
    )


def materialize(
    directory: Path,
    simulator: str,
    row: int,
    column: int,
    stored: bool,
    operation: str,
    write_value: bool = False,
) -> tuple[Path, Path | None, tuple[str, ...]]:
    source = SOURCE.read_text()
    source, count = re.subn(r"(?im)^\.end\s*$", "", source, count=1)
    if count != 1:
        raise RuntimeError("DRAM bank source has no unique .end")
    if operation == "write":
        restore = "pwl(0 0 18n 0 18.1n 5 45n 5 45.1n 0 75n 0)"
        restoreb = "pwl(0 5 18n 5 18.1n 0 45n 0 45.1n 5 75n 5)"
        sense_hi = "pwl(0 2.5 20n 2.5 20.1n 5 45n 5 45.1n 2.5 75n 2.5)"
        sense_lo = "pwl(0 2.5 20n 2.5 20.1n 0 45n 0 45.1n 2.5 75n 2.5)"
        write = "pwl(0 0 47n 0 47.1n 5 75n 5)"
        writeb = "pwl(0 5 47n 5 47.1n 0 75n 0)"
        final_time = "75n"
    else:
        restore = "pwl(0 0 18n 0 18.1n 5 50n 5)"
        restoreb = "pwl(0 5 18n 5 18.1n 0 50n 0)"
        sense_hi = "pwl(0 2.5 20n 2.5 20.1n 5 50n 5)"
        sense_lo = "pwl(0 2.5 20n 2.5 20.1n 0 50n 0)"
        write = "0"
        writeb = "5"
        final_time = "45n"
    testbench = [
        source.rstrip(),
        "vvdd vdd 0 5",
        "vvpre vpre 0 2.5",
        "vprectl precharge 0 pwl(0 5 10n 5 10.1n 0 75n 0)",
        f"vrestore restore 0 {restore}",
        f"vrestoreb restoreb 0 {restoreb}",
        f"vsensehi sensehi 0 {sense_hi}",
        f"vsenselo senselo 0 {sense_lo}",
        f"vwrite write 0 {write}",
        f"vwriteb writeb 0 {writeb}",
        f"vdin din 0 {5 if write_value else 0}",
    ]
    testbench.extend(
        f"vword{index} word{index} 0 "
        + (
            "pwl(0 0 12n 0 12.1n 5 75n 5)"
            if index == row
            else "0"
        )
        for index in range(ROWS)
    )
    for index in range(COLUMNS):
        selected = index == column
        testbench.extend(
            (
                f"vselect{index} select{index} 0 {5 if selected else 0}",
                f"vselectb{index} selectb{index} 0 {0 if selected else 5}",
            )
        )
    adjacent_column = (column + 1) % COLUMNS
    initial_high = [
        storage_probe(row, adjacent_column),
        storage_probe(7, 3),
    ]
    if stored:
        initial_high.append(storage_probe(row, column))
    testbench.extend(
        (
            ".ic " + " ".join(f"v({node})=4" for node in initial_high),
            f".tran 50p {final_time} uic",
        )
    )
    observed = probes(row, column)
    data_path = None
    stem = (
        f"dram_bank_256x32_{operation}_r{row}c{column}_"
        f"{int(stored)}_{int(write_value)}"
    )
    if simulator == "ngspice":
        data_path = directory / f"{stem}.data"
        testbench.extend(
            (
                ".control",
                "run",
                f"wrdata {data_path} "
                + " ".join(f"v({probe})" for probe in observed),
                ".endc",
            )
        )
    testbench.append(".end")
    deck = directory / f"{stem}.cir"
    deck.write_text("\n".join(testbench) + "\n")
    return deck, data_path, observed


def run_ngspice(
    executable: str,
    deck: Path,
    data_path: Path,
    observed: tuple[str, ...],
) -> dict[str, list[tuple[float, float]]]:
    run = subprocess.run(
        [executable, "-b", str(deck)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=300,
    )
    if run.returncode:
        raise RuntimeError(
            f"ngspice failed for {deck.name}:\n{run.stdout}\n{run.stderr}"
        )
    traces = {probe: [] for probe in observed}
    for line in data_path.read_text().splitlines():
        fields = [float(value) for value in line.split()]
        if len(fields) != 2 * len(observed):
            raise RuntimeError(f"unexpected ngspice wrdata row: {line}")
        for index, probe in enumerate(observed):
            traces[probe].append(
                (fields[2 * index], fields[2 * index + 1])
            )
    if not traces[observed[0]]:
        raise RuntimeError("ngspice emitted no DRAM transient rows")
    return traces


def run_spectre(
    executable: str,
    deck: Path,
    directory: Path,
    observed: tuple[str, ...],
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
        timeout=300,
    )
    if run.returncode:
        raise RuntimeError(
            f"Spectre failed for {deck.name}:\n{run.stdout}\n{run.stderr}"
        )
    names, rows = common.parse_nutascii(raw)
    time_index = names.index("time")
    traces = {}
    for probe in observed:
        probe_index = names.index(probe)
        traces[probe] = [
            (row[time_index], row[probe_index])
            for row in rows
        ]
    return traces


def sample(trace: list[tuple[float, float]], time: float) -> float:
    return min(trace, key=lambda row: abs(row[0] - time))[1]


def check_read(
    simulator: str,
    traces: dict[str, list[tuple[float, float]]],
    row: int,
    column: int,
    stored: bool,
) -> int:
    bitline = traces[f"xbank.bit{column}"]
    precharged = sample(bitline, PRECHARGE_SAMPLE)
    shared = sample(bitline, CHARGE_SHARE_SAMPLE)
    reference = sample(
        traces[f"xbank.xcolumn{column}.ref"], CHARGE_SHARE_SAMPLE
    )
    sensed = sample(
        traces[f"xbank.xcolumn{column}.q"], SENSE_SAMPLE
    )
    sensed_bar = sample(
        traces[f"xbank.xcolumn{column}.qb"], SENSE_SAMPLE
    )
    data_out = sample(traces["dout"], SENSE_SAMPLE)
    restored = sample(
        traces[storage_probe(row, column)], READ_FINAL_SAMPLE
    )
    same_row_sentinel = sample(
        traces[storage_probe(row, (column + 1) % COLUMNS)],
        READ_FINAL_SAMPLE,
    )
    sentinel = sample(traces[storage_probe(7, 3)], READ_FINAL_SAMPLE)
    expected_shared = 29 / 11 if stored else 25 / 11
    expected_logic = 5.0 if stored else 0.0
    failures = sum(
        (
            abs(precharged - 2.5) > 0.03,
            abs(shared - expected_shared) > 0.03,
            abs(reference - 2.5) > 0.03,
            abs(sensed - expected_logic) > 0.1,
            abs(sensed_bar - (5.0 - expected_logic)) > 0.1,
            abs(data_out - expected_logic) > 0.1,
            abs(restored - stored_voltage(stored)) > 0.08,
            abs(same_row_sentinel - 4.0) > 0.08,
            abs(sentinel - 4.0) > 0.005,
        )
    )
    verdict = "MATCH" if failures == 0 else "MISMATCH"
    print(
        f"{simulator:7} read r{row}c{column}={int(stored)}: "
        f"pre={precharged:.5g} shared=({shared:.5g},{reference:.5g}) "
        f"sense=({sensed:.5g},{sensed_bar:.5g}) dout={data_out:.5g} "
        f"restore={restored:.5g} "
        f"same-row={same_row_sentinel:.5g} "
        f"hold={sentinel:.5g} {verdict}"
    )
    return failures


def check_write(
    simulator: str,
    traces: dict[str, list[tuple[float, float]]],
    row: int,
    column: int,
    write_value: bool,
) -> int:
    write_bus = sample(traces["xbank.writebus"], WRITE_FINAL_SAMPLE)
    stored = sample(
        traces[storage_probe(row, column)], WRITE_FINAL_SAMPLE
    )
    same_row_sentinel = sample(
        traces[storage_probe(row, (column + 1) % COLUMNS)],
        WRITE_FINAL_SAMPLE,
    )
    sentinel = sample(traces[storage_probe(7, 3)], WRITE_FINAL_SAMPLE)
    expected_bus = 5.0 if write_value else 0.0
    expected_store = stored_voltage(write_value)
    failures = sum(
        (
            abs(write_bus - expected_bus) > 0.08,
            abs(stored - expected_store) > 0.1,
            abs(same_row_sentinel - 4.0) > 0.08,
            abs(sentinel - 4.0) > 0.005,
        )
    )
    verdict = "MATCH" if failures == 0 else "MISMATCH"
    print(
        f"{simulator:7} write r{row}c{column}={int(write_value)}: "
        f"writebus={write_bus:.5g} store={stored:.5g} "
        f"same-row={same_row_sentinel:.5g} "
        f"hold={sentinel:.5g} {verdict}"
    )
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sim", choices=("ngspice", "spectre"), required=True)
    parser.add_argument(
        "--full",
        action="store_true",
        help="exercise both read polarities and both write polarities",
    )
    args = parser.parse_args()
    executable = common.executable(args.sim)
    cases = [
        ("read", 173, 17, True, False),
        ("write", 45, 3, True, False),
    ]
    if args.full:
        cases.extend(
            (
                ("read", 45, 3, False, False),
                ("write", 173, 17, False, True),
            )
        )
    failures = 0
    with tempfile.TemporaryDirectory(
        prefix=f"leanmodels-dram-bank-256x32-{args.sim}-"
    ) as temporary:
        directory = Path(temporary)
        for operation, row, column, stored, write_value in cases:
            deck, data_path, observed = materialize(
                directory,
                args.sim,
                row,
                column,
                stored,
                operation,
                write_value,
            )
            traces = (
                run_ngspice(
                    executable, deck, data_path, observed
                )
                if args.sim == "ngspice"
                else run_spectre(
                    executable, deck, directory, observed
                )
            )
            failures += (
                check_read(args.sim, traces, row, column, stored)
                if operation == "read"
                else check_write(
                    args.sim, traces, row, column, write_value
                )
            )
    print(
        f"{args.sim}: 256x32 DRAM bank read/write transient: "
        f"{failures} failed"
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
