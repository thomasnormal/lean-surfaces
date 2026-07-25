#!/usr/bin/env python3
"""Compare the typed exact DC semantics with Cadence Spectre.

Spectre is an untrusted differential oracle. The Lean theorem does not depend
on this floating-point comparison, and agreement does not establish physical
model validity.
"""

from __future__ import annotations

from fractions import Fraction
import math
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

import diff_test

ROOT = Path(__file__).resolve().parents[2]
RUNNER = ROOT / "LeanModels/Circuit/DCRunner.lean"
LOW_MAX = 0.5
HIGH_MIN = 4.5
RIPPLE_WIDTH = 50
RIPPLE_VECTORS = (
    (0, 0, 0),
    ((1 << 49) + 10, (1 << 48) + 3, 0),
    ((1 << 50) - 1, 1, 0),
    ((1 << 50) - 1, (1 << 50) - 1, 1),
)
LOGIC_DESIGNS = (
    (
        "and",
        "Examples/spice/and_gate/and_gate.cir",
        (
            ("out", lambda left, right: bool(left and right)),
            ("nand", lambda left, right: not bool(left and right)),
        ),
    ),
    (
        "half-adder",
        "Examples/spice/half_adder/half_adder.cir",
        (
            ("sum", lambda left, right: bool(left ^ right)),
            ("carry", lambda left, right: bool(left and right)),
        ),
    ),
)
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


def spectre_path() -> str:
    found = shutil.which("spectre")
    if found is None:
        raise SystemExit("spectre not found on PATH")
    return found


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


def parse_nutascii(path: Path) -> tuple[list[str], list[list[float]]]:
    text = path.read_text()
    header, values_text = text.split("Values:", maxsplit=1)
    variables_match = re.search(
        r"No\. Variables:\s*(\d+).*?Variables:(.*)",
        header,
        re.DOTALL,
    )
    if variables_match is None:
        raise RuntimeError("Spectre output has no variable table")
    count = int(variables_match.group(1))
    names: list[str] = []
    for line in variables_match.group(2).splitlines():
        fields = line.split()
        if len(fields) >= 2 and fields[0].isdigit():
            names.append(fields[1].lower())
    if len(names) != count:
        raise RuntimeError(
            f"Spectre declared {count} variables but listed {len(names)}"
        )
    tokens = values_text.split()
    stride = count + 1
    if not tokens or len(tokens) % stride != 0:
        raise RuntimeError("Spectre result records are truncated")
    rows: list[list[float]] = []
    for offset in range(0, len(tokens), stride):
        point = int(tokens[offset])
        if point != len(rows):
            raise RuntimeError(f"unexpected Spectre point index {point}")
        rows.append(
            [float(token) for token in tokens[offset + 1 : offset + stride]]
        )
    return names, rows


def spectre_values(
    executable: str, deck: Path, directory: Path
) -> dict[str, float]:
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
    if run.returncode != 0:
        raise RuntimeError(
            f"Spectre failed for {deck}:\n{run.stdout}\n{run.stderr}"
        )
    names, rows = parse_nutascii(raw)
    if len(rows) != 1:
        raise RuntimeError(f"expected one DC point, found {len(rows)}")
    return dict(zip(names, rows[0]))


def in_logic_band(voltage: float, expected: bool) -> bool:
    return voltage >= HIGH_MIN if expected else voltage <= LOW_MAX


def bit(value: int, index: int) -> bool:
    return bool((value >> index) & 1)


def check_logic_components(executable: str, directory: Path) -> tuple[int, int]:
    checks = 0
    failures = 0
    print()
    print(f"{'logic case/probe':30} {'Spectre':>16} {'expected':>10}  verdict")
    print("-" * 76)
    for design, source, probes in LOGIC_DESIGNS:
        for left in (0, 1):
            for right in (0, 1):
                case = {
                    "name": f"spectre-{design}-{left}{right}",
                    "source": source,
                    "inject_drives": {
                        "vddsrc": ("vdd", 5),
                        "va": ("a", 5 * left),
                        "vb": ("b", 5 * right),
                    },
                }
                deck = diff_test.materialize(case, directory)
                values = spectre_values(executable, deck, directory)
                for probe, expected_fn in probes:
                    expected = expected_fn(left, right)
                    voltage = values[probe]
                    ok = in_logic_band(voltage, expected)
                    checks += 1
                    failures += not ok
                    verdict = "MATCH" if ok else "MISMATCH"
                    level = "high" if expected else "low"
                    label = f"{design}/{left}{right}/{probe}"
                    print(
                        f"{label:30} {voltage:16.9g} "
                        f"{level:>10}  {verdict}"
                    )
    return checks, failures


def check_ripple(executable: str, directory: Path) -> tuple[int, int]:
    checks = 0
    failures = 0
    print()
    print(f"{'ripple vector':30} {'checked outputs':>16}  verdict")
    print("-" * 58)
    for left, right, carry_in in RIPPLE_VECTORS:
        expected = left + right + carry_in
        case = {
            "name": f"spectre-ripple-{left}-{right}-{carry_in}",
            "source": "Examples/spice/ripple_adder/ripple_adder.cir",
            "inject_drives": {
                "vddsrc": ("vdd", 5),
                **{
                    f"va{index}": (f"a{index}", 5 * bit(left, index))
                    for index in range(RIPPLE_WIDTH)
                },
                **{
                    f"vb{index}": (f"b{index}", 5 * bit(right, index))
                    for index in range(RIPPLE_WIDTH)
                },
                "vcin": ("cin", 5 * carry_in),
            },
        }
        deck = diff_test.materialize(case, directory)
        values = spectre_values(executable, deck, directory)
        probes = (
            *(f"sum{index}" for index in range(RIPPLE_WIDTH)),
            "cout",
        )
        expected_bits = (
            *(bit(expected, index) for index in range(RIPPLE_WIDTH)),
            bit(expected, RIPPLE_WIDTH),
        )
        vector_ok = True
        for probe, expected_bit in zip(probes, expected_bits):
            ok = in_logic_band(values[probe], expected_bit)
            checks += 1
            failures += not ok
            vector_ok = vector_ok and ok
        verdict = "MATCH" if vector_ok else "MISMATCH"
        print(
            f"{left}+{right}+{carry_in:<8} "
            f"{len(probes):16}  {verdict}"
        )
    return checks, failures


def transient_deck(directory: Path) -> Path:
    source = (
        ROOT / "Examples/spice/loaded_rc/loaded_rc.cir"
    ).read_text()
    source, count = re.subn(
        r"(?im)^\.op\s*$",
        ".ic v(out)=0\n.tran 10u 5m uic\n.print tran v(out)",
        source,
        count=1,
    )
    if count != 1:
        raise RuntimeError("loaded_rc.cir has no unique .op card")
    deck = directory / "loaded_rc_spectre_transient.cir"
    deck.write_text(source)
    return deck


def spectre_transient(
    executable: str, directory: Path
) -> list[tuple[float, float]]:
    deck = transient_deck(directory)
    raw = directory / "loaded_rc_spectre_transient.raw"
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
    if run.returncode != 0:
        raise RuntimeError(
            f"Spectre transient failed:\n{run.stdout}\n{run.stderr}"
        )
    names, rows = parse_nutascii(raw)
    try:
        time_index = names.index("time")
        output_index = names.index("out")
    except ValueError as error:
        raise RuntimeError(
            f"Spectre transient variables do not include time/out: {names}"
        ) from error
    return [(row[time_index], row[output_index]) for row in rows]


def analytic_loaded_rc(time: float) -> float:
    return (10.0 / 3.0) * (1.0 - math.exp(-1500.0 * time))


def check_transient(rows: list[tuple[float, float]]) -> int:
    failures = 0
    previous = -math.inf
    for _, voltage in rows:
        if (
            voltage + 1e-9 < previous
            or voltage < -1e-9
            or voltage > 10.0 / 3.0 + 1e-6
        ):
            failures += 1
            break
        previous = voltage
    print()
    print(
        f"{'time':>10} {'Lean analytic':>16} "
        f"{'Spectre':>16} {'relative error':>16}"
    )
    print("-" * 62)
    for target in (0.0005, 0.001, 0.002, 0.003, 0.005):
        time, voltage = min(rows, key=lambda row: abs(row[0] - target))
        expected = analytic_loaded_rc(time)
        relative = abs(voltage - expected) / max(abs(expected), 1e-12)
        if relative > 0.006:
            failures += 1
        print(
            f"{time:10.6g} {expected:16.9g} "
            f"{voltage:16.9g} {relative:16.3g}"
        )
    print("-" * 62)
    return failures


def rlc_transient_deck(directory: Path) -> Path:
    source = (
        ROOT / "Examples/spice/rlc_discharge/rlc_discharge.cir"
    ).read_text()
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
    deck = directory / "rlc_spectre_transient.cir"
    deck.write_text(source)
    return deck


def spectre_rlc_transient(
    executable: str, directory: Path
) -> list[tuple[float, float, float, float]]:
    deck = rlc_transient_deck(directory)
    raw = directory / "rlc_spectre_transient.raw"
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
    if run.returncode != 0:
        raise RuntimeError(
            f"Spectre RLC transient failed:\n{run.stdout}\n{run.stderr}"
        )
    names, rows = parse_nutascii(raw)
    try:
        time_index = names.index("time")
        storage_index = names.index("n1")
        load_index = names.index("n2")
        current_index = names.index("lpath:1")
    except ValueError as error:
        raise RuntimeError(
            f"Spectre RLC variables are incomplete: {names}"
        ) from error
    return [
        (
            row[time_index],
            row[storage_index],
            row[load_index],
            row[current_index],
        )
        for row in rows
    ]


def analytic_rlc(time: float) -> tuple[float, float, float]:
    decay = math.exp(-1_000_000.0 * time)
    storage = 5.0 * (1.0 + 1_000_000.0 * time) * decay
    current = 5_000_000.0 * time * decay
    return storage, 2.0 * current, current


def check_rlc_transient(
    rows: list[tuple[float, float, float, float]]
) -> int:
    failures = 0
    previous_energy = math.inf
    for _, storage, _load, current in rows:
        energy = 0.5e-6 * (storage * storage + current * current)
        if energy > previous_energy + 1e-10:
            failures += 1
            break
        previous_energy = energy
    print()
    print(
        f"{'time':>10} {'Lean n1':>13} {'Spectre n1':>13} "
        f"{'Lean n2':>13} {'Spectre n2':>13}"
    )
    print("-" * 68)
    for target in (0.2e-6, 0.5e-6, 1e-6, 2e-6, 5e-6):
        time, storage, load, _current = min(
            rows, key=lambda row: abs(row[0] - target)
        )
        expected_storage, expected_load, _ = analytic_rlc(time)
        storage_relative = abs(storage - expected_storage) / max(
            abs(expected_storage), 1e-12
        )
        load_relative = abs(load - expected_load) / max(
            abs(expected_load), 1e-12
        )
        if max(storage_relative, load_relative) > 0.01:
            failures += 1
        print(
            f"{time:10.3g} {expected_storage:13.7g} {storage:13.7g} "
            f"{expected_load:13.7g} {load:13.7g}"
        )
    print("-" * 68)
    return failures


def main() -> int:
    executable = spectre_path()
    failures = 0
    print(f"{'case/probe':30} {'Lean exact':>16} {'Spectre':>16}  verdict")
    print("-" * 76)
    with tempfile.TemporaryDirectory(prefix="leanmodels-spectre-") as tmp:
        directory = Path(tmp)
        for deck, probes in CASES:
            exact = lean_values(deck, probes)
            approximate = spectre_values(executable, deck, directory)
            for probe in probes:
                observed = approximate[probe.lower()]
                ok = math.isclose(
                    float(exact[probe]), observed, rel_tol=1e-9, abs_tol=1e-12
                )
                failures += not ok
                verdict = "MATCH" if ok else "MISMATCH"
                label = f"{deck.parent.name}/{probe}"
                print(
                    f"{label:30} {str(exact[probe]):>16} "
                    f"{observed:16.9g}  {verdict}"
                )
        transient_failures = check_transient(
            spectre_transient(executable, directory)
        )
        failures += transient_failures
        failures += check_rlc_transient(
            spectre_rlc_transient(executable, directory)
        )
        logic_checks, logic_failures = check_logic_components(
            executable, directory
        )
        failures += logic_failures
        ripple_checks, ripple_failures = check_ripple(executable, directory)
        failures += ripple_failures
    print("-" * 76)
    print(
        f"{len(CASES)} DC decks, loaded-RC/RLC transients, "
        f"{logic_checks} gate checks, and {ripple_checks} ripple outputs: "
        f"{failures} failed"
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
