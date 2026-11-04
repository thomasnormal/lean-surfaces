#!/usr/bin/env python3
"""Compare the direct Lean SPICE frontend with ngspice listings."""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
import pathlib
import re
import shutil
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
RUNNER = ROOT / "LeanModels/Circuit/ParserRunner.lean"
DECKS = (
    ROOT / "Examples/spice/typed_divider/typed_divider.cir",
    ROOT / "Examples/spice/robust_divider/robust_divider.cir",
    ROOT / "Examples/spice/loaded_rc/loaded_rc.cir",
    ROOT / "Examples/spice/rlc_discharge/rlc_discharge.cir",
    ROOT / "Examples/spice/gnd_alias/gnd_alias.cir",
)


@dataclass(frozen=True)
class Device:
    kind: str
    name: str
    positive: str
    negative: str
    value: Fraction


def exact_value(token: str) -> Fraction:
    token = token.lower()
    suffixes = {
        "meg": Fraction(1_000_000),
        "k": Fraction(1_000),
        "m": Fraction(1, 1_000),
        "u": Fraction(1, 1_000_000),
        "n": Fraction(1, 1_000_000_000),
        "p": Fraction(1, 1_000_000_000_000),
        "f": Fraction(1, 1_000_000_000_000_000),
    }
    multiplier = Fraction(1)
    for suffix in sorted(suffixes, key=len, reverse=True):
        if token.endswith(suffix):
            token = token[: -len(suffix)]
            multiplier = suffixes[suffix]
            break
    return Fraction(Decimal(token)) * multiplier


def lean_topology(deck: pathlib.Path) -> tuple[list[str], list[Device]]:
    result = subprocess.run(
        ["lake", "env", "lean", "--run", str(RUNNER), str(deck)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    nodes: list[str] = []
    raw_devices: list[tuple[str, str, int, int, Fraction]] = []
    for line in result.stdout.splitlines():
        fields = line.split()
        if fields[:1] == ["node"]:
            index = int(fields[1])
            assert index == len(nodes), line
            nodes.append(fields[2])
        elif fields[:1] == ["device"]:
            raw_devices.append(
                (
                    fields[1],
                    fields[2],
                    int(fields[3]),
                    int(fields[4]),
                    Fraction(fields[5]),
                )
            )
    devices = [
        Device(kind, name, nodes[positive], nodes[negative], value)
        for kind, name, positive, negative, value in raw_devices
    ]
    return nodes, devices


def ngspice_binary() -> str:
    found = shutil.which("ngspice")
    if found is not None:
        return found
    candidate = pathlib.Path.home() / ".local/bin/ngspice"
    if candidate.exists():
        return str(candidate)
    raise RuntimeError("ngspice not found")


def ngspice_topology(deck: pathlib.Path) -> tuple[set[str], list[Device]]:
    source = deck.read_text()
    control = ".control\nlisting\nquit\n.endc\n.end"
    source = re.sub(r"(?im)^\.end\s*$", control, source)
    with tempfile.TemporaryDirectory(prefix="leanmodels-spice-parser-") as tmp:
        listing_deck = pathlib.Path(tmp) / "listing.cir"
        listing_deck.write_text(source)
        result = subprocess.run(
            [ngspice_binary(), "-b", str(listing_deck)],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=True,
        )

    devices: list[Device] = []
    nodes: set[str] = {"0"}
    listing = re.compile(
        r"^\s*(\d+)\s*:\s*([rvcl])(\S*)\s+(\S+)\s+(\S+)\s+"
        r"(?:(dc)\s+)?(\S+)",
        re.IGNORECASE,
    )
    for line in result.stdout.splitlines():
        match = listing.match(line)
        if match is None:
            continue
        line_number, prefix, tail, positive, negative, _dc, value = (
            match.groups()
        )
        if line_number == "1":
            continue
        kind = {
            "r": "resistor",
            "v": "voltageSource",
            "c": "capacitor",
            "l": "inductor",
        }[prefix.lower()]
        name = (prefix + tail).lower()
        positive = positive.lower()
        negative = negative.lower()
        devices.append(
            Device(kind, name, positive, negative, exact_value(value))
        )
        nodes.update((positive, negative))
    return nodes, devices


def assert_agreement(deck: pathlib.Path) -> None:
    nodes, lean_devices = lean_topology(deck)
    ng_nodes, ng_devices = ngspice_topology(deck)
    if set(nodes) != ng_nodes:
        raise AssertionError(
            f"{deck}: node disagreement: Lean={nodes}, ngspice={ng_nodes}"
        )
    if lean_devices != ng_devices:
        raise AssertionError(
            f"{deck}: device disagreement:\n"
            f"  Lean={lean_devices}\n  ngspice={ng_devices}"
        )


def assert_lean_rejects(source: str, expected: str) -> None:
    with tempfile.TemporaryDirectory(prefix="leanmodels-spice-reject-") as tmp:
        deck = pathlib.Path(tmp) / "reject.cir"
        deck.write_text(source)
        result = subprocess.run(
            ["lake", "env", "lean", "--run", str(RUNNER), str(deck)],
            cwd=ROOT,
            text=True,
            capture_output=True,
        )
    if result.returncode == 0 or expected not in result.stderr:
        raise AssertionError(
            f"Lean frontend did not reject with {expected!r}:\n"
            f"stdout={result.stdout}\nstderr={result.stderr}"
        )


def main() -> int:
    checked = list(DECKS)
    with tempfile.TemporaryDirectory(prefix="leanmodels-spice-accept-") as tmp:
        scientific = pathlib.Path(tmp) / "scientific.cir"
        scientific.write_text(
            "scientific notation\n"
            "V1 in 0 DC 5e0\n"
            "R1 in out 1e3\n"
            "R2 out 0 2e3\n"
            ".op\n.end\n"
        )
        assert_agreement(scientific)
    for deck in checked:
        assert_agreement(deck)

    assert_lean_rejects(
        "missing ground\nV1 in ref DC 5\nR1 in out 1k\n.end\n",
        "no ground",
    )
    assert_lean_rejects(
        "duplicate\nV1 in 0 DC 5\nV1 out 0 DC 2\n.end\n",
        "duplicate device",
    )
    assert_lean_rejects(
        "invalid inductor\nL1 in 0 0\n.end\n",
        "positive",
    )

    print("parser-agreement: PASS")
    print(
        "  accepted: typed divider, robust divider, loaded RC, RLC, "
        "scientific notation, gnd-alias ground"
    )
    print("  compared: node names, device kind/name/orientation, exact values")
    print("  rejected: missing ground, duplicate device, invalid inductor")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
