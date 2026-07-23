#!/usr/bin/env python3
"""Validate transistor-gate logic levels against ngspice operating points."""

import argparse
import json
import subprocess
import tempfile
from pathlib import Path

import diff_test

ROOT = Path(__file__).resolve().parents[2]
LOW_MAX = 0.5
HIGH_MIN = 4.5
DESIGNS = [
    {
        "name": "and",
        "source": "Examples/spice/and_gate/and_gate.cir",
        "probes": [
            ("out", lambda left, right: bool(left and right)),
            ("nand", lambda left, right: not bool(left and right)),
        ],
    },
    {
        "name": "half-adder",
        "source": "Examples/spice/half_adder/half_adder.cir",
        "probes": [
            ("sum", lambda left, right: bool(left ^ right)),
            ("carry", lambda left, right: bool(left and right)),
        ],
    },
]

RIPPLE_VECTORS = [
    (0, 0, 0),
    (10, 3, 0),
    (15, 1, 0),
    (15, 15, 1),
]


def in_logic_band(voltage, expected):
    return voltage >= HIGH_MIN if expected else voltage <= LOW_MAX


def bit(value, index):
    return bool((value >> index) & 1)


def run_ripple_checks(spice, directory):
    failures = 0
    checks = 0
    for left, right, carry_in in RIPPLE_VECTORS:
        expected = left + right + carry_in
        drives = {
            **{f"va{i}": 5 * bit(left, i) for i in range(4)},
            **{f"vb{i}": 5 * bit(right, i) for i in range(4)},
            "vcin": 5 * carry_in,
        }
        case = {
            "name": f"ripple-{left}-{right}-{carry_in}",
            "source": "Examples/spice/ripple_adder/ripple_adder.cir",
            "drives": drives,
        }
        deck, envelope = diff_test.materialize(case, directory)
        parsed = json.loads(envelope.read_text())
        if parsed["netlist"]["kind"] != "Netlist":
            raise RuntimeError(f"{case['name']}: invalid envelope")
        run = subprocess.run(
            [spice, "-b", str(deck)], cwd=ROOT, check=True,
            capture_output=True, text=True)
        output = run.stdout + run.stderr
        probes = [
            *(f"sum{i}" for i in range(4)),
            "cout",
        ]
        expected_bits = [
            *(bit(expected, i) for i in range(4)),
            bit(expected, 4),
        ]
        for probe, expected_bit in zip(probes, expected_bits):
            voltage = diff_test.parse_ngspice(output, probe)
            ok = in_logic_band(voltage, expected_bit)
            failures += not ok
            checks += 1
            verdict = "MATCH" if ok else "MISMATCH"
            label = f"ripple/{left}+{right}+{carry_in}/{probe}"
            level = "high" if expected_bit else "low"
            print(f"{label:28} {voltage:12.8g}  {level:>8}  {verdict}")
    return checks, failures


def main():
    parser = argparse.ArgumentParser()
    parser.parse_args()
    spice = diff_test.ngspice_path()
    failures = 0
    checks = 0
    print(f"{'design/input/probe':28} {'voltage':>12}  expected  verdict")
    print("-" * 64)
    with tempfile.TemporaryDirectory(prefix="leanmodels-spice-switch-") as tmp:
        directory = Path(tmp)
        for design in DESIGNS:
            for left in (0, 1):
                for right in (0, 1):
                    case = {
                        "name": f"{design['name']}-{left}{right}",
                        "source": design["source"],
                        "drives": {"va": 5 * left, "vb": 5 * right},
                    }
                    deck, envelope = diff_test.materialize(case, directory)
                    parsed = json.loads(envelope.read_text())
                    if parsed["netlist"]["kind"] != "Netlist":
                        raise RuntimeError(f"{case['name']}: invalid envelope")
                    run = subprocess.run(
                        [spice, "-b", str(deck)], cwd=ROOT, check=True,
                        capture_output=True, text=True)
                    output = run.stdout + run.stderr
                    for probe, expected_fn in design["probes"]:
                        voltage = diff_test.parse_ngspice(output, probe)
                        expected = expected_fn(left, right)
                        ok = in_logic_band(voltage, expected)
                        failures += not ok
                        checks += 1
                        verdict = "MATCH" if ok else "MISMATCH"
                        label = f"{design['name']}/{left}{right}/{probe}"
                        level = "high" if expected else "low"
                        print(f"{label:28} {voltage:12.8g}  {level:>8}  {verdict}")
        ripple_checks, ripple_failures = run_ripple_checks(spice, directory)
        checks += ripple_checks
        failures += ripple_failures
    print("-" * 64)
    print(
        f"{checks} checks: {failures} failed "
        f"(low <= {LOW_MAX} V, high >= {HIGH_MIN} V)"
    )
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
