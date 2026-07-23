#!/usr/bin/env python3
"""Validate transistor-gate logic levels against ngspice operating points."""

import argparse
import json
import subprocess
import tempfile
from pathlib import Path

import diff_test

ROOT = Path(__file__).resolve().parents[2]
SOURCE = "Examples/spice/and_gate/and_gate.cir"
LOW_MAX = 0.5
HIGH_MIN = 4.5


def in_logic_band(voltage, expected):
    return voltage >= HIGH_MIN if expected else voltage <= LOW_MAX


def main():
    parser = argparse.ArgumentParser()
    parser.parse_args()
    spice = diff_test.ngspice_path()
    failures = 0
    print(f"{'inputs':8} {'out':>12} {'nand':>12}  verdict")
    print("-" * 46)
    with tempfile.TemporaryDirectory(prefix="leanmodels-spice-switch-") as tmp:
        directory = Path(tmp)
        for left in (0, 1):
            for right in (0, 1):
                case = {
                    "name": f"and-{left}{right}",
                    "source": SOURCE,
                    "drives": {"va": 5 * left, "vb": 5 * right},
                }
                deck, envelope = diff_test.materialize(case, directory)
                parsed = json.loads(envelope.read_text())
                kinds = [card["kind"] for card in parsed["netlist"]["cards"]]
                if "Unsupported" in kinds:
                    raise RuntimeError(f"{case['name']}: extractor lost a MOS card")
                run = subprocess.run(
                    [spice, "-b", str(deck)], cwd=ROOT, check=True,
                    capture_output=True, text=True)
                output = run.stdout + run.stderr
                out_voltage = diff_test.parse_ngspice(output, "out")
                nand_voltage = diff_test.parse_ngspice(output, "nand")
                expected = bool(left and right)
                ok = (
                    in_logic_band(out_voltage, expected)
                    and in_logic_band(nand_voltage, not expected)
                )
                failures += not ok
                verdict = "MATCH" if ok else "MISMATCH"
                print(
                    f"{left}{right:1} {out_voltage:12.8g} "
                    f"{nand_voltage:12.8g}  {verdict}"
                )
    print("-" * 46)
    print(
        f"4 vectors: {failures} failed "
        f"(low <= {LOW_MAX} V, high >= {HIGH_MIN} V)"
    )
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
