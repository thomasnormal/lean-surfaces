#!/usr/bin/env python3
"""Check the loaded-RC transient against its proved analytic trajectory.

Lean proves the continuous DAE trajectory exactly. This harness separately
checks that ngspice's adaptive numerical trace approximates that trajectory;
the floating-point comparison is validation, not a proof premise.
"""

import math
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "Examples/spice/loaded_rc/loaded_rc.cir"


def ngspice_path():
    found = shutil.which("ngspice")
    if found:
        return found
    local = Path.home() / ".local/bin/ngspice"
    if local.exists():
        return str(local)
    raise SystemExit("ngspice not found on PATH or at ~/.local/bin/ngspice")


def transient_deck(directory):
    source = SOURCE.read_text()
    source, count = re.subn(
        r"(?im)^\.op\s*$",
        ".ic v(out)=0\n.tran 10u 5m uic\n.print tran v(out)",
        source,
        count=1,
    )
    if count != 1:
        raise RuntimeError("loaded_rc.cir has no unique .op card")
    deck = directory / "loaded_rc_transient.cir"
    deck.write_text(source)
    return deck


def parse_trace(output):
    rows = []
    pattern = re.compile(
        r"^\s*\d+\s+"
        r"([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[-+]?\d+)?)\s+"
        r"([-+]?(?:\d+(?:\.\d*)?|\.\d+)(?:e[-+]?\d+)?)\s*$",
        re.IGNORECASE,
    )
    for line in output.splitlines():
        match = pattern.match(line)
        if match:
            rows.append((float(match.group(1)), float(match.group(2))))
    if not rows:
        raise RuntimeError("ngspice emitted no transient rows")
    return rows


def analytic(time):
    return (10.0 / 3.0) * (1.0 - math.exp(-1500.0 * time))


def nearest(rows, target):
    return min(rows, key=lambda row: abs(row[0] - target))


def main():
    spice = ngspice_path()
    with tempfile.TemporaryDirectory(prefix="leanmodels-rc-") as tmp:
        deck = transient_deck(Path(tmp))
        run = subprocess.run(
            [spice, "-b", str(deck)],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        rows = parse_trace(run.stdout + run.stderr)

    failures = 0
    previous = -math.inf
    for _, voltage in rows:
        if (voltage + 1e-9 < previous or voltage < -1e-9
                or voltage > 10.0 / 3.0 + 1e-6):
            failures += 1
            break
        previous = voltage

    print(f"{'time':>10} {'Lean analytic':>16} {'ngspice':>16} {'relative error':>16}")
    print("-" * 62)
    for target in (0.0005, 0.001, 0.002, 0.003, 0.005):
        time, voltage = nearest(rows, target)
        expected = analytic(time)
        relative = abs(voltage - expected) / max(abs(expected), 1e-12)
        if relative > 0.006:
            failures += 1
        print(f"{time:10.6g} {expected:16.9g} {voltage:16.9g} {relative:16.3g}")
    print("-" * 62)
    print(f"monotone/bounded and analytic comparison: {failures} failed")
    raise SystemExit(1 if failures else 0)


if __name__ == "__main__":
    main()
