#!/usr/bin/env python3
"""Run Lean modules under the hosted-runner memory budget.

Each module is executed in its own user systemd scope with swap disabled.  The
scope's cgroup ``memory.peak`` is sampled until the command exits, then the
measurement is recorded in ``docs/lean-memory.json``.  A peak over 8 GiB is a
warning; a peak over 12 GiB, or a failed Lean command, fails the gate.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import time
import uuid


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_RECORD = ROOT / "docs" / "lean-memory.json"
WARN_BYTES = 8 * 1024**3
MAX_BYTES = 12 * 1024**3
UNSET = 2**64 - 1


def _show(unit: str, prop: str) -> str:
    result = subprocess.run(
        ["systemctl", "--user", "show", unit, "-p", prop, "--value"],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
    )
    return result.stdout.strip()


def _cgroup_path(unit: str) -> Path | None:
    value = _show(unit, "ControlGroup")
    if not value:
        return None
    path = Path("/sys/fs/cgroup") / value.lstrip("/")
    return path if path.is_dir() else None


def _peak(path: Path | None) -> int:
    if path is None:
        return 0
    try:
        value = int((path / "memory.peak").read_text().strip())
    except (FileNotFoundError, ValueError, OSError):
        return 0
    return 0 if value == UNSET else value


def run_module(module: str) -> dict:
    unit = "lean-memory-gate-" + uuid.uuid4().hex[:12]
    command = [
        "systemd-run", "--user", "--scope", "--unit", unit,
        "-p", "MemoryMax=12G", "-p", "MemorySwapMax=0",
        "env", "LEAN_NUM_THREADS=1", "lake", "env", "lean", module,
    ]
    started = time.time()
    try:
        process = subprocess.Popen(command, cwd=ROOT)
    except OSError as error:
        return {"module": module, "error": str(error), "exit_code": 127}

    cgroup = None
    peak = 0
    while process.poll() is None:
        if cgroup is None:
            cgroup = _cgroup_path(unit + ".scope")
        peak = max(peak, _peak(cgroup))
        time.sleep(0.1)
    peak = max(peak, _peak(cgroup or _cgroup_path(unit + ".scope")))
    process.wait()
    row = {
        "module": module,
        "peak_bytes": peak,
        "peak_gib": round(peak / 1024**3, 3),
        "exit_code": process.returncode,
        "seconds": round(time.time() - started, 3),
        "warning": peak > WARN_BYTES,
        "over_budget": peak > MAX_BYTES,
    }
    if peak > WARN_BYTES:
        print("lean-memory-gate: WARNING %s peaked at %.3f GiB" %
              (module, peak / 1024**3), file=sys.stderr)
    return row


def load_records(path: Path) -> dict:
    if not path.exists():
        return {}
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise SystemExit("lean-memory-gate: cannot read %s: %s" % (path, error))
    return value if isinstance(value, dict) else {}


def write_records(path: Path, records: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(records, indent=2, sort_keys=True) + "\n")


def self_test() -> int:
    if not Path("/run/systemd/system").exists():
        print("lean-memory-gate self-test: systemd unavailable; skipped")
        return 0
    print("lean-memory-gate self-test: systemd scope available")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path, default=DEFAULT_RECORD)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("modules", nargs="*")
    options = parser.parse_args(argv)
    if options.self_test:
        return self_test()
    if not options.modules:
        parser.error("at least one Lean module is required")
    records = load_records(options.record)
    failed = False
    for module in options.modules:
        row = run_module(module)
        records[module] = row
        print(json.dumps(row, sort_keys=True), flush=True)
        failed |= row.get("exit_code", 1) != 0 or row.get("over_budget", False)
    write_records(options.record, records)
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
