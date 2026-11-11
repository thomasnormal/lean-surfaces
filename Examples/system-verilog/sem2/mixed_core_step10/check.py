#!/usr/bin/env python3
"""Compare mixed comb/edge source rows between Icarus and gated Xcelium."""

from pathlib import Path
import os
import shutil
import signal
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium  # noqa: E402


def run(args, cwd=ROOT):
    p = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = p.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if p.returncode:
        raise RuntimeError(f"{args[0]} exited {p.returncode}:\n{out}{err}")
    return out


def rows(output):
    result = []
    for line in output.splitlines():
        if line.startswith("ROW "):
            result.append(line.split())
    return result


def main():
    lean = run(["lake", "env", "lean", str(HERE / "agree.lean")])
    if lean.strip():
        print(lean, end="")
    sources = [str(HERE / "mixed_core_step10.sv"),
               str(HERE / "mixed_core_step10_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-step10-mixed-") as work:
        exe = str(Path(work) / "sim")
        run(["iverilog", "-g2012", "-s", "mixed_core_step10_tb", "-o", exe]
            + sources, work)
        iverilog_rows = rows(run(["vvp", exe], work))
    print(f"iverilog: {len(iverilog_rows)} rows")
    if not shutil.which("xrun"):
        print("no Xcelium result: xrun unavailable")
        return
    status, details = probe_xcelium()
    print(details)
    if status == 77:
        print("no Xcelium result: explicit license refusal")
        return
    if status != 0:
        raise RuntimeError("Xcelium readiness probe failed")
    with tempfile.TemporaryDirectory(prefix="sv-step10-mixed-xrun-") as work:
        xrun_rows = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "mixed_core_step10_tb"] + sources, work))
    if xrun_rows != iverilog_rows:
        raise RuntimeError(f"Icarus rows differ from Xcelium:\n{iverilog_rows}\n{xrun_rows}")
    print(f"xrun: {len(xrun_rows)} rows MATCH Icarus")


if __name__ == "__main__":
    main()
