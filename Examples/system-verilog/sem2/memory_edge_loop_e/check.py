#!/usr/bin/env python3
"""Compare the E edge-loop memory trace with Icarus and gated Xcelium."""

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
    proc = subprocess.Popen(args, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    try:
        out, err = proc.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out


def rows(output):
    return [line.split()[1:] for line in output.splitlines()
            if line.startswith("ROW ")]


def main():
    lean = run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")])
    expected = rows(lean)
    if len(expected) != 9:
        raise RuntimeError(f"E produced {len(expected)} rows:\n{lean}")
    print("E: 9 rows (initial, reset, x/z clock/reset/data cases)")

    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            simulators.append("xrun")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result: xrun unavailable")

    sources = [str(HERE / "memory_edge_loop_e.sv"),
               str(HERE / "memory_edge_loop_e_tb.sv")]
    for simulator in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-e-memory-loop-") as work:
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "memory_edge_loop_e_tb",
                     "-o", exe] + sources, work)
                actual = rows(run(["vvp", exe], work))
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "memory_edge_loop_e_tb"] + sources, work))
        if actual != expected:
            raise RuntimeError(f"{simulator}: E {expected} != source {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
