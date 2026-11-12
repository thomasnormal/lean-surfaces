#!/usr/bin/env python3
"""Compare canonical-E source-shaped memory rows with Icarus and Xcelium."""

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
    if len(expected) != 12:
        raise RuntimeError(f"E produced {len(expected)} rows:\n{lean}")
    print("E: 12 rows (W=4,P=3 and W=8,P=5)")

    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
    print(run(["iverilog", "-V"]).splitlines()[0])
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            print(run(["xrun", "-version"]).strip())
            simulators.append("xrun")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result: xrun unavailable")

    for simulator in simulators:
        actual = []
        for width, depth in ((4, 3), (8, 5)):
            sources = [str(HERE / "memory_shape_a_e.sv"),
                       str(HERE / "memory_shape_a_e_tb.sv")]
            with tempfile.TemporaryDirectory(prefix="sv-e-memory-shape-") as work:
                if simulator == "iverilog":
                    exe = str(Path(work) / "sim")
                    run(["iverilog", "-g2012", "-s", "memory_shape_a_e_tb",
                         "-D", f"WIDTH={width}", "-D", f"DEPTH={depth}",
                         "-o", exe] + sources, work)
                    output = run(["vvp", exe], work)
                else:
                    output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                  "-top", "memory_shape_a_e_tb",
                                  "-define", f"WIDTH={width}",
                                  "-define", f"DEPTH={depth}"] + sources,
                                 work)
            actual.extend(rows(output))
        if actual != expected:
            raise RuntimeError(f"{simulator}: E {expected} != source {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
