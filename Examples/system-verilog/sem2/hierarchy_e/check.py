#!/usr/bin/env python3
"""Compare canonical E hierarchy rows with Icarus and gated Xcelium."""
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

EXPECTED = [
    ["0", "y=00000000"],
    ["1", "y=00000001"],
    ["2", "y=10100101"],
    ["3", "y=11110000"],
    ["4", "y=xxxxxxxx"],
]


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


def source_rows(tool):
    sources = [str(HERE / "hierarchy_parameterized.sv"),
               str(HERE / "hierarchy_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-hierarchy-") as work:
        if tool == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "hierarchy_e_tb",
                 "-o", exe] + sources, work)
            return rows(run(["vvp", exe], work))
        return rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                         "-top", "hierarchy_e_tb"] + sources, work))


def main():
    agree_olean = ROOT / ".lake/build/lib/lean/Examples/system-verilog/sem2/hierarchy_e/agree.olean"
    agree_olean.parent.mkdir(parents=True, exist_ok=True)
    run(["lake", "env", "lean", "-o", str(agree_olean), str(HERE / "agree.lean")])
    expected = rows(run(["lake", "env", "lean", "--run",
                         str(HERE / "oracle.lean")]))
    if expected != EXPECTED:
        raise RuntimeError(f"E rows differ: {expected}")
    print("E: 5 hierarchy rows")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required")
    print(run(["iverilog", "-V"]).splitlines()[0])
    tools = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            print(run(["xrun", "-version"]).strip())
            tools.append("xrun")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result: xrun unavailable")
    for tool in tools:
        actual = source_rows(tool)
        if actual != EXPECTED:
            raise RuntimeError(f"{tool}: expected {EXPECTED}, got {actual}")
        print(f"{tool}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
