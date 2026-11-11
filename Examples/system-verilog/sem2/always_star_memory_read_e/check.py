#!/usr/bin/env python3
"""Compare the source-shaped @* memory read with pinned simulators."""
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
    ["first", "0", "00", "00", "00000000", "xxxxxxxx"],
    ["write2", "1", "10", "00", "10100101", "xxxxxxxx"],
    ["read2", "1", "10", "10", "10100101", "10100101"],
    ["read1", "1", "10", "01", "10100101", "xxxxxxxx"],
    ["write1", "1", "01", "01", "00111100", "00111100"],
    ["read1_after", "1", "01", "01", "00111100", "00111100"],
    ["readx", "1", "01", "xx", "00111100", "xxxxxxxx"],
    ["readz", "1", "01", "zz", "00111100", "xxxxxxxx"],
    ["read3", "1", "01", "11", "00111100", "xxxxxxxx"],
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
    return out, err


def rows(output):
    answer = []
    for line in output.splitlines():
        if not line.startswith("ROW "):
            continue
        fields = line.split()
        answer.append([fields[1]] + [x.split("=", 1)[1] for x in fields[2:]])
    return answer


def source_rows(simulator):
    sources = [str(HERE / "always_star_memory_read_e.sv"),
               str(HERE / "always_star_memory_read_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-always-star-memory-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "always_star_memory_read_e_tb",
                 "-o", exe] + sources, work)
            output, _ = run(["vvp", exe], work)
        else:
            output, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                             "-top", "always_star_memory_read_e_tb"] + sources, work)
    return rows(output)


def main():
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/always_star_memory_read_e/agree.lean"])
    print("E source-shaped @* memory read admission: PASS")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required")
    version, err = run(["iverilog", "-V"])
    print((version + err).splitlines()[0])
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            version, err = run(["xrun", "-version"])
            print((version + err).strip())
            simulators.append("xrun")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result: xrun unavailable")
    for simulator in simulators:
        actual = source_rows(simulator)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: expected {EXPECTED}, got {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH source")


if __name__ == "__main__":
    main()
