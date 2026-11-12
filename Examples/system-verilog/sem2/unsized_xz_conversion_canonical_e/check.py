#!/usr/bin/env python3
"""Compare canonical E's unsized x/z conversion row with both simulators."""
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

EXPECTED = [[
    "values",
    "x" * 40,
    "z" * 40,
    "x" * 36 + "0000",
    "z" * 36 + "0001",
    "x" * 8,
    "z" * 8,
    "xxxx0000",
    "zzzz0001",
]]


def run(args, cwd=ROOT):
    process = subprocess.Popen(
        args, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n" + stdout + stderr)
    if process.returncode:
        raise RuntimeError(f"{args[0]} exited {process.returncode}:\n" + stdout + stderr)
    return stdout


def rows(output):
    answer = []
    for line in output.splitlines():
        if not line.startswith("ROW "):
            continue
        fields = line.split()
        answer.append([fields[1]] + [field.split("=", 1)[1]
                                     for field in fields[2:]])
    return answer


def source_rows(simulator):
    sources = [
        str(HERE / "unsized_xz_conversion_canonical_e.sv"),
        str(HERE / "unsized_xz_conversion_canonical_e_tb.sv"),
    ]
    with tempfile.TemporaryDirectory(prefix="sv-unsized-xz-canonical-e-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s",
                 "unsized_xz_conversion_canonical_e_tb", "-o", exe] + sources,
                work)
            output = run(["vvp", exe], work)
        else:
            output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                          "-top", "unsized_xz_conversion_canonical_e_tb"] + sources,
                         work)
    return rows(output)


def main():
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/unsized_xz_conversion_canonical_e/agree.lean"])
    print("canonical E parser marker and width guards: PASS")
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
        actual = source_rows(simulator)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: expected {EXPECTED}, got {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
