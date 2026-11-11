#!/usr/bin/env python3
"""Compare the source-shaped @* case latch with the pinned simulators."""
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

EXPECTED = {
    # The first sample is an independent time-zero Active-region ordering:
    # Icarus leaves an implicit @* waiter asleep, while Xcelium wakes it
    # after the port connection settles.  The later hold/capture rows agree.
    "iverilog": [
        ["first", "00", "0011", "xxxx"],
        ["invert", "01", "0011", "1100"],
        ["hold_unmatched", "10", "0011", "1100"],
        ["hold_data", "10", "1010", "1100"],
        ["capture", "00", "1010", "1010"],
        ["hold_xz", "xz", "1010", "1010"],
        ["invert_z", "01", "zzzz", "xxxx"],
        ["hold_last", "11", "zzzz", "xxxx"],
    ],
    "xrun": [
        ["first", "00", "0011", "0011"],
        ["invert", "01", "0011", "1100"],
        ["hold_unmatched", "10", "0011", "1100"],
        ["hold_data", "10", "1010", "1100"],
        ["capture", "00", "1010", "1010"],
        ["hold_xz", "xz", "1010", "1010"],
        ["invert_z", "01", "zzzz", "xxxx"],
        ["hold_last", "11", "zzzz", "xxxx"],
    ],
}


def run(args, cwd):
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
    answer = []
    for line in output.splitlines():
        if line.startswith("ROW "):
            fields = line.split()
            answer.append([fields[1]] + [x.split("=", 1)[1] for x in fields[2:]])
    return answer


def source_rows(tool):
    sources = [str(HERE / "always_star_case_latch_e.sv"),
               str(HERE / "always_star_case_latch_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-star-case-latch-e-") as work:
        if tool == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "always_star_case_latch_e_tb",
                 "-o", exe] + sources, work)
            return rows(run(["vvp", exe], work))
        return rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                         "-top", "always_star_case_latch_e_tb"] + sources, work))


def main():
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/always_star_case_latch_e/agree.lean"], ROOT)
    print("E implicit-event case retention: PASS")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required")
    print(run(["iverilog", "-V"], ROOT).splitlines()[0])
    tools = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            print(run(["xrun", "-version"], ROOT).strip())
            tools.append("xrun")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result: xrun unavailable")
    for tool in tools:
        actual = source_rows(tool)
        if actual != EXPECTED[tool]:
            raise RuntimeError(f"{tool}: expected {EXPECTED[tool]}, got {actual}")
        detail = " (first startup row split)" if tool == "iverilog" else ""
        print(f"{tool}: {len(actual)} rows MATCH source{detail}")


if __name__ == "__main__":
    main()
