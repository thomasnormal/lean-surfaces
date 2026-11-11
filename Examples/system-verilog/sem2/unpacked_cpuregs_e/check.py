#!/usr/bin/env python3
"""Differential rows for the source-shaped E register-file memory profile."""
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

X32 = "x" * 32
A5 = f"{0xa5:032b}"
Z5 = f"{0x5a:032b}"
EXPECTED = [
    ["before", X32],
    ["write3", X32],
    ["read3", A5],
    ["xread", X32],
    ["zread", X32],
    ["xwrite", A5],
    ["afterxwrite", A5],
    ["write7", A5],
    ["xwe_noedge", Z5],
    ["xwe_edge", Z5],
    ["afterxwe", Z5],
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
        answer.append([fields[1], fields[2].split("=", 1)[1]])
    return answer


def source_rows(simulator):
    sources = [str(HERE / "unpacked_cpuregs_e.sv"),
               str(HERE / "unpacked_cpuregs_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-unpacked-cpuregs-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "unpacked_cpuregs_e_tb",
                 "-o", exe] + sources, work)
            output, _ = run(["vvp", exe], work)
        else:
            output, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                             "-top", "unpacked_cpuregs_e_tb"] + sources, work)
    return rows(output)


def main():
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/unpacked_cpuregs_e/agree.lean"])
    print("E native one-rank memory and runtime-index guards: PASS")

    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
    iverilog_version, iverilog_err = run(["iverilog", "-V"])
    print((iverilog_version + iverilog_err).splitlines()[0])
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
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
