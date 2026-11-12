#!/usr/bin/env python3
"""Check the two S0.b MemE boundary rows against pinned simulators."""

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

EXPECTED = [["first", "12", "xx"], ["second", "a5", "xx"]]


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
        if line.startswith("ROW "):
            fields = line.split()
            answer.append([fields[1]] + [x.split("=", 1)[1]
                                         for x in fields[2:]])
    return answer


def source_rows(simulator, name):
    sources = [str(ROOT / "Examples/system-verilog/sem2" / name / f"{name}.sv"),
               str(ROOT / "Examples/system-verilog/sem2" / name / f"{name}_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-meme-boundary-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", f"{name}_tb", "-o", exe] + sources,
                work)
            output, _ = run(["vvp", exe], work)
        else:
            output, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                             "-top", f"{name}_tb"] + sources, work)
    return rows(output)


def main():
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/mem_order_e/agree.lean"])
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/mem_always_comb_e/agree.lean"])
    print("MemE boundary receipts: PASS")
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
        for name in ("mem_order_e", "mem_always_comb_e"):
            actual = source_rows(simulator, name)
            if actual != EXPECTED:
                raise RuntimeError(f"{simulator} {name}: expected {EXPECTED}, got {actual}")
            print(f"{simulator} {name}: {len(actual)} rows MATCH source")


if __name__ == "__main__":
    main()
