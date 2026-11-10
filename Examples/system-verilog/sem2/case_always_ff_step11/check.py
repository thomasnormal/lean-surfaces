#!/usr/bin/env python3
"""Compare E's loaded-case traces with source simulations (no run2 route)."""

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
    process = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
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


def main():
    lean = run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")])
    expected = {tag: [] for tag in ("plain", "order")}
    for line in lean.splitlines():
        if line.startswith("ROW "):
            _, tag, *values = line.split()
            expected[tag].append(values)
    if [len(expected[tag]) for tag in ("plain", "order")] != [8, 7]:
        raise RuntimeError("E did not produce both complete traces:\n" + lean)

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

    for tag, top in [("plain", "case_always_ff_step11"),
                     ("order", "case_always_ff_order_step11")]:
        sources = [str(HERE / (top + ".sv")), str(HERE / (top + "_tb.sv"))]
        for simulator in simulators:
            with tempfile.TemporaryDirectory(prefix="sv-e-case-") as work:
                if simulator == "iverilog":
                    exe = str(Path(work) / "sim")
                    run(["iverilog", "-g2012", "-s", top + "_tb", "-o", exe]
                        + sources, work)
                    output = run(["vvp", exe], work)
                else:
                    output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                  "-top", top + "_tb"] + sources, work)
            actual = []
            for line in output.splitlines():
                if line.startswith("ROW "):
                    fields = line.split()[1:]
                    actual.append([p.split("=", 1)[1] for p in fields if "=" in p]
                                  if tag == "plain" else fields)
            if actual != expected[tag]:
                raise RuntimeError(f"{tag}/{simulator}: E {expected[tag]} != {actual}")
            print(f"{tag}/{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
