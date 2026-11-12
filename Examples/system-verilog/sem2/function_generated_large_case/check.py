#!/usr/bin/env python3
"""Run the source-shaped function wall in E and against both simulators."""

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
    ("00000000000000000000000000000000000000000000000000000000000000000",
     "11111111111111111111111111111111111111111111111111111111111111111"),
    ("00000000000000000000000000000000000000000000000000000000000000001",
     "11111111111111111111111111111111111111111111111111111111111111110"),
    ("11111111111111111111111111111111111111111111111111111111111111111",
     "00000000000000000000000000000000000000000000000000000000000000000"),
]


def run(args, cwd=ROOT):
    proc = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
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


def e_rows():
    output = run([
        "lake", "env", "lean", "--run", "harness/sv/runner_e0.lean",
        str(HERE / "function_generated_large_case.sv.json"),
        "harness/sv/cases2.json", "function_generated_large_case_e", "src",
    ])
    rows = []
    for line in output.splitlines():
        if line.startswith("CYCLE "):
            fields = line.split()[2:]
            rows.append(tuple(field.split("=", 1)[1] for field in fields))
    if rows != EXPECTED:
        raise RuntimeError(f"E rows differ:\nexpected {EXPECTED}\nactual {rows}\n{output}")
    return rows


def check_envelope():
    with tempfile.TemporaryDirectory(prefix="sv-function-envelope-") as work:
        output = Path(work) / "function_generated_large_case.sv.json"
        run([
            sys.executable, str(ROOT / "extractors/sv/extract.py"),
            "--top", "function_generated_large_case", "--retain-proc-rewrites",
            "-o", str(output),
            str((HERE / "function_generated_large_case.sv").relative_to(ROOT)),
        ])
        recorded = HERE / "function_generated_large_case.sv.json"
        if output.read_bytes() != recorded.read_bytes():
            raise RuntimeError("source-shaped function envelope is not reproducible")
    print("extractor: source-shaped function envelope regenerates byte-identically")


def source_rows(simulator):
    sources = [str(HERE / "function_generated_large_case.sv"),
               str(HERE / "function_generated_large_case_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-function-large-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "function_generated_large_case_tb",
                 "-o", exe] + sources, work)
            output = run(["vvp", exe], work)
        else:
            output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                          "-top", "function_generated_large_case_tb"] + sources, work)
    rows = []
    for line in output.splitlines():
        if line.startswith("ROW "):
            fields = line.split()[2:]
            rows.append(tuple(field.split("=", 1)[1] for field in fields))
    return rows


def main():
    check_envelope()
    expected = e_rows()
    print(f"E: {len(expected)} rows MATCH")
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
        if actual != expected:
            raise RuntimeError(f"{simulator}: expected {expected}, got {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
