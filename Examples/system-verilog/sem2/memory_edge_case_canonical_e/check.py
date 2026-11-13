#!/usr/bin/env python3
"""Check the canonical-E edge case receipt against both simulators."""

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
        os.killpg(proc.pid, signal.SIGKILL)
        out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out, err


def rows(output):
    return [line.split()[1:] for line in output.splitlines()
            if line.startswith("ROW ")]


def source_rows(simulator):
    sources = [str(HERE / "memory_edge_case_canonical_e.sv"),
               str(HERE / "memory_edge_case_canonical_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-memory-edge-case-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "memory_edge_case_canonical_e_tb",
                 "-o", exe] + sources, work)
            output, _ = run(["vvp", exe], work)
        else:
            output, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                             "-top", "memory_edge_case_canonical_e_tb"] + sources,
                            work)
    return rows(output)


def main():
    envelope = HERE / "memory_edge_case_canonical_e.sv.json"
    with tempfile.NamedTemporaryFile(prefix="sv-memory-edge-envelope-",
                                     suffix=".json") as generated:
        generated_path = Path(generated.name)
        run(["python3", "extractors/sv/extract.py", "--top",
             "memory_edge_case_canonical_e", "--retain-loops",
             "--retain-proc-rewrites", "-o", str(generated_path),
             str((HERE / "memory_edge_case_canonical_e.sv").relative_to(ROOT))])
        if generated_path.read_bytes() != envelope.read_bytes():
            raise RuntimeError("extractor envelope is stale")
    run(["lake", "build",
         "Examples.«system-verilog».sem2.memory_edge_case_canonical_e.agree"])
    lean, _ = run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")])
    expected = rows(lean)
    if expected != [["i=0", "q0=0001", "q1=0010", "hit=xxxx"],
                    ["i=1", "q0=1010", "q1=0010", "hit=xxxx"]]:
        raise RuntimeError(f"unexpected E rows: {expected}\n{lean}")
    print("extractor: envelope regenerates byte-identically")
    print("E: 2 rows (source-shaped edge case, memory-0 NBA arm)")

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

    source_expected = [
        ["i=0", "q0=0001", "q1=0010", "hit=xxxx"],
        ["i=1", "q0=1010", "q1=0010", "hit=xxxx"],
        ["i=2", "q0=1010", "q1=0010", "hit=xxxx"],
        ["i=3", "q0=1010", "q1=1011", "hit=xxxx"],
        ["i=4", "q0=1010", "q1=1011", "hit=xxxx"],
        ["i=5", "q0=1010", "q1=1011", "hit=1100"],
    ]
    for simulator in simulators:
        actual = source_rows(simulator)
        if actual != source_expected:
            raise RuntimeError(f"{simulator}: expected {source_expected}, got {actual}")
        print(f"{simulator}: {len(actual)} source rows MATCH")


if __name__ == "__main__":
    main()
