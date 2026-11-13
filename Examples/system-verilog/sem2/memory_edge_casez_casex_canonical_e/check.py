#!/usr/bin/env python3
"""Check canonical-E casez/casex execution against both simulators."""

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
    sources = [str(HERE / "memory_edge_casez_casex_canonical_e.sv"),
               str(HERE / "memory_edge_casez_casex_canonical_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-memory-case-wildcard-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "memory_edge_casez_casex_canonical_e_tb",
                 "-o", exe] + sources, work)
            output, _ = run(["vvp", exe], work)
        else:
            output, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                             "-top", "memory_edge_casez_casex_canonical_e_tb"] + sources,
                            work)
    return rows(output)


def main():
    envelope = HERE / "memory_edge_casez_casex_canonical_e.sv.json"
    with tempfile.NamedTemporaryFile(prefix="sv-memory-case-wildcard-envelope-",
                                     suffix=".json") as generated:
        generated_path = Path(generated.name)
        run(["python3", "extractors/sv/extract.py", "--top",
             "memory_edge_casez_casex_canonical_e", "--retain-loops",
             "-o", str(generated_path),
             str((HERE / "memory_edge_casez_casex_canonical_e.sv").relative_to(ROOT))])
        if generated_path.read_bytes() != envelope.read_bytes():
            raise RuntimeError("extractor envelope is stale")
    run(["lake", "build",
         "Examples.«system-verilog».sem2.memory_edge_casez_casex_canonical_e.agree"])
    lean, _ = run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")])
    expected = rows(lean)
    if expected != [
            ["i=0", "qz=0001", "qx=0010", "plain=0000"],
            ["i=1", "qz=0001", "qx=0100", "plain=0000"],
            ]:
        raise RuntimeError(f"unexpected E rows: {expected}\n{lean}")
    print("extractor: envelope regenerates byte-identically")
    print("E: 2 rows (source-shaped case, casez, and casex edge assignments)")

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
        ["first", "qz=0001", "qx=0010", "plain=0000"],
        ["sel_0000_d9", "qz=0011", "qx=0110", "plain=1001"],
        ["sel_0001_d8", "qz=0010", "qx=0101", "plain=0000"],
        ["sel_01xz_d7", "qz=0001", "qx=0100", "plain=0000"],
        ["sel_1x00_d6", "qz=0110", "qx=0110", "plain=0000"],
        ["sel_zzzz_d5", "qz=0101", "qx=0101", "plain=0000"],
    ]
    for simulator in simulators:
        actual = source_rows(simulator)
        if actual != source_expected:
            raise RuntimeError(f"{simulator}: expected {source_expected}, got {actual}")
        print(f"{simulator}: {len(actual)} source rows MATCH")


if __name__ == "__main__":
    main()
