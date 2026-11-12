#!/usr/bin/env python3
"""Check exact-width constant arithmetic against E and both simulators."""

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
    ("default", "N=10000", "k=1410", "s=0", "a=-649",
     "u=-2147483648", "kh=00000582", "sh=00000000", "ah=fffffd77",
     "uh=80000000"),
    ("override", "N=8", "k=8", "s=0", "a=-641", "u=-2147483648",
     "kh=00000008", "sh=00000000", "ah=fffffd7f", "uh=80000000"),
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


def parse_rows(output):
    rows = []
    for line in output.splitlines():
        if line.startswith("ROW "):
            rows.append(tuple(line.split()[1:]))
    return rows


def check_envelope():
    with tempfile.TemporaryDirectory(prefix="sv-int32-envelope-") as work:
        output = Path(work) / "int32_const_overflow_e.sv.json"
        run([
            sys.executable, str(ROOT / "extractors/sv/extract.py"),
            "--top", "int32_const_overflow_e", "-o", str(output),
            str((HERE / "int32_const_overflow_e.sv").relative_to(ROOT)),
        ])
        recorded = HERE / "int32_const_overflow_e.sv.json"
        if output.read_bytes() != recorded.read_bytes():
            raise RuntimeError("constant-arithmetic envelope is not reproducible")
    print("extractor: envelope regenerates byte-identically")


def check_lean():
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("E: 2 parameter rows MATCH (all four localparams)")


def source_rows(simulator):
    sources = [str(HERE / "int32_const_overflow_e.sv"),
               str(HERE / "int32_const_overflow_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-int32-rows-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "int32_const_overflow_e_tb",
                 "-o", exe] + sources, work)
            output = run(["vvp", exe], work)
        else:
            output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                          "-top", "int32_const_overflow_e_tb"] + sources, work)
    return parse_rows(output)


def simulator_version(binary, first_line=False):
    flag = "-V" if binary == "iverilog" else "-version"
    proc = subprocess.run([binary, flag], cwd=ROOT, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          check=True)
    lines = (proc.stdout + proc.stderr).splitlines()
    return lines[0] if first_line and lines else "\n".join(lines)


def main():
    check_envelope()
    check_lean()
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
    print(simulator_version("iverilog", first_line=True))
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            print(simulator_version("xrun"))
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
        label = "Icarus Verilog 13.0" if simulator == "iverilog" else "Xcelium 24.03-s004"
        print(f"{label}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
