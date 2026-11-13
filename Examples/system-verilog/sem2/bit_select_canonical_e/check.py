#!/usr/bin/env python3
"""Compare canonical-E packed bit-select rows with both simulators."""
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
    ["known", "1", "0"],
    ["second", "0", "1"],
    ["xvalue", "x", "x"],
    ["xindex", "1", "x"],
    ["zindex", "1", "x"],
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
        if line.startswith("ROW "):
            fields = line.split()
            answer.append([fields[1]] +
                          [field.split("=", 1)[1] for field in fields[2:]])
    return answer


def source_rows(simulator):
    sources = [str(HERE / "bit_select_canonical_e.sv"),
               str(HERE / "bit_select_canonical_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-bit-select-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "bit_select_canonical_e_tb",
                 "-o", exe] + sources, work)
            output, _ = run(["vvp", exe], work)
        else:
            output, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                             "-top", "bit_select_canonical_e_tb"] + sources, work)
    return rows(output)


def main():
    fd, name = tempfile.mkstemp(prefix="sv-e-bit-select-envelope-", suffix=".json")
    os.close(fd)
    envelope = Path(name)
    try:
        run(["python3", "extractors/sv/extract.py", "--top",
             "bit_select_canonical_e", "-o", str(envelope),
             str((HERE / "bit_select_canonical_e.sv").relative_to(ROOT))])
        if envelope.read_bytes() != (HERE / "bit_select_canonical_e.sv.json").read_bytes():
            raise RuntimeError("extractor envelope is stale")
    finally:
        envelope.unlink(missing_ok=True)
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/bit_select_canonical_e/agree.lean"])
    print("extractor: envelope regenerates byte-identically")
    print("E: 5 rows (constant, dynamic, x-value, and x/z-index selects)")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
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
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
