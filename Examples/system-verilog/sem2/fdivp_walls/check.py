#!/usr/bin/env python3
"""Measure the three fdivp clean-room walls on the current loader."""
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


def run(args, cwd=ROOT, check=True):
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
    if check and p.returncode:
        raise RuntimeError(f"{args[0]} exited {p.returncode}:\n{out}{err}")
    return p.returncode, out, err


def rows(output):
    return [line.split()[1:] for line in output.splitlines()
            if line.startswith("ROW ")]


def check_envelopes():
    sources = [
        ("fdivp_sized_localparam", "fdivp_sized_localparam.sv"),
        ("generate_wall", "fdivp_generate_localdecl.sv"),
        ("pow_wall", "fdivp_large_pow.sv"),
    ]
    for top, source in sources:
        with tempfile.TemporaryDirectory(prefix="sv-fdivp-envelope-") as work:
            output = Path(work) / (source + ".json")
            run([sys.executable, str(ROOT / "extractors/sv/extract.py"),
                 "--top", top, "-o", str(output),
                 str((HERE / source).relative_to(ROOT))])
            recorded = HERE / (source + ".json")
            if output.read_bytes() != recorded.read_bytes():
                raise RuntimeError(f"{top}: envelope is not byte-identical")
    print("extractor: all three envelopes regenerate byte-identically")


def check_loader_wall():
    # The sized localparam is admitted from its parser-shaped conversion node.
    source = str(HERE / "fdivp_sized_localparam.sv.json")
    text = f'''import LeanModels.Sv.Ingest2\nnamespace FDivpWall\nopen LeanModels.Sv\nload_design_sv2 fdivpSized from "{source}"\nend FDivpWall\n'''
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT,
                                     delete=False) as probe:
        probe.write(text)
        probe_path = Path(probe.name)
    try:
        code, out, err = run(["lake", "env", "lean", str(probe_path)], check=False)
    finally:
        probe_path.unlink(missing_ok=True)
    diagnostic = out + err
    if code != 0:
        raise RuntimeError(f"sized localparam load failed:\n{diagnostic}")
    print("loader: sized localparam loads through implicit width conversion")


def source_rows(simulator):
    sources = [str(HERE / "fdivp_sized_localparam.sv"),
               str(HERE / "fdivp_sized_localparam_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-fdivp-source-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "fdivp_sized_localparam_tb",
                 "-o", exe] + sources, work)
            return rows(run(["vvp", exe], work)[1])
        return rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                         "-top", "fdivp_sized_localparam_tb"] + sources, work)[1])


def source_rows_for(simulator, top, source, tb):
    sources = [str(HERE / source), str(HERE / tb)]
    with tempfile.TemporaryDirectory(prefix="sv-fdivp-source-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", top, "-o", exe] + sources, work)
            return rows(run(["vvp", exe], work)[1])
        return rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                         "-top", top] + sources, work)[1])


def main():
    check_envelopes()
    check_loader_wall()
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    expected = [["default", "y=f"], ["override", "y=2"]]
    expected_generate = [["zero", "y=00"], ["pattern", "y=a5"]]
    expected_pow = [["large", "y=00"]]
    print("instantiate: generate locals are named unsupported; large ** wraps to zero")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required")
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
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
        print(f"{simulator}: {len(actual)} rows MATCH source")
        actual = source_rows_for(simulator, "generate_wall_tb",
                                 "fdivp_generate_localdecl.sv",
                                 "fdivp_generate_localdecl_tb.sv")
        if actual != expected_generate:
            raise RuntimeError(f"{simulator} generate: expected {expected_generate}, got {actual}")
        print(f"{simulator}: {len(actual)} generate rows MATCH source")
        actual = source_rows_for(simulator, "pow_wall_tb",
                                 "fdivp_large_pow.sv", "fdivp_large_pow_tb.sv")
        if actual != expected_pow:
            raise RuntimeError(f"{simulator} power: expected {expected_pow}, got {actual}")
        print(f"{simulator}: {len(actual)} power rows MATCH source")


if __name__ == "__main__":
    main()
