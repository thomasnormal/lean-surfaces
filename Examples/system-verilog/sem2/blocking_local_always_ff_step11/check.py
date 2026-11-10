#!/usr/bin/env python3
"""Check source-simulator evidence for scoped locals; E still refuses them."""
import importlib.util
from pathlib import Path
import shutil
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "case_check", HERE.parent / "case_always_ff_step11/check.py")
case_check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(case_check)
run = case_check.run

# These are source oracle rows, never a replacement for an E trace.
FIXTURES = (
    ("blocking_local_always_ff_step11", "q q_not", (
        "xxxx xxxx", "0000 1111", "1010 0101", "xz01 xx10", "zzzz xxxx")),
    ("static_local_lifetime_step11", "q_old q_new q_shadow q_known q_signed", (
        "xxxx xxxx xxxx xxxx xxxxxxxx",
        "xxxx xxxx xxxx 0000 xxxxxxxx",
        "xxxx 1010 0101 0000 11111010",
        "1010 1010 0101 1010 11111010",
        "1010 xz01 xx10 1010 xxxxxz01",
        "xz01 xz01 xx10 0001 xxxxxz01",
        "xz01 zzzz xxxx 0001 zzzzzzzz",
        "zzzz zzzz xxxx 0000 zzzzzzzz",
        "0000 0000 xxxx 0000 00000000",
        "0000 0000 xxxx 0000 00000000")),
)


def rows(output):
    result = []
    for line in output.splitlines():
        if not line.startswith("ROW "):
            continue
        fields = line.split()[1:]
        result.append([field.split("=", 1)[1] for field in fields if "=" in field]
                      if any("=" in field for field in fields) else fields)
    return result


def main():
    print("source oracle evidence only; no E execution result is claimed")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this source check")
    print(run(["iverilog", "-V"]).splitlines()[0])
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = case_check.probe_xcelium()
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

    for top, columns, expected_rows in FIXTURES:
        expected = [line.split() for line in expected_rows]
        sources = [str(HERE / (top + suffix)) for suffix in (".sv", "_tb.sv")]
        print(f"{top}: columns {columns}")
        for simulator in simulators:
            with tempfile.TemporaryDirectory(prefix="sv-static-local-") as work:
                if simulator == "iverilog":
                    exe = str(Path(work) / "sim")
                    run(["iverilog", "-g2012", "-s", top + "_tb", "-o", exe]
                        + sources, work)
                    output = run(["vvp", exe], work)
                else:
                    output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                  "-top", top + "_tb"] + sources, work)
            actual = rows(output)
            if actual != expected:
                raise RuntimeError(f"{top}/{simulator}: expected {expected} != {actual}")
            print(f"{top}/{simulator}: {len(actual)} source rows verified")


if __name__ == "__main__":
    main()
