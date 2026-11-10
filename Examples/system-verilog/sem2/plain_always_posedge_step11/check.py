#!/usr/bin/env python3
"""Compare source-shaped plain-always E traces with both gated simulators."""

import importlib.util
from pathlib import Path
import shutil
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "case_check", HERE.parent / "case_always_ff_step11/check.py")
case_check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(case_check)


def check_reset_source():
    """The refused iff regression has source evidence, not an E trace."""
    top = "plain_always_reset_metadata_step11"
    expected = [line.split() for line in (
        "first x x", "clock 1 1", "masked_reset 0 1", "clock_gate_zero 0 0",
        "reload 1 1", "enabled_reset 0 0", "data_x x x", "data_z z z",
        "reload_for_unknown_gate 1 1", "gate_x 0 1", "gate_z 0 1")]
    sources = [str(HERE / (top + suffix)) for suffix in (".sv", "_tb.sv")]
    simulators = ["iverilog"]
    print(case_check.run(["iverilog", "-V"]).splitlines()[0])
    if shutil.which("xrun"):
        status, details = case_check.probe_xcelium()
        print(details)
        if status == 0:
            print(case_check.run(["xrun", "-version"]).strip())
            simulators.append("xrun")
        elif status == 77:
            print("no Xcelium result for reset-event iff: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result for reset-event iff: xrun unavailable")
    for simulator in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-reset-metadata-") as work:
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                try:
                    case_check.run(["iverilog", "-g2012", "-s", top + "_tb", "-o", exe]
                                   + sources, work)
                except RuntimeError as error:
                    # Exact observed Icarus-13 diagnostic at this source's iff.
                    # A new compiler that accepts it must run all rows; every
                    # other compilation failure remains a hard error.
                    known = [sources[0] + ":9: " + diagnostic for diagnostic in (
                        "syntax error", "error: Malformed event control expression.",
                        "error: Invalid event control.")]
                    if str(error).splitlines() != ["iverilog exited 3:"] + known:
                        raise
                    print("no Icarus result for reset-event iff: " + str(error))
                    continue
                output = case_check.run(["vvp", exe], work)
            else:
                output = case_check.run(
                    ["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", top + "_tb"]
                    + sources, work)
        actual = [line.split()[1:] for line in output.splitlines() if line.startswith("ROW ")]
        if actual != expected:
            raise RuntimeError(f"reset-source/{simulator}: expected {expected} != {actual}")
        print(f"reset-source/{simulator}: {len(actual)} source rows verified; no E execution result")


if __name__ == "__main__":
    case_check.main(HERE, (("plainedge", "plain_always_posedge_step11", 6),
                           ("kinds", "plain_always_kinds_step11", 13)))
    check_reset_source()
