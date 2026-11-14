#!/usr/bin/env python3
"""Differential receipt for a dynamic unpacked-array target."""

from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["i=0", "y=xxxxxxxx"],
    ["i=1", "y=00000000"],
    ["i=2", "y=10100101"],
    ["i=3", "y=00111100"],
    ["i=4", "y=xxxxxxxx"],
    ["i=5", "y=xxxxxxxx"],
    ["i=6", "y=zzzzzzzz"],
    ["i=7", "y=xxxxxxxx"],
    ["i=8", "y=00001111"],
]


def run(args, cwd=ROOT):
    proc = subprocess.Popen(args, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    try:
        out, err = proc.communicate(timeout=180)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out


def rows(output):
    return [line.split()[1:] for line in output.splitlines()
            if line.startswith("ROW ")]


def testbench():
    return """module unpacked_array_target_canonical_e_tb;
  logic [7:0] x; logic idx; wire [7:0] y;
  unpacked_array_target_canonical_e dut(.x(x), .idx(idx), .y(y));
  initial begin
    #1 $display("ROW i=0 y=%b", y);
    x=8'h00; idx=1'b0; #1 $display("ROW i=1 y=%b", y);
    x=8'ha5; idx=1'b1; #1 $display("ROW i=2 y=%b", y);
    x=8'h3c; idx=1'b0; #1 $display("ROW i=3 y=%b", y);
    x=8'bxxxxxxxx; idx=1'b1; #1 $display("ROW i=4 y=%b", y);
    x=8'h5a; idx=1'bx; #1 $display("ROW i=5 y=%b", y);
    x=8'bzzzzzzzz; idx=1'b0; #1 $display("ROW i=6 y=%b", y);
    x=8'h96; idx=1'bz; #1 $display("ROW i=7 y=%b", y);
    x=8'h0f; idx=1'b1; #1 $display("ROW i=8 y=%b", y);
    $finish;
  end
endmodule
"""


def main():
    generated = HERE / "unpacked_array_target_canonical_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "unpacked_array_target_canonical_e", "--retain-proc-rewrites",
             "-o", temp.name,
             str((HERE / "unpacked_array_target_canonical_e.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is stale")

    run(["lake", "build",
         "Examples.«system-verilog».sem2.unpacked_array_target_canonical_e.agree"])
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if expected != EXPECTED:
        raise RuntimeError(f"unexpected E rows: {expected}")
    print("extractor: retained envelope regenerates byte-identically")
    print("E: 9 rows (initial state, known 0/1 indices, x/z data and indices)")

    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus Verilog 13.0 is required")
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    for simulator in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-unpacked-target-") as work:
            tb = Path(work) / "tb.sv"
            tb.write_text(testbench())
            src = str(HERE / "unpacked_array_target_canonical_e.sv")
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s",
                     "unpacked_array_target_canonical_e_tb", "-o", exe,
                     src, str(tb)], work)
                actual = rows(run(["vvp", exe], work))
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "unpacked_array_target_canonical_e_tb",
                                   src, str(tb)], work))
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
        version = run(["iverilog", "-V"] if simulator == "iverilog"
                      else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
