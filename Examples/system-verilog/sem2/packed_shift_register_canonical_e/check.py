#!/usr/bin/env python3
"""Differential receipt for a parameter-width packed shift register."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["N=4", "i=0", "q=xxxx"],
    ["N=4", "i=1", "q=xxx1"],
    ["N=4", "i=2", "q=xxx1"],
    ["N=4", "i=3", "q=xx10"],
    ["N=4", "i=4", "q=xx10"],
    ["N=4", "i=5", "q=x101"],
    ["N=4", "i=6", "q=x101"],
    ["N=4", "i=7", "q=x101"],
    ["N=4", "i=8", "q=101z"],
    ["N=8", "i=0", "q=xxxxxxxx"],
    ["N=8", "i=1", "q=xxxxxxx1"],
    ["N=8", "i=2", "q=xxxxxxx1"],
    ["N=8", "i=3", "q=xxxxxx10"],
    ["N=8", "i=4", "q=xxxxxx10"],
    ["N=8", "i=5", "q=xxxxx101"],
    ["N=8", "i=6", "q=xxxxx101"],
    ["N=8", "i=7", "q=xxxxx101"],
    ["N=8", "i=8", "q=xxxx101z"],
]


def run(args, cwd=ROOT, timeout=240):
    proc = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
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


def testbench(width):
    return f'''module packed_shift_register_canonical_e_tb;
  localparam integer N = {width};
  logic clk;
  logic v;
  wire [N-1:0] q;
  packed_shift_register_canonical_e #(.N(N)) dut(.clk(clk), .v(v), .q(q));
  initial begin
    clk=0; v=0; #1 $display("ROW N=%0d i=0 q=%b", N, q);
    clk=1; v=1; #1 $display("ROW N=%0d i=1 q=%b", N, q);
    clk=0; v=0; #1 $display("ROW N=%0d i=2 q=%b", N, q);
    clk=1; v=0; #1 $display("ROW N=%0d i=3 q=%b", N, q);
    clk=0; v=1; #1 $display("ROW N=%0d i=4 q=%b", N, q);
    clk=1; v=1; #1 $display("ROW N=%0d i=5 q=%b", N, q);
    clk=1'bx; v=1'bx; #1 $display("ROW N=%0d i=6 q=%b", N, q);
    clk=0; v=1'bz; #1 $display("ROW N=%0d i=7 q=%b", N, q);
    clk=1; v=1'bz; #1 $display("ROW N=%0d i=8 q=%b", N, q);
    $finish;
  end
endmodule
'''


def main():
    generated = HERE / "packed_shift_register_canonical_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "packed_shift_register_canonical_e", "-o", temp.name,
             str((HERE / "packed_shift_register_canonical_e.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is stale")

    run(["lake", "build",
         "Examples.«system-verilog».sem2.packed_shift_register_canonical_e.agree"])
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if expected != EXPECTED:
        raise RuntimeError(f"unexpected E rows: {expected}")
    print("extractor: envelope regenerates byte-identically")
    print("E: 18 ordinary-route rows (N=4 and N=8, first/x/z clock/data)")

    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    source = str(HERE / "packed_shift_register_canonical_e.sv")
    for simulator in simulators:
        actual = []
        for width in (4, 8):
            with tempfile.TemporaryDirectory(prefix="sv-packed-shift-") as work:
                tb = Path(work) / "tb.sv"
                tb.write_text(testbench(width))
                if simulator == "iverilog":
                    exe = str(Path(work) / "sim")
                    run(["iverilog", "-g2012", "-s",
                         "packed_shift_register_canonical_e_tb", "-o", exe,
                         source, str(tb)], work)
                    actual.extend(rows(run(["vvp", exe], work)))
                else:
                    actual.extend(rows(run(["xrun", "-sv", "-q", "-timescale",
                                            "1ns/1ps", "-top",
                                            "packed_shift_register_canonical_e_tb",
                                            source, str(tb)], work)))
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
        version = run(["iverilog", "-V"] if simulator == "iverilog"
                      else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
