#!/usr/bin/env python3
"""Compare canonical-E source-shaped memory rows with Icarus and Xcelium."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile
import sys

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
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out

def rows(output):
    return [line.split()[1:] for line in output.splitlines()
            if line.startswith("ROW ")]

def tb(width, depth):
    return f'''module memory_shape_a_canonical_e_tb;
  logic clk=0; logic [{width-1}:0] d=0; logic [{depth-1}:0] idx=0;
  wire [{width-1}:0] q, selected;
  memory_shape_a_canonical_e #(.W({width}), .P({depth})) dut(.*);
  task show(input integer i);
    #1 $display("ROW W={width} P={depth} i=%0d q=%b selected=%b", i, q, selected);
  endtask
  initial begin
    d=1; idx=0; clk=0; #1 show(0);
    d=2; idx=0; clk=1; #1 show(1);
    d=3; idx=1; clk=0; #1 show(2);
    d=4; idx=1; clk=1; #1 show(3);
    d=5; idx='x; clk=0; #1 show(4);
    d=6; idx=2; clk=1; #1 show(5); $finish;
  end
endmodule
'''

def main():
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if len(expected) != 12:
        raise RuntimeError(f"E produced {len(expected)} rows: {expected}")
    print("E: 12 rows (W=4,P=3 and W=8,P=5)")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
    print(run(["iverilog", "-V"]).splitlines()[0])
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
        actual = []
        for width, depth in ((4, 3), (8, 5)):
            with tempfile.TemporaryDirectory(prefix="sv-e-memory-shape-") as work:
                tb_path = Path(work) / "tb.sv"
                tb_path.write_text(tb(width, depth))
                src = str(HERE / "memory_shape_a_canonical_e.sv")
                if simulator == "iverilog":
                    exe = str(Path(work) / "sim")
                    run(["iverilog", "-g2012", "-s", "memory_shape_a_canonical_e_tb",
                         "-o", exe, src, str(tb_path)], work)
                    output = run(["vvp", exe], work)
                else:
                    output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                  "-top", "memory_shape_a_canonical_e_tb", src,
                                  str(tb_path)], work)
            actual.extend(rows(output))
        if actual != expected:
            raise RuntimeError(f"{simulator}: E {expected} != source {actual}")
        if simulator == "xrun":
            print(run(["xrun", "-version"]).strip())
        print(f"{simulator}: {len(actual)} rows MATCH E")

if __name__ == "__main__":
    main()
