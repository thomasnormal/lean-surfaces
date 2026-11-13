#!/usr/bin/env python3
"""Compare canonical-E fixed unpacked loop-local-index rows with simulators."""
from pathlib import Path
import os, shutil, signal, subprocess, tempfile, sys
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium

def run(args, cwd=ROOT):
    proc = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    try: out, err = proc.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL); out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode: raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out

def rows(output):
    return [line.split()[1:] for line in output.splitlines() if line.startswith("ROW ")]

def tb(width):
    return f'''module memory_shape_d_canonical_e_tb;
  logic clk=0; logic [{width-1}:0] d=0; logic [1:0] idx=0;
  wire [{width-1}:0] q, selected;
  memory_shape_d_canonical_e #(.W({width})) dut(.*);
  initial begin
    #1; $display("ROW W={width} i=0 q=%b selected=%b",q,selected);
    d=1; idx=0; clk=1; #1; $display("ROW W={width} i=1 q=%b selected=%b",q,selected);
    d=2; idx=2'bxx; clk=0; #1; $display("ROW W={width} i=2 q=%b selected=%b",q,selected);
    $finish;
  end
endmodule
'''

def main():
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if len(expected) != 6: raise RuntimeError(f"E produced {len(expected)} rows: {expected}")
    print("E: 6 rows (W=4,8; loop-local index and x index)")
    if not shutil.which("iverilog") or not shutil.which("vvp"): raise RuntimeError("Icarus is required")
    print(run(["iverilog", "-V"]).splitlines()[0]); simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium(); print(details)
        if status == 0: simulators.append("xrun")
        elif status == 77: print("no Xcelium result: explicit license refusal")
        else: raise RuntimeError("Xcelium readiness probe failed")
    else: print("no Xcelium result: xrun unavailable")
    for simulator in simulators:
        actual = []
        for width in (4, 8):
            with tempfile.TemporaryDirectory(prefix="sv-e-memory-shape-d-") as work:
                tb_path = Path(work) / "tb.sv"; tb_path.write_text(tb(width))
                src = str(HERE / "memory_shape_d_canonical_e.sv")
                if simulator == "iverilog":
                    exe = str(Path(work) / "sim")
                    run(["iverilog", "-g2012", "-s", "memory_shape_d_canonical_e_tb", "-o", exe, src, str(tb_path)], work)
                    output = run(["vvp", exe], work)
                else:
                    output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "memory_shape_d_canonical_e_tb", src, str(tb_path)], work)
            actual.extend(rows(output))
        if actual != expected: raise RuntimeError(f"{simulator}: E {expected} != source {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH E")
if __name__ == "__main__": main()
