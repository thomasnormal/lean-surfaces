#!/usr/bin/env python3
"""Compare canonical-E time-zero memory rows with Icarus and Xcelium."""
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


def testbench():
    return '''module memory_initial_canonical_e_tb;
  logic [1:0] idx=0;
  wire [7:0] q;
  memory_initial_canonical_e #(.W(8), .P(3), .INIT_ZERO(1)) dut(.idx(idx), .q(q));
  task show(input integer i);
    #1 $display("ROW i=%0d q=%b", i, q);
  endtask
  initial begin
    idx=0; show(0);
    idx=1; show(1);
    idx='x; show(2);
    $finish;
  end
endmodule
'''


def main():
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if expected != [["i=0", "q=10100101"], ["i=1", "q=00000000"],
                    ["i=2", "q=xxxxxxxx"]]:
        raise RuntimeError(f"unexpected E rows: {expected}")
    print("E: 3 rows (time-zero initializer, known and x indices)")
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
        with tempfile.TemporaryDirectory(prefix="sv-e-memory-initial-") as work:
            tb_path = Path(work) / "tb.sv"
            tb_path.write_text(testbench())
            src = str(HERE / "memory_initial_canonical_e.sv")
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "memory_initial_canonical_e_tb",
                     "-o", exe, src, str(tb_path)], work)
                output = run(["vvp", exe], work)
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "memory_initial_canonical_e_tb", src,
                              str(tb_path)], work)
        actual = rows(output)
        if actual != expected:
            raise RuntimeError(f"{simulator}: E {expected} != source {actual}")
        if simulator == "xrun":
            print(run(["xrun", "-version"]).strip())
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
