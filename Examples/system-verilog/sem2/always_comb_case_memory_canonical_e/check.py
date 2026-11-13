#!/usr/bin/env python3
"""Compare canonical-E always_comb case/memory rows with Icarus and Xcelium."""
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
    return '''module always_comb_case_memory_canonical_e_tb;
  logic [1:0] sel = 0; logic [3:0] d = 4'hc; wire [3:0] q;
  always_comb_case_memory_canonical_e #(.W(4)) dut(.sel(sel), .d(d), .q(q));
  initial begin
    #1 $display("ROW i=0 q=%b", q);
    sel = 2'd1; #1 $display("ROW i=1 q=%b", q);
    sel = 2'd2; #1 $display("ROW i=2 q=%b", q);
    d = 4'h5; #1 $display("ROW i=3 q=%b", q);
    $finish;
  end
endmodule
'''


def main():
    fd, name = tempfile.mkstemp(prefix="sv-always-comb-memory-envelope-", suffix=".json")
    os.close(fd)
    out_path = Path(name)
    try:
        run(["python3", "extractors/sv/extract.py", "--top",
             "always_comb_case_memory_canonical_e", "-o", str(out_path),
             str((HERE / "always_comb_case_memory_canonical_e.sv").relative_to(ROOT))])
        if out_path.read_bytes() != (HERE / "always_comb_case_memory_canonical_e.sv.json").read_bytes():
            raise RuntimeError("extractor envelope is stale")
    finally:
        out_path.unlink(missing_ok=True)

    run(["lake", "build",
         "Examples.«system-verilog».sem2.always_comb_case_memory_canonical_e.agree"])
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if expected != [["i=0", "q=0011"],
                    ["i=1", "q=0111"], ["i=2", "q=1100"],
                    ["i=3", "q=0101"]]:
        raise RuntimeError(f"unexpected E rows: {expected}")
    print("extractor: envelope regenerates byte-identically")
    print("E: 4 rows (time-zero case, memory reads, scalar reactivation)")
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
        with tempfile.TemporaryDirectory(prefix="sv-always-comb-memory-") as work:
            tb_path = Path(work) / "tb.sv"
            tb_path.write_text(testbench())
            src = str(HERE / "always_comb_case_memory_canonical_e.sv")
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "always_comb_case_memory_canonical_e_tb",
                     "-o", exe, src, str(tb_path)], work)
                output = run(["vvp", exe], work)
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "always_comb_case_memory_canonical_e_tb", src,
                              str(tb_path)], work)
        actual = rows(output)
        if actual != expected:
            raise RuntimeError(f"{simulator}: E {expected} != source {actual}")
        if simulator == "xrun":
            print(run(["xrun", "-version"]).strip())
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
