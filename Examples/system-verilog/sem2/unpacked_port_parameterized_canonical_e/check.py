#!/usr/bin/env python3
"""Differential receipt for a parameter-sized unpacked array port connection."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["N=2", "i=0", "y=0011"],
    ["N=2", "i=1", "y=1111"],
    ["N=2", "i=2", "y=xxxx"],
    ["N=2", "i=3", "y=xxxx"],
    ["N=2", "i=4", "y=0000"],
    ["N=3", "i=0", "y=0011"],
    ["N=3", "i=1", "y=1111"],
    ["N=3", "i=2", "y=xxxx"],
    ["N=3", "i=3", "y=xxxx"],
    ["N=3", "i=4", "y=0000"],
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


def testbench(point):
    return f'''module unpacked_port_parameterized_canonical_e_tb;
  localparam integer P = {point};
  logic [3:0] data [P];
  wire [3:0] y;
  unpacked_port_parameterized_canonical_e #(.W(4), .N(P)) dut(.data(data), .y(y));
  initial begin
    data[0]=4'h1; data[1]=4'h2; if (P > 2) data[2]=4'h4; #1 $display("ROW N=%0d i=0 y=%b", P, y);
    data[0]=4'ha; data[1]=4'h5; if (P > 2) data[2]=4'h7; #1 $display("ROW N=%0d i=1 y=%b", P, y);
    data[0]=4'bxxxx; data[1]=4'h3; if (P > 2) data[2]=4'h8; #1 $display("ROW N=%0d i=2 y=%b", P, y);
    data[0]=4'h9; data[1]=4'bzzzz; if (P > 2) data[2]=4'h0; #1 $display("ROW N=%0d i=3 y=%b", P, y);
    data[0]=4'hf; data[1]=4'hf; if (P > 2) data[2]=4'bxxxx; #1 $display("ROW N=%0d i=4 y=%b", P, y);
    $finish;
  end
endmodule
'''


def main():
    generated = HERE / "unpacked_port_parameterized_canonical_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "unpacked_port_parameterized_canonical_e", "-o", temp.name,
             str((HERE / "unpacked_port_parameterized_canonical_e.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is stale")

    run(["lake", "build",
         "Examples.«system-verilog».sem2.unpacked_port_parameterized_canonical_e.agree"])
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if expected != EXPECTED:
        raise RuntimeError(f"unexpected E rows: {expected}")
    print("extractor: envelope regenerates byte-identically")
    print("E: 10 ordinary-route rows (N=2 and N=3, known/x/z elements)")

    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    src = str(HERE / "unpacked_port_parameterized_canonical_e.sv")
    for simulator in simulators:
        actual = []
        for point in (2, 3):
            with tempfile.TemporaryDirectory(prefix="sv-unpacked-port-") as work:
                tb = Path(work) / "tb.sv"
                tb.write_text(testbench(point))
                if simulator == "iverilog":
                    exe = str(Path(work) / "sim")
                    run(["iverilog", "-g2012", "-s",
                         "unpacked_port_parameterized_canonical_e_tb", "-o", exe,
                         src, str(tb)], work)
                    actual.extend(rows(run(["vvp", exe], work)))
                else:
                    actual.extend(rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                            "-top", "unpacked_port_parameterized_canonical_e_tb",
                                            src, str(tb)], work)))
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
        version = run(["iverilog", "-V"] if simulator == "iverilog"
                      else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
