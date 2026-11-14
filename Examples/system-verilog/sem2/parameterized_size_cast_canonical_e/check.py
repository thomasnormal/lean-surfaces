#!/usr/bin/env python3
"""Differential receipt for a parameter-sized integral size cast."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["W=2", "i=0", "y=00"],
    ["W=2", "i=1", "y=01"],
    ["W=2", "i=2", "y=00"],
    ["W=2", "i=3", "y=xx"],
    ["W=2", "i=4", "y=zz"],
    ["W=2", "i=5", "y=x1"],
    ["W=12", "i=0", "y=000000000000"],
    ["W=12", "i=1", "y=000010100101"],
    ["W=12", "i=2", "y=000000111100"],
    ["W=12", "i=3", "y=0000xxxxxxxx"],
    ["W=12", "i=4", "y=0000zzzzzzzz"],
    ["W=12", "i=5", "y=000010x1z0x1"],
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
    return f'''module parameterized_size_cast_canonical_e_tb;
  localparam integer W = {width};
  logic [7:0] x;
  wire [W-1:0] y;
  parameterized_size_cast_canonical_e #(.W(W)) dut(.x(x), .y(y));
  initial begin
    x=8'h00; #1 $display("ROW W=%0d i=0 y=%b", W, y);
    x=8'ha5; #1 $display("ROW W=%0d i=1 y=%b", W, y);
    x=8'h3c; #1 $display("ROW W=%0d i=2 y=%b", W, y);
    x=8'bxxxxxxxx; #1 $display("ROW W=%0d i=3 y=%b", W, y);
    x=8'bzzzzzzzz; #1 $display("ROW W=%0d i=4 y=%b", W, y);
    x=8'b10x1z0x1; #1 $display("ROW W=%0d i=5 y=%b", W, y);
    $finish;
  end
endmodule
'''


def main():
    generated = HERE / "parameterized_size_cast_canonical_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "parameterized_size_cast_canonical_e", "-o", temp.name,
             str((HERE / "parameterized_size_cast_canonical_e.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is stale")

    run(["lake", "build",
         "Examples.«system-verilog».sem2.parameterized_size_cast_canonical_e.agree"])
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if expected != EXPECTED:
        raise RuntimeError(f"unexpected E rows: {expected}")
    print("extractor: envelope regenerates byte-identically")
    print("E: 12 ordinary-route rows (W=2 and W=12, truncation/extension/x/z)")

    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    source = str(HERE / "parameterized_size_cast_canonical_e.sv")
    for simulator in simulators:
        actual = []
        for width in (2, 12):
            with tempfile.TemporaryDirectory(prefix="sv-size-cast-") as work:
                tb = Path(work) / "tb.sv"
                tb.write_text(testbench(width))
                if simulator == "iverilog":
                    exe = str(Path(work) / "sim")
                    run(["iverilog", "-g2012", "-s",
                         "parameterized_size_cast_canonical_e_tb", "-o", exe,
                         source, str(tb)], work)
                    actual.extend(rows(run(["vvp", exe], work)))
                else:
                    actual.extend(rows(run(["xrun", "-sv", "-q", "-timescale",
                                            "1ns/1ps", "-top",
                                            "parameterized_size_cast_canonical_e_tb",
                                            source, str(tb)], work)))
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
        version = run(["iverilog", "-V"] if simulator == "iverilog"
                      else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
