#!/usr/bin/env python3
"""Receipt for a parameter-dependent unpacked array on canonical E."""
from pathlib import Path
import os
import signal
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["i=0", "y=xxxxxxxx"],
    ["i=1", "y=00000000"],
    ["i=2", "y=10100101"],
    ["i=3", "y=11111111"],
    ["i=4", "y=xxxxxxxx"],
    ["i=5", "y=zzzzzzzz"],
    ["i=6", "y=00111100"],
    ["i=7", "y=00000001"],
]


def run(argv, cwd=ROOT):
    proc = subprocess.Popen(argv, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=180)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, err = proc.communicate()
        raise RuntimeError("timeout")
    if proc.returncode:
        raise RuntimeError(out + err)
    return out


def rows(out):
    return [line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]


def testbench():
    values = ["8'bxxxxxxxx", "8'h00", "8'ha5", "8'hff",
              "8'bxxxxxxxx", "8'bzzzzzzzz", "8'h3c", "8'h01"]
    lines = [
        "`timescale 1ns/1ps",
        "module batch_tb; logic [7:0] x; wire [7:0] y;",
        " unpacked_generate_array #(.W(8), .S(2)) dut(.x(x), .y(y));",
        " initial begin",
    ]
    for i, value in enumerate(values):
        lines.append(f"  x={value}; #1 $display(\"ROW i={i} y=%b\", y);")
    lines += ["  $finish; end", "endmodule", ""]
    return "\n".join(lines)


def main():
    source = HERE / "unpacked_generate_array.sv"
    with tempfile.TemporaryDirectory(prefix="sv-e-unpacked-generate-array-extract-") as w:
        envelope = Path(w) / source.name.replace(".sv", ".sv.json")
        run(["python3", "extractors/sv/extract.py", "--top", "unpacked_generate_array",
             "-o", str(envelope), str(source.relative_to(ROOT))])
        if envelope.read_bytes() != (HERE / envelope.name).read_bytes():
            raise RuntimeError("envelope is not reproducible")
    print("extractor: unpacked-array envelope regenerates byte-identically")
    run(["lake", "build", "Examples.«system-verilog».sem2.unpacked_generate_array.agree"])
    actual = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if actual != EXPECTED:
        raise RuntimeError(f"E rows: {actual!r}")
    print("E: parameterized unpacked storage W=8,S=2, 8 rows")
    for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-e-unpacked-generate-array-sim-") as w:
            tb_path = Path(w) / "batch_tb.sv"
            tb_path.write_text(testbench())
            if sim == "iverilog":
                exe = Path(w) / "sim"
                run(["iverilog", "-g2012", "-s", "batch_tb", "-o", str(exe),
                     str(source), str(tb_path)], Path(w))
                out = run(["vvp", str(exe)], Path(w))
            else:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                           "-top", "batch_tb", str(source), str(tb_path)], Path(w))
        actual = rows(out)
        if actual != EXPECTED:
            raise RuntimeError(f"{sim}: {actual!r}")
        version = run([sim, "-V" if sim == "iverilog" else "-version"], ROOT).splitlines()[0]
        print(f"{version}: 8 source rows MATCH E")


if __name__ == "__main__":
    main()
