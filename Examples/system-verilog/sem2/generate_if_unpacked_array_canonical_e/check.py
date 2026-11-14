#!/usr/bin/env python3
"""Receipt for a source-shaped generate-if unpacked declaration."""
from pathlib import Path
import os, signal, shutil, subprocess, tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["N=1", "i=0", "y=xxxxxxxx"],
    ["N=1", "i=1", "y=00000000"],
    ["N=1", "i=2", "y=10100101"],
    ["N=1", "i=3", "y=xxxxxxxx"],
    ["N=1", "i=4", "y=zzzzzzzz"],
    ["N=1", "i=5", "y=00111100"],
    ["N=1", "i=6", "y=11111111"],
    ["N=1", "i=7", "y=00000001"],
    ["N=2", "i=0", "y=xxxxxxxx"],
    ["N=2", "i=1", "y=00000000"],
    ["N=2", "i=2", "y=10100101"],
    ["N=2", "i=3", "y=xxxxxxxx"],
    ["N=2", "i=4", "y=zzzzzzzz"],
    ["N=2", "i=5", "y=00111100"],
    ["N=2", "i=6", "y=11111111"],
    ["N=2", "i=7", "y=00000001"],
]

def run(argv, cwd=ROOT):
    p = subprocess.Popen(argv, cwd=cwd, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = p.communicate(timeout=180)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        out, err = p.communicate()
        raise RuntimeError("timeout")
    if p.returncode:
        raise RuntimeError(out + err)
    return out

def rows(out):
    return [line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]

def tb(N):
    values = ["8'bxxxxxxxx", "8'h00", "8'ha5", "8'bxxxxxxxx",
              "8'bzzzzzzzz", "8'h3c", "8'hff", "8'h01"]
    lines = [
        "`timescale 1ns/1ps",
        "module batch_tb; logic [7:0] x; wire [7:0] y;",
        f" generate_if_unpacked_array_canonical_e #(.N({N})) dut(.x(x), .y(y));",
        " initial begin",
    ]
    for i, value in enumerate(values):
        lines += [f"  x={value}; #1 $display(\"ROW N={N} i={i} y=%b\", y);"]
    lines += ["  $finish; end", "endmodule", ""]
    return "\n".join(lines)

def main():
    with tempfile.TemporaryDirectory(prefix="sv-e-generate-if-array-extract-") as w:
        envelope = Path(w) / "generate_if_unpacked_array_canonical_e.sv.json"
        run(["python3", "extractors/sv/extract.py", "--top",
             "generate_if_unpacked_array_canonical_e", "--retain-proc-rewrites",
             "-o", str(envelope), str((HERE / "generate_if_unpacked_array_canonical_e.sv").relative_to(ROOT))])
        if envelope.read_bytes() != (HERE / envelope.name).read_bytes():
            raise RuntimeError("envelope is not reproducible")
    print("extractor: generate-if declaration envelope regenerates byte-identically")
    run(["lake", "build", "Examples.«system-verilog».sem2.generate_if_unpacked_array_canonical_e.agree"])
    actual = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if actual != EXPECTED:
        raise RuntimeError(f"E rows: {actual!r}")
    print("E: generate-if unpacked storage N=1,N=2, 16 rows")
    source = str(HERE / "generate_if_unpacked_array_canonical_e.sv")
    for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        all_rows = []
        for N in [1, 2]:
            with tempfile.TemporaryDirectory(prefix="sv-e-generate-if-array-sim-") as w:
                tb_path = Path(w) / "batch_tb.sv"
                tb_path.write_text(tb(N))
                if sim == "iverilog":
                    exe = Path(w) / "sim"
                    run(["iverilog", "-g2012", "-s", "batch_tb", "-o", str(exe), source, str(tb_path)], Path(w))
                    out = run(["vvp", str(exe)], Path(w))
                else:
                    out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "batch_tb", source, str(tb_path)], Path(w))
                all_rows.extend(rows(out))
        if all_rows != EXPECTED:
            raise RuntimeError(f"{sim}: {all_rows!r}")
        version = run([sim, "-V" if sim == "iverilog" else "-version"], ROOT).splitlines()[0]
        print(f"{version}: 16 source rows MATCH E")

if __name__ == "__main__":
    main()
