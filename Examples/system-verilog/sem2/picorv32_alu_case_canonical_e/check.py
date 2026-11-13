#!/usr/bin/env python3
"""Differential receipt for the source-shaped PicoRV32 ALU case body."""
from pathlib import Path
import shutil, subprocess, tempfile, sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["0", "00000000000000000000000000000001"],
    ["1", "00000000000000000000000000000110"],
]

def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=120)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout

def rows(text):
    return [[x if "=" not in x else x.split("=", 1)[1]
             for x in line.split()[1:]]
            for line in text.splitlines() if line.startswith("ROW ")]

def main():
    src = str(HERE / "picorv32_alu_case_canonical_e.sv")
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run([sys.executable, str(ROOT / "extractors/sv/extract.py"),
             "--top", "picorv32_alu_case_canonical_e", "-o", f.name,
             str((HERE / "picorv32_alu_case_canonical_e.sv").relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / "picorv32_alu_case_canonical_e.sv.json").read_bytes():
            raise RuntimeError("envelope is not byte-identical to extraction")
    print("extractor: envelope regenerates byte-identically")
    run(["lake", "build", "Examples.«system-verilog».sem2.picorv32_alu_case_canonical_e.agree"])
    e = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if e != EXPECTED:
        raise RuntimeError(f"E: {e}")
    print("E: 2 rows")
    tb = str(HERE / "picorv32_alu_case_canonical_e_tb.sv")
    with tempfile.TemporaryDirectory(prefix="sv-e-alu-case-") as w:
        exe = str(Path(w) / "sim")
        run(["iverilog", "-g2012", "-s", "tb", "-o", exe, src, tb], w)
        if rows(run(["vvp", exe], w)) != EXPECTED:
            raise RuntimeError("Icarus trace differs from E")
    print("Icarus Verilog 13.0: 2 rows MATCH E")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-e-alu-case-xrun-") as w:
            if rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                         "-top", "tb", src, tb], w)) != EXPECTED:
                raise RuntimeError("Xcelium trace differs from E")
        print("Xcelium 24.03-s004: 2 rows MATCH E")

if __name__ == "__main__":
    main()
