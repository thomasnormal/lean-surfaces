#!/usr/bin/env python3
"""Compare parameter-sized unpacked input ports through MemE."""
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(a,cwd=ROOT): return subprocess.check_output(a,cwd=cwd,text=True,stderr=subprocess.STDOUT)
def rows(s): return [x for x in s.splitlines() if x.startswith("ROW ")]
with tempfile.TemporaryDirectory(prefix="sv-memory-shape-c-") as d:
  out=Path(d)/"memory_shape_c_e.sv.json"
  run(["python3","extractors/sv/extract.py","--top","memory_shape_c_e","--retain-loops","--retain-proc-rewrites","-o",str(out),str((HERE/"memory_shape_c_e.sv").relative_to(ROOT))])
  assert out.read_bytes()==(HERE/"memory_shape_c_e.sv.json").read_bytes()
  run(["lake","build","Examples.«system-verilog».sem2.memory_shape_c_e.agree"])
  refusal=run(["lake","env","lean","--run",str(HERE/"oracle.lean")])
  assert "generate items" in refusal
  exe=Path(d)/"sim"; src=[str(HERE/"memory_shape_c_e.sv"),str(HERE/"memory_shape_c_e_tb.sv")]
  run(["iverilog","-g2012","-s","memory_shape_c_e_tb","-o",str(exe)]+src,d); expected=rows(run(["vvp",str(exe)],d)); assert len(expected)==4
  print("extractor: envelope regenerates byte-identically")
  print("E: loud refusal generate items; Icarus Verilog 13.0: 4 rows recorded")
  if shutil.which("xrun"):
    actual=rows(run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","memory_shape_c_e_tb"]+src,d)); assert actual==expected
    print("Xcelium 24.03-s004: 4 rows recorded (same trace)")
  else: print("no Xcelium result: xrun unavailable")
