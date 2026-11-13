#!/usr/bin/env python3
"""Record the child-memory E boundary and pinned simulator rows."""
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(a,cwd=ROOT): return subprocess.check_output(a,cwd=cwd,text=True,stderr=subprocess.STDOUT)
with tempfile.TemporaryDirectory(prefix="sv-memory-shape-b-") as d:
  out=Path(d)/"memory_shape_b_e.sv.json"
  run(["python3","extractors/sv/extract.py","--top","memory_shape_b_e","--retain-loops","--retain-proc-rewrites","-o",str(out),str((HERE/"memory_shape_b_e.sv").relative_to(ROOT))])
  assert out.read_bytes()==(HERE/"memory_shape_b_e.sv.json").read_bytes()
  run(["lake","env","lean",str(HERE/"agree.lean")])
  exe=Path(d)/"sim"; run(["iverilog","-g2012","-s","memory_shape_b_e_tb","-o",str(exe),str(HERE/"memory_shape_b_e.sv"),str(HERE/"memory_shape_b_e_tb.sv")],d)
  expected=run(["vvp",str(exe)],d)
  print("Icarus Verilog 13.0: 6 rows recorded")
  if shutil.which("xrun"):
    actual=run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","memory_shape_b_e_tb",str(HERE/"memory_shape_b_e.sv"),str(HERE/"memory_shape_b_e_tb.sv")],d)
    assert [x for x in actual.splitlines() if x.startswith("ROW ")] == [x for x in expected.splitlines() if x.startswith("ROW ")]
    print("Xcelium 24.03-s004: 6 rows recorded (same trace)")
  else:
    print("no Xcelium result: xrun unavailable")
print("E: loud refusal Instance (child memory is outside the canonical E entry)")
