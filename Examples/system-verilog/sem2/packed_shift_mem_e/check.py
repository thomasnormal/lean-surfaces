#!/usr/bin/env python3
from pathlib import Path
import shutil,subprocess,tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(a,cwd=ROOT): return subprocess.check_output(a,cwd=cwd,text=True,stderr=subprocess.STDOUT)
def rows(s):
 return sorted([x for x in s.splitlines() if x.startswith("ROW ")], key=lambda x:(x.split()[1],x.split()[2]))
with tempfile.TemporaryDirectory(prefix="sv-packed-shift-") as d:
 out=Path(d)/"packed_shift_mem_e.sv.json"; src=[str(HERE/"packed_shift_mem_e.sv"),str(HERE/"packed_shift_mem_e_tb.sv")]
 run(["python3","extractors/sv/extract.py","--top","packed_shift_mem_e","--retain-loops","--retain-proc-rewrites","-o",str(out),str((HERE/"packed_shift_mem_e.sv").relative_to(ROOT))]); assert out.read_bytes()==(HERE/"packed_shift_mem_e.sv.json").read_bytes()
 run(["lake","build","Examples.«system-verilog».sem2.packed_shift_mem_e.agree"]); expected=rows(run(["lake","env","lean","--run",str(HERE/"oracle.lean")]))
 exe=Path(d)/"sim"; run(["iverilog","-g2012","-s","packed_shift_mem_e_tb","-o",str(exe)]+src,d); assert rows(run(["vvp",str(exe)],d))==expected
 print("extractor: envelope regenerates byte-identically"); print("E: 8 rows; Icarus Verilog 13.0: 8 rows MATCH E")
 if shutil.which("xrun"):
  actual=rows(run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","packed_shift_mem_e_tb"]+src,d)); assert actual==expected
  print("Xcelium 24.03-s004: 8 rows MATCH E")
 else: print("no Xcelium result: xrun unavailable")
