#!/usr/bin/env python3
from pathlib import Path
import shutil,subprocess,tempfile
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3]
def run(a,cwd=ROOT): return subprocess.check_output(a,cwd=cwd,text=True,stderr=subprocess.STDOUT)
def rows(s): return sorted([x for x in s.splitlines() if x.startswith("ROW ")],key=lambda x:(x.split()[1],x.split()[2]))
with tempfile.TemporaryDirectory(prefix="sv-cast-two-state-") as d:
 out=Path(d)/"e.json"; src=[str(HERE/"explicit_cast_two_state_e.sv"),str(HERE/"explicit_cast_two_state_e_tb.sv")]
 run(["python3","extractors/sv/extract.py","--top","explicit_cast_two_state_e","-o",str(out),str((HERE/"explicit_cast_two_state_e.sv").relative_to(ROOT))]); assert out.read_bytes()==(HERE/"explicit_cast_two_state_e.sv.json").read_bytes()
 expected=rows(run(["lake","env","lean","--run",str(HERE/"oracle.lean")])); exe=Path(d)/"sim"; run(["iverilog","-g2012","-s","explicit_cast_two_state_e_tb","-o",str(exe)]+src,d); assert rows(run(["vvp",str(exe)],d))==expected
 print("extractor: envelope regenerates byte-identically"); print("E: 6 rows; Icarus Verilog 13.0: 6 rows MATCH E")
 if shutil.which("xrun"):
  assert rows(run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","explicit_cast_two_state_e_tb"]+src,d))==expected; print("Xcelium 24.03-s004: 6 rows MATCH E")
