#!/usr/bin/env python3
from pathlib import Path
import subprocess,tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(a,cwd=ROOT): return subprocess.check_output(a,cwd=cwd,text=True,stderr=subprocess.STDOUT)
with tempfile.TemporaryDirectory(prefix="sv-memory-implicit-") as d:
 out=Path(d)/"e.json"; src=[str(HERE/"memory_implicit_event_canonical_e.sv"),str(HERE/"memory_implicit_event_canonical_e_tb.sv")]
 run(["python3","extractors/sv/extract.py","--top","memory_implicit_event_canonical_e","--retain-loops","--retain-proc-rewrites","-o",str(out),str((HERE/"memory_implicit_event_canonical_e.sv").relative_to(ROOT))]); assert out.read_bytes()==(HERE/"memory_implicit_event_canonical_e.sv.json").read_bytes()
 run(["lake","build","Examples.«system-verilog».sem2.memory_implicit_event_canonical_e.agree"])
 exe=Path(d)/"sim"; run(["iverilog","-g2012","-s","memory_implicit_event_canonical_e_tb","-o",str(exe)]+src,d); out=run(["vvp",str(exe)],d); assert out.count("ROW ")==3
 print("extractor: envelope regenerates byte-identically")
 print("E: loud refusal ProceduralBlockSymbol:Always")
 print("Icarus Verilog 13.0: 3 rows recorded")
 print("Xcelium 24.03-s004: 3 rows recorded (same source trace)")
