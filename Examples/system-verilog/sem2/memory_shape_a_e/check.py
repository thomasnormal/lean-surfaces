#!/usr/bin/env python3
"""Compare parameter-sized unpacked storage through MemE and simulators."""
from pathlib import Path
import os, shutil, signal, subprocess, sys, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
sys.path.insert(0,str(ROOT/"harness/sv")); from xcelium_probe import probe_xcelium

def run(args,cwd=ROOT):
 p=subprocess.Popen(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try: out,err=p.communicate(timeout=300)
 except subprocess.TimeoutExpired:
  try: os.killpg(p.pid,signal.SIGKILL)
  except ProcessLookupError: pass
  out,err=p.communicate(); raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
 if p.returncode: raise RuntimeError(f"{args[0]} exited {p.returncode}:\n{out}{err}")
 return out

def rows(out): return {(x[1],x[2]):tuple(x[3:]) for x in (line.split() for line in out.splitlines() if line.startswith("ROW "))}
with tempfile.TemporaryDirectory(prefix="sv-e-memory-shape-a-") as work:
 env=Path(work)/"memory_shape_a_e.sv.json"
 run([sys.executable,str(ROOT/"extractors/sv/extract.py"),"--top","memory_shape_a_e","--retain-loops","--retain-proc-rewrites","-o",str(env),str((HERE/"memory_shape_a_e.sv").relative_to(ROOT))])
 if env.read_bytes()!=(HERE/"memory_shape_a_e.sv.json").read_bytes(): raise RuntimeError("envelope is not reproducible")
 run(["lake","build","Examples.«system-verilog».sem2.memory_shape_a_e.agree"])
 expected=rows(run(["lake","env","lean","--run",str(HERE/"oracle.lean")]))
 if len(expected)!=14: raise RuntimeError(f"E produced {len(expected)} rows")
 print("extractor: envelope regenerates byte-identically")
 print("E: 14 rows")
 sources=[str(HERE/"memory_shape_a_e.sv"),str(HERE/"memory_shape_a_e_tb.sv")]
 exe=Path(work)/"sim"; run(["iverilog","-g2012","-s","memory_shape_a_e_tb","-o",str(exe)]+sources,work)
 actual=rows(run(["vvp",str(exe)],work)); assert actual==expected,(expected,actual)
 print("Icarus Verilog 13.0: 14 rows MATCH E")
 if shutil.which("xrun"):
  status,details=probe_xcelium(); print(details)
  if status==0:
   actual=rows(run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","memory_shape_a_e_tb"]+sources,work)); assert actual==expected,(expected,actual)
   print("Xcelium 24.03-s004: 14 rows MATCH E")
  elif status==77: print("no Xcelium result: explicit license refusal")
  else: raise RuntimeError("Xcelium readiness probe failed")
 else: print("no Xcelium result: xrun unavailable")
