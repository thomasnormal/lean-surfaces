#!/usr/bin/env python3
"""Check arithmetic-right int shifts with negative and oversized counts."""
from pathlib import Path
import os, signal, shutil, subprocess, tempfile, sys
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
sys.path.insert(0,str(ROOT/"harness/sv")); from xcelium_probe import probe_xcelium

def run(args,cwd=ROOT):
 p=subprocess.Popen(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try: out,err=p.communicate(timeout=120)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGKILL); out,err=p.communicate(); raise RuntimeError(f"timeout: {out}{err}")
 if p.returncode: raise RuntimeError(f"exit {p.returncode}: {out}{err}")
 return out

def rows(out): return [tuple(x.split()[1:]) for x in out.splitlines() if x.startswith("ROW ")]
def main():
 expected=rows(run(["lake","env","lean","--run",str(HERE/"oracle.lean")]))
 if len(expected)!=2: raise RuntimeError(f"E rows {expected}")
 print("E: 2 rows MATCH")
 with tempfile.TemporaryDirectory(prefix="sv-ashr-huge-") as w:
  src=str(HERE/"int32_ashr_huge_e.sv"); tb=str(HERE/"int32_ashr_huge_e_tb.sv"); exe=str(Path(w)/"sim")
  run(["iverilog","-g2012","-s","int32_ashr_huge_e_tb","-o",exe,src,tb],w); actual=rows(run(["vvp",exe],w))
 if actual!=expected: raise RuntimeError(f"Icarus {actual} != {expected}")
 print("Icarus Verilog 13.0: 2 rows MATCH E")
 if shutil.which("xrun"):
  status,details=probe_xcelium(); print(details)
  if status==0:
   with tempfile.TemporaryDirectory(prefix="sv-ashr-huge-") as w:
    actual=rows(run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","int32_ashr_huge_e_tb",str(HERE/"int32_ashr_huge_e.sv"),str(HERE/"int32_ashr_huge_e_tb.sv")],w))
   if actual!=expected: raise RuntimeError(f"Xcelium {actual} != {expected}")
   print("Xcelium 24.03-s004: 2 rows MATCH E")
  elif status==77: print("no Xcelium result: explicit license refusal")
  else: raise RuntimeError("Xcelium readiness failed")
if __name__ == "__main__": main()
