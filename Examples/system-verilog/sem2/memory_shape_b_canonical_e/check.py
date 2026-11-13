#!/usr/bin/env python3
"""Compare the first two canonical-E hierarchy-memory slots with simulators."""
from pathlib import Path
import os, shutil, signal, subprocess, tempfile, sys
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium

def run(args, cwd=ROOT):
    p=subprocess.Popen(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    try: out,err=p.communicate(timeout=180)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGKILL); out,err=p.communicate(); raise RuntimeError(f"timeout: {out}{err}")
    if p.returncode: raise RuntimeError(f"exit {p.returncode}: {out}{err}")
    return out

def rows(out): return [line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]
def main():
    expected=rows(run(["lake","env","lean","--run",str(HERE/"oracle.lean")]))
    if expected != [["i=0","q=xxxx"],["i=1","q=xxxx"]]: raise RuntimeError(f"E rows: {expected}")
    print("E: 2 hierarchy-memory rows MATCH")
    src=str(HERE/"memory_shape_b_canonical_e.sv")
    tb='''module tb; logic clk=0; logic [3:0] d=0; wire [3:0] q; memory_shape_b_canonical_e dut(.*); initial begin #1 $display("ROW i=0 q=%b",q); d=1; clk=1; #1 $display("ROW i=1 q=%b",q); $finish; end endmodule'''
    for sim in (["iverilog"] if shutil.which("iverilog") else []):
      with tempfile.TemporaryDirectory(prefix="sv-e-hierarchy-memory-") as w:
       t=Path(w)/"tb.sv"; t.write_text(tb); exe=str(Path(w)/"sim"); run([sim,"-g2012","-s","tb","-o",exe,src,str(t)],w); actual=rows(run(["vvp",exe],w))
      if actual != expected: raise RuntimeError(f"{sim}: {actual} != {expected}")
      print(f"{sim}: 2 rows MATCH E")
    if shutil.which("xrun"):
      status,details=probe_xcelium(); print(details)
      if status==0:
       with tempfile.TemporaryDirectory(prefix="sv-e-hierarchy-memory-") as w:
        t=Path(w)/"tb.sv"; t.write_text(tb); actual=rows(run(["xrun","-sv","-q","-top","tb",src,str(t)],w))
       if actual != expected: raise RuntimeError(f"xrun: {actual} != {expected}")
       print("xrun: 2 rows MATCH E")
      elif status==77: print("no Xcelium result: explicit license refusal")
      else: raise RuntimeError("Xcelium readiness failed")
if __name__ == "__main__": main()
