#!/usr/bin/env python3
"""Differential receipt for parameter-sized E memory shift loops."""
from pathlib import Path
import os, shutil, signal, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def run(args, cwd=ROOT):
 p=subprocess.Popen(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try: out,err=p.communicate(timeout=120)
 except subprocess.TimeoutExpired:
  try: os.killpg(p.pid, signal.SIGKILL)
  except ProcessLookupError: pass
  out,err=p.communicate(); raise RuntimeError(f"timeout: {out}{err}")
 if p.returncode: raise RuntimeError(f"{args} failed:\n{out}{err}")
 return out

def rows(s): return [line.split()[1:] for line in s.splitlines() if line.startswith('ROW ')]
def tb(p):
 return f'''module tb; logic clk=0; logic [7:0] d=0; wire [7:0] q;
param_mem_shift_e #(.W(8),.P({p})) dut(.*);
initial begin #1 $display("ROW P{p}_0 q=%b",q); d=8'ha5; clk=1; #1 $display("ROW P{p}_1 q=%b",q); clk=0; d=8'h5a; #1 $display("ROW P{p}_2 q=%b",q); clk=1; #1 $display("ROW P{p}_3 q=%b",q); clk=0; d=8'hxx; #1 $display("ROW P{p}_4 q=%b",q); $finish; end endmodule'''
def sim(p, kind):
 with tempfile.TemporaryDirectory(prefix='sv-param-mem-') as w:
  t=Path(w)/'tb.sv'; t.write_text(tb(p))
  src=str(HERE/'param_mem_shift_e.sv')
  if kind=='iverilog':
   exe=str(Path(w)/'a.out'); run(['iverilog','-g2012','-s','tb','-o',exe,src,str(t)],w); return rows(run(['vvp',exe],w))
  return rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(t)],w))
def main():
 run(['lake','build','Examples.«system-verilog».sem2.param_mem_shift_e.agree'])
 e=rows(run(['lake','env','lean','--run',str(HERE/'oracle.lean')]))
 assert len(e)==10, e
 print(f'E: {len(e)} rows')
 for k in ('iverilog','xrun'):
  if k=='xrun' and not shutil.which('xrun'): continue
  actual=sim(4,k)+sim(2,k)
  assert actual==e, (k,e,actual)
  print(f'{k}: {len(actual)} rows MATCH E')
if __name__=='__main__': main()
