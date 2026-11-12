#!/usr/bin/env python3
"""Differential receipt for a parameter-width packed register RHS."""
from pathlib import Path
import os, shutil, signal, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(args,cwd=ROOT):
 p=subprocess.Popen(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try:o,e=p.communicate(timeout=120)
 except subprocess.TimeoutExpired: os.killpg(p.pid,signal.SIGKILL); o,e=p.communicate(); raise RuntimeError('timeout')
 if p.returncode: raise RuntimeError(f'{args} failed:\n{o}{e}')
 return o
def rows(s): return [x.split()[1:] for x in s.splitlines() if x.startswith('ROW ')]
def tb(n): return f'''module tb; logic clk=0,v=0; wire [{n-1}:0] q; packed_rhs_e #(.N({n})) dut(.*);
initial begin #1 $display("ROW N{n}_0 q=%b",q); v=1; clk=1; #1 $display("ROW N{n}_1 q=%b",q); clk=0; v=0; #1 $display("ROW N{n}_2 q=%b",q); clk=1; v=1; #1 $display("ROW N{n}_3 q=%b",q); clk=0; v=1'bx; #1 $display("ROW N{n}_4 q=%b",q); $finish; end endmodule'''
def sim(n,k):
 with tempfile.TemporaryDirectory(prefix='sv-packed-rhs-') as d:
  t=Path(d)/'tb.sv'; t.write_text(tb(n)); src=str(HERE/'packed_rhs_e.sv')
  if k=='iverilog': exe=str(Path(d)/'a.out'); run(['iverilog','-g2012','-s','tb','-o',exe,src,str(t)],d); return rows(run(['vvp',exe],d))
  return rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(t)],d))
def main():
 e=rows(run(['lake','env','lean','--run',str(HERE/'oracle.lean')]))
 assert len(e)==10,e; print(f'E: {len(e)} rows')
 for k in ('iverilog','xrun'):
  if k=='xrun' and not shutil.which('xrun'): continue
  a=sim(8,k)+sim(4,k); assert a==e,(k,e,a); print(f'{k}: {len(a)} rows MATCH E')
if __name__=='__main__': main()
