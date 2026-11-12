#!/usr/bin/env python3
"""Differential receipt for parameter-sized unpacked input ports and generated storage."""
from pathlib import Path
import os, shutil, signal, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(args, cwd=ROOT):
 p=subprocess.Popen(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try: out,err=p.communicate(timeout=120)
 except subprocess.TimeoutExpired:
  os.killpg(p.pid, signal.SIGKILL); out,err=p.communicate(); raise RuntimeError("timeout")
 if p.returncode: raise RuntimeError(f"{args} failed:\n{out}{err}")
 return out
def rows(s): return [line.split()[1:] for line in s.splitlines() if line.startswith('ROW ')]
def tb(n):
 return f'''module tb; logic clk=0; logic [7:0] a [0:{n-1}]; wire [7:0] q;
param_mem_input_gen_e #(.W(8),.N({n})) dut(.clk(clk),.a(a),.q(q));
initial begin a[0]=0; a[1]=0; #1 $display("ROW N{n}_0 q=%b",q); a[0]=8'ha5; a[1]=8'h3c; clk=1; #1 $display("ROW N{n}_1 q=%b",q); clk=0; a[0]=8'h5a; a[1]=8'hc3; #1 $display("ROW N{n}_2 q=%b",q); clk=1; #1 $display("ROW N{n}_3 q=%b",q); clk=0; a[0]=8'hxx; a[1]=8'hxx; #1 $display("ROW N{n}_4 q=%b",q); $finish; end endmodule'''
def sim(n, kind):
 with tempfile.TemporaryDirectory(prefix='sv-input-mem-') as d:
  t=Path(d)/'tb.sv'; t.write_text(tb(n)); src=str(HERE/'param_mem_input_gen_e.sv')
  if kind=='iverilog':
   exe=str(Path(d)/'a.out'); run(['iverilog','-g2012','-s','tb','-o',exe,src,str(t)],d); return rows(run(['vvp',exe],d))
  return rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(t)],d))
def main():
 e=rows(run(['lake','env','lean','--run',str(HERE/'oracle.lean')]))
 assert len(e)==10, e
 print(f'E: {len(e)} rows')
 for k in ('iverilog','xrun'):
  if k=='xrun' and not shutil.which('xrun'): continue
  a=sim(4,k)+sim(2,k); assert a==e, (k,e,a); print(f'{k}: {len(a)} rows MATCH E')
if __name__=='__main__': main()
