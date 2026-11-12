#!/usr/bin/env python3
"""Differential receipt for a fixed unpacked array with a block-local loop variable."""
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
def tb(w):
 return f'''module tb; logic clk=0; logic [{w-1}:0] d=0; logic [1:0] idx=0; wire [{w-1}:0] q;
fixed_mem_local_loop_e #(.W({w})) dut(.*);
initial begin #1 $display("ROW W{w}_0 q=%b",q); d={w}'h{('a5' if w == 8 else 'a')}; idx=2'd1; clk=1; #1 $display("ROW W{w}_1 q=%b",q); clk=0; d={w}'h{('5a' if w == 8 else '5')}; idx=2'bxx; #1 $display("ROW W{w}_2 q=%b",q); clk=1; #1 $display("ROW W{w}_3 q=%b",q); clk=0; d={w}'h0; idx=2'bxx; #1 $display("ROW W{w}_4 q=%b",q); $finish; end endmodule'''
def sim(w, kind):
 with tempfile.TemporaryDirectory(prefix='sv-fixed-mem-') as d:
  t=Path(d)/'tb.sv'; t.write_text(tb(w)); src=str(HERE/'fixed_mem_local_loop_e.sv')
  if kind=='iverilog':
   exe=str(Path(d)/'a.out'); run(['iverilog','-g2012','-s','tb','-o',exe,src,str(t)],d); return rows(run(['vvp',exe],d))
  return rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(t)],d))
def main():
 e=rows(run(['lake','env','lean','--run',str(HERE/'oracle.lean')]))
 assert len(e)==10, e
 print(f'E: {len(e)} rows')
 for k in ('iverilog','xrun'):
  if k=='xrun' and not shutil.which('xrun'): continue
  a=sim(8,k)+sim(4,k); assert a==e, (k,e,a); print(f'{k}: {len(a)} rows MATCH E')
if __name__=='__main__': main()
