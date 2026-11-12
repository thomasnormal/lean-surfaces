#!/usr/bin/env python3
from pathlib import Path
import os,shutil,signal,subprocess,tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(a,cwd=ROOT):
 p=subprocess.Popen(a,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try:o,e=p.communicate(timeout=120)
 except subprocess.TimeoutExpired: os.killpg(p.pid,signal.SIGKILL);o,e=p.communicate();raise RuntimeError('timeout')
 if p.returncode: raise RuntimeError(f'{a} failed:\n{o}{e}')
 return o
def rows(s): return [x.split()[1:] for x in s.splitlines() if x.startswith('ROW ')]
def tb(w): return f'''module tb; logic [3:0] x; wire [{w-1}:0] y; explicit_cast_e #(.W({w})) dut(.*); initial begin x=0; #1 $display("ROW {w}_0 y=%b",y); x=4'ha; #1 $display("ROW {w}_1 y=%b",y); x=4'bx; #1 $display("ROW {w}_2 y=%b",y); $finish; end endmodule'''
def sim(w,k):
 with tempfile.TemporaryDirectory(prefix='sv-cast-') as d:
  t=Path(d)/'tb.sv';t.write_text(tb(w));src=str(HERE/'explicit_cast_e.sv')
  if k=='iverilog': exe=str(Path(d)/'a.out');run(['iverilog','-g2012','-s','tb','-o',exe,src,str(t)],d);return rows(run(['vvp',exe],d))
  return rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(t)],d))
def main():
 e=rows(run(['lake','env','lean','--run',str(HERE/'oracle.lean')]))
 e=[[str(i), r[1]] for i,r in enumerate(e)]
 assert len(e)==6,e;print(f'E: {len(e)} rows')
 for k in ('iverilog','xrun'):
  if k=='xrun' and not shutil.which('xrun'):continue
  a=sim(8,k)+sim(2,k); a=[[str(i),r[1]] for i,r in enumerate(a)]; assert a==e,(k,e,a);print(f'{k}: {len(a)} rows MATCH E')
if __name__=='__main__':main()
