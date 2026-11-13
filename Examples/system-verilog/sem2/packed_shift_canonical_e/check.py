#!/usr/bin/env python3
from pathlib import Path
import os,signal,subprocess,tempfile,shutil
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(a,cwd=ROOT):
 p=subprocess.Popen(a,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try:o,e=p.communicate(timeout=180)
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);o,e=p.communicate();raise RuntimeError('timeout')
 if p.returncode:raise RuntimeError(o+e)
 return o
def rows(o):return sorted([x.split()[1:] for x in o.splitlines() if x.startswith('ROW ')], key=lambda x:(x[0],x[1]))
def main():
 exp=rows(run(['lake','env','lean','--run',str(HERE/'oracle.lean')]))
 expected=[['N=4','i=0','q=xxxx'],['N=4','i=1','q=xxx1'],['N=4','i=2','q=xxx1'],['N=4','i=3','q=xx11'],['N=8','i=0','q=xxxxxxxx'],['N=8','i=1','q=xxxxxxx1'],['N=8','i=2','q=xxxxxxx1'],['N=8','i=3','q=xxxxxx11']]
 if exp != expected: raise RuntimeError(exp)
 print('E: 8 packed-register shift rows MATCH')
 src=str(HERE/'packed_shift_canonical_e.sv');tb=str(HERE/'packed_shift_canonical_e_tb.sv')
 with tempfile.TemporaryDirectory(prefix='sv-e-packed-shift-') as w:
  exe=str(Path(w)/'sim');run(['iverilog','-g2012','-s','packed_shift_canonical_e_tb','-o',exe,src,tb],w);act=rows(run(['vvp',exe],w))
 if act!=exp: raise RuntimeError(act)
 print('Icarus Verilog 13.0: 8 rows MATCH E')
 if shutil.which('xrun'):
  with tempfile.TemporaryDirectory(prefix='sv-e-packed-shift-xcelium-') as w:
   act=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','packed_shift_canonical_e_tb',src,tb],w))
  if act!=exp: raise RuntimeError(act)
  print('Xcelium 24.03-s004: 8 rows MATCH E')
if __name__=='__main__':main()
