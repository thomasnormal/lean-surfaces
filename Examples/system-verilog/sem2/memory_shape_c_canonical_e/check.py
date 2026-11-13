#!/usr/bin/env python3
from pathlib import Path
import os,signal,subprocess,tempfile,shutil,sys
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]; sys.path.insert(0,str(ROOT/'harness/sv')); from xcelium_probe import probe_xcelium
def run(a,cwd=ROOT):
 p=subprocess.Popen(a,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try:o,e=p.communicate(timeout=180)
 except subprocess.TimeoutExpired: os.killpg(p.pid,signal.SIGKILL);o,e=p.communicate();raise RuntimeError('timeout')
 if p.returncode:raise RuntimeError(o+e)
 return o
def rows(o):return [x.split()[1:] for x in o.splitlines() if x.startswith('ROW ')]
def main():
 exp=rows(run(['lake','env','lean','--run',str(HERE/'oracle.lean')]))
 if exp != [['i=0','q=xxxx'],['i=1','q=0001'],['i=2','q=0001'],['i=3','q=0011']]:raise RuntimeError(exp)
 print('E: 4 generated-array rows MATCH')
 src=str(HERE/'memory_shape_c_canonical_e.sv');tb=str(HERE/'memory_shape_c_canonical_e_tb.sv')
 with tempfile.TemporaryDirectory(prefix='sv-e-generated-memory-') as w:
  exe=str(Path(w)/'sim');run(['iverilog','-g2012','-s','memory_shape_c_canonical_e_tb','-o',exe,src,tb],w);act=rows(run(['vvp',exe],w))
 if act!=exp:raise RuntimeError(act)
 print('Icarus Verilog 13.0: 4 rows MATCH E')
 if shutil.which('xrun'):
  st,details=probe_xcelium();print(details)
  if st==0:
   with tempfile.TemporaryDirectory(prefix='sv-e-generated-memory-') as w:act=rows(run(['xrun','-sv','-q','-top','memory_shape_c_canonical_e_tb',src,tb],w))
   if act!=exp:raise RuntimeError(act)
   print('Xcelium 24.03-s004: 4 rows MATCH E')
if __name__=='__main__':main()
