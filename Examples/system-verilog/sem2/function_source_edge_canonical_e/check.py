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
def rows(o):return [x.split()[1:] for x in o.splitlines() if x.startswith('ROW ')]
def main():
 e=run(['lake','env','lean','--run',str(HERE/'oracle.lean')])
 expected=[['i=0','q=x'],['i=1','q=1'],['i=2','q=1'],['i=3','q=x'],
           ['i=4','q=x'],['i=5','q=x'],['i=6','q=x'],['i=7','q=0']]
 actual=rows(e)
 if actual != expected: raise RuntimeError(f'E rows: {actual!r}\n{e}')
 print('E: source-shaped edge function call 8 rows')
 src=str(HERE/'function_source_edge_canonical_e.sv');tb=str(HERE/'function_source_edge_canonical_e_tb.sv')
 with tempfile.TemporaryDirectory(prefix='sv-e-function-edge-') as w:
  exe=str(Path(w)/'sim');run(['iverilog','-g2012','-s','function_source_edge_canonical_e_tb','-o',exe,src,tb],w);act=rows(run(['vvp',exe],w))
 if act != expected: raise RuntimeError(f'Icarus: {act!r}')
 print('Icarus Verilog 13.0: 8 source rows MATCH E')
 if shutil.which('xrun'):
  with tempfile.TemporaryDirectory(prefix='sv-e-function-edge-xcelium-') as w:
   act=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','function_source_edge_canonical_e_tb',src,tb],w))
  if act != expected: raise RuntimeError(f'Xcelium: {act!r}')
  print('Xcelium 24.03-s004: 8 source rows MATCH E')
if __name__=='__main__':main()
