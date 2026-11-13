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
 if "E_REFUSAL Instance: module instance 'u_child' of 'edge_child_canonical_e' outside the canonical E memory route" not in e: raise RuntimeError(e)
 print('E: flat edge-child instance REFUSE (canonical hierarchy boundary)')
 src=str(HERE/'edge_child_instance_canonical_e.sv');tb=str(HERE/'edge_child_instance_canonical_e_tb.sv')
 with tempfile.TemporaryDirectory(prefix='sv-e-edge-child-') as w:
  exe=str(Path(w)/'sim');run(['iverilog','-g2012','-s','edge_child_instance_canonical_e_tb','-o',exe,src,tb],w);act=rows(run(['vvp',exe],w))
 if act != [['i=0','y=x'],['i=1','y=0']]: raise RuntimeError(act)
 print('Icarus Verilog 13.0: 2 source rows execute (E refusal is intentional)')
 if shutil.which('xrun'):
  with tempfile.TemporaryDirectory(prefix='sv-e-edge-child-xcelium-') as w:
   act=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','edge_child_instance_canonical_e_tb',src,tb],w))
  if act != [['i=0','y=x'],['i=1','y=0']]: raise RuntimeError(act)
  print('Xcelium 24.03-s004: 2 source rows execute (E refusal is intentional)')
if __name__=='__main__':main()
