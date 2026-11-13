#!/usr/bin/env python3
from pathlib import Path
import os,signal,subprocess,tempfile,shutil
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(a,cwd=ROOT,allow_fail=False):
 p=subprocess.Popen(a,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try:o,e=p.communicate(timeout=180)
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);o,e=p.communicate();raise RuntimeError('timeout')
 if p.returncode and not allow_fail:raise RuntimeError(o+e)
 return p.returncode,o,e
def rows(o):return [x.split()[1:] for x in o.splitlines() if x.startswith('ROW ')]
def main():
 rc,o,e=run(['lake','env','lean',str(HERE/'probe.lean')],allow_fail=True)
 expected='envelope: module: GenerateIf: UnpackedDecl: unknown generate member kind "UnpackedDecl"'
 if rc == 0 or expected not in (o + e): raise RuntimeError(f'rc={rc}\n{o}\n{e}')
 print('E loader: GenerateIf/UnpackedDecl REFUSE (source-shaped envelope boundary)')
 src=str(HERE/'generate_if_unpacked_array_canonical_e.sv');tb=str(HERE/'generate_if_unpacked_array_canonical_e_tb.sv')
 with tempfile.TemporaryDirectory(prefix='sv-e-generate-if-array-') as w:
  exe=str(Path(w)/'sim');run(['iverilog','-g2012','-s','generate_if_unpacked_array_canonical_e_tb','-o',exe,src,tb],w);_,o,_=run(['vvp',exe],w);act=rows(o)
 if act != [['i=0','y=00000000'],['i=1','y=10100101']]: raise RuntimeError(act)
 print('Icarus Verilog 13.0: 2 source rows execute (E loader refusal is intentional)')
 if shutil.which('xrun'):
  with tempfile.TemporaryDirectory(prefix='sv-e-generate-if-array-xcelium-') as w:
   _,o,_=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','generate_if_unpacked_array_canonical_e_tb',src,tb],w);act=rows(o)
  if act != [['i=0','y=00000000'],['i=1','y=10100101']]: raise RuntimeError(act)
  print('Xcelium 24.03-s004: 2 source rows execute (E loader refusal is intentional)')
if __name__=='__main__':main()
