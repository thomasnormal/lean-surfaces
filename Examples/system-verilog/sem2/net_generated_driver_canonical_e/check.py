#!/usr/bin/env python3
from pathlib import Path
import os,signal,subprocess,tempfile,shutil,sys
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
sys.path.insert(0, str(ROOT / 'harness/sv'))
from xcelium_probe import probe_xcelium
def run(a,cwd=ROOT):
 p=subprocess.Popen(a,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
 try:o,e=p.communicate(timeout=180)
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);o,e=p.communicate();raise RuntimeError('timeout')
 if p.returncode:raise RuntimeError(o+e)
 return o
def rows(o):return [x.split()[1:] for x in o.splitlines() if x.startswith('ROW ')]
def main():
 exp=rows(run(['lake','env','lean','--run',str(HERE/'oracle.lean')]))
 expected=[['i=0','q='+'x'*32,'z_out=0'],['i=1','q='+'x'*32,'z_out=0']]
 if exp != expected:raise RuntimeError(exp)
 print('E: 2 generated-driver rows MATCH')
 src=str(HERE/'net_generated_driver_canonical_e.sv');tb=str(HERE/'net_generated_driver_canonical_e_tb.sv')
 for sim in ('iverilog','xrun'):
  if sim == 'xrun' and not shutil.which('xrun'): continue
  status=0
  if sim == 'xrun': status,_=probe_xcelium()
  if sim == 'xrun' and status != 0: print('no Xcelium result: explicit license refusal' if status == 77 else 'no Xcelium result: unavailable'); continue
  with tempfile.TemporaryDirectory(prefix='sv-e-net-generated-') as w:
   if sim == 'iverilog':
    exe=str(Path(w)/'sim');run(['iverilog','-g2012','-s','net_generated_driver_canonical_e_tb','-o',exe,src,tb],w);act=rows(run(['vvp',exe],w))
   else: act=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','net_generated_driver_canonical_e_tb',src,tb],w))
  if act!=exp:raise RuntimeError(f'{sim}: {act} != {exp}')
  print(('Icarus Verilog 13.0' if sim == 'iverilog' else 'Xcelium 24.03-s004') + ': 2 rows MATCH E')
if __name__=='__main__':main()
