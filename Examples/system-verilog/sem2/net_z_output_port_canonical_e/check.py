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
 expected=[['i=0','q='+'x'*32,'z_out=z'],['i=1','q='+'x'*32,'z_out=z']]
 if exp != expected:raise RuntimeError(exp)
 print('E: 2 undriven-output-port rows MATCH')
 src=str(HERE/'net_z_output_port_canonical_e.sv');tb=str(HERE/'net_z_output_port_canonical_e_tb.sv')
 with tempfile.TemporaryDirectory(prefix='sv-e-net-z-port-') as w:
  exe=str(Path(w)/'sim');run(['iverilog','-g2012','-s','net_z_output_port_canonical_e_tb','-o',exe,src,tb],w);act=rows(run(['vvp',exe],w))
 if act!=exp:raise RuntimeError(act)
 print('Icarus Verilog 13.0: 2 rows MATCH E')
 if shutil.which('xrun'):
  status,details=probe_xcelium(); print(details)
  if status == 0:
   with tempfile.TemporaryDirectory(prefix='sv-e-net-z-port-xcelium-') as w:
    act=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','net_z_output_port_canonical_e_tb',src,tb],w))
   if act!=exp:raise RuntimeError(f'Xcelium {act} != {exp}')
   print(run(['xrun','-version']).strip()); print('Xcelium 24.03-s004: 2 rows MATCH E')
  elif status == 77: print('no Xcelium result: explicit license refusal')
  else: raise RuntimeError('Xcelium readiness probe failed')
 else: print('no Xcelium result: xrun unavailable')
if __name__=='__main__':main()
