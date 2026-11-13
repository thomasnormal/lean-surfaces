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
 with tempfile.TemporaryDirectory(prefix='sv-e-generated-index-extract-') as w:
  out=Path(w)/'generated_array_index_canonical_e.sv.json'
  run(['python3','extractors/sv/extract.py','--top','generated_array_index_canonical_e',
       '--retain-proc-rewrites','-o',str(out),
       str((HERE/'generated_array_index_canonical_e.sv').relative_to(ROOT))])
  if out.read_bytes() != (HERE/'generated_array_index_canonical_e.sv.json').read_bytes():
   raise RuntimeError('envelope is not reproducible')
 print('extractor: retained generated index envelope regenerates byte-identically')
 e=run(['lake','build','Examples.«system-verilog».sem2.generated_array_index_canonical_e.agree'])
 e=run(['lake','env','lean','--run',str(HERE/'oracle.lean')])
 expected=[['i=0','y=xxxxxxxx'],['i=1','y=00000000'],['i=2','y=10100101'],
           ['i=3','y=xxxxxxxx'],['i=4','y=zzzzzzzz'],['i=5','y=00111100'],
           ['i=6','y=11111111'],['i=7','y=00000000'],['i=8','y=00000001']]
 actual=rows(e)
 if actual != expected: raise RuntimeError(f'E rows: {actual!r}\n{e}')
 print('E: generated fixed-array index 9 rows')
 src=str(HERE/'generated_array_index_canonical_e.sv');tb=str(HERE/'generated_array_index_canonical_e_tb.sv')
 with tempfile.TemporaryDirectory(prefix='sv-e-generated-index-') as w:
  exe=str(Path(w)/'sim');run(['iverilog','-g2012','-s','generated_array_index_canonical_e_tb','-o',exe,src,tb],w);act=rows(run(['vvp',exe],w))
 if act != expected: raise RuntimeError(f'Icarus: {act!r}')
 print('Icarus Verilog 13.0: 9 source rows MATCH E')
 if shutil.which('xrun'):
  with tempfile.TemporaryDirectory(prefix='sv-e-generated-index-xcelium-') as w:
   act=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','generated_array_index_canonical_e_tb',src,tb],w))
  if act != expected: raise RuntimeError(f'Xcelium: {act!r}')
  print('Xcelium 24.03-s004: 9 source rows MATCH E')
if __name__=='__main__':main()
