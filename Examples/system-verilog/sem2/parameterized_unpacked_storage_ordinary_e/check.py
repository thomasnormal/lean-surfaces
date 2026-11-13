#!/usr/bin/env python3
"""Ordinary canonical-E receipt for parameter-sized unpacked storage."""
from pathlib import Path
import subprocess, tempfile, shutil
HERE = Path(__file__).resolve().parent; ROOT = HERE.parents[3]
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def rows(s): return [x.split()[1:] for x in s.splitlines() if x.startswith('ROW ')]
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  run(['python3','extractors/sv/extract.py','--top','parameterized_unpacked_storage_ordinary_e','-o',f.name,str((HERE/'parameterized_unpacked_storage_ordinary_e.sv').relative_to(ROOT))])
  if Path(f.name).read_bytes() != (HERE/'parameterized_unpacked_storage_ordinary_e.sv.json').read_bytes(): raise RuntimeError('stale envelope')
 run(['lake','build','Examples.«system-verilog».sem2.parameterized_unpacked_storage_ordinary_e.agree'])
 expected=[['i=0','y=00010000'],['i=1','y=10100101']]
 print('extractor: envelope regenerates byte-identically'); print('E: 2 ordinary-route rows')
 tb='''module tb; logic [7:0] x=8'h10; wire [7:0] y; parameterized_unpacked_storage_ordinary_e #(.N(2)) dut(.x(x),.y(y)); initial begin #1 $display("ROW i=0 y=%b",y); x=8'ha5; #1 $display("ROW i=1 y=%b",y); $finish; end endmodule'''
 with tempfile.TemporaryDirectory() as w:
  src=str(HERE/'parameterized_unpacked_storage_ordinary_e.sv'); t=Path(w)/'tb.sv'; t.write_text(tb); exe=str(Path(w)/'sim'); run(['iverilog','-g2012','-o',exe,src,str(t)],w); got=rows(run(['vvp',exe],w))
 if got!=expected: raise RuntimeError(f'iverilog {got}')
 print('iverilog: 2 source rows MATCH')
 if shutil.which('xrun'):
  with tempfile.TemporaryDirectory() as w:
   src=str(HERE/'parameterized_unpacked_storage_ordinary_e.sv'); t=Path(w)/'tb.sv'; t.write_text(tb); got=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(t)],w))
  if got!=expected: raise RuntimeError(f'xrun {got}')
  print('xrun: 2 source rows MATCH')
if __name__=='__main__': main()
