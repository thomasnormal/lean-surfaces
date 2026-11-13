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
 expected_one=[['i=0','y=00000000'],['i=1','y=00000001'],['i=2','y=00010000'],['i=3','y=10100101'],['i=4','y=11111111'],['i=5','y=xxxxxxxx'],['i=6','y=zzzzzzzz'],['i=7','y=01011010']]
 expected=expected_one+expected_one
 print('extractor: envelope regenerates byte-identically'); print('E: 16 ordinary-route rows (N=1 and N=2)')
 tb='''module tb; parameter integer P=2; logic [7:0] x=8'h00; wire [7:0] y; parameterized_unpacked_storage_ordinary_e #(.N(P)) dut(.x(x),.y(y)); initial begin #1 $display("ROW i=0 y=%b",y); x=8'h01; #1 $display("ROW i=1 y=%b",y); x=8'h10; #1 $display("ROW i=2 y=%b",y); x=8'ha5; #1 $display("ROW i=3 y=%b",y); x=8'hff; #1 $display("ROW i=4 y=%b",y); x=8'hxx; #1 $display("ROW i=5 y=%b",y); x=8'hzz; #1 $display("ROW i=6 y=%b",y); x=8'h5a; #1 $display("ROW i=7 y=%b",y); $finish; end endmodule'''
 with tempfile.TemporaryDirectory() as w:
  src=str(HERE/'parameterized_unpacked_storage_ordinary_e.sv'); got=[]
  for p in (1,2):
   t=Path(w)/f'tb{p}.sv'; t.write_text(f'`define P {p}\n'+tb.replace('parameter integer P=2','parameter integer P=`P')); exe=str(Path(w)/f'sim{p}'); run(['iverilog','-g2012','-o',exe,src,str(t)],w); got.extend(rows(run(['vvp',exe],w)))
 if got!=expected: raise RuntimeError(f'iverilog {got}')
 print('iverilog: 16 source rows MATCH (N=1 and N=2)')
 if shutil.which('xrun'):
  with tempfile.TemporaryDirectory() as w:
   src=str(HERE/'parameterized_unpacked_storage_ordinary_e.sv'); got=[]
   for p in (1,2):
    t=Path(w)/f'tb{p}.sv'; t.write_text(f'`define P {p}\n'+tb.replace('parameter integer P=2','parameter integer P=`P')); got.extend(rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(t)],w)))
  if got!=expected: raise RuntimeError(f'xrun {got}')
  print('xrun: 16 source rows MATCH (N=1 and N=2)')
if __name__=='__main__': main()
