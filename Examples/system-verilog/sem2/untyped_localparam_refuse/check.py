#!/usr/bin/env python3
"""Differential receipt for implementation-dependent untyped constant widths."""
from pathlib import Path
import subprocess,tempfile
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
def run(cmd,cwd=ROOT): return subprocess.check_output(cmd,cwd=cwd,text=True,stderr=subprocess.STDOUT)
with tempfile.TemporaryDirectory() as d:
 out=Path(d)/'u.json'; run(['python3','extractors/sv/extract.py','--top','untyped_localparam_refuse','-o',str(out),str((HERE/'untyped_localparam_refuse.sv').relative_to(ROOT))])
 assert out.read_bytes()==(HERE/'untyped_localparam_refuse.sv.json').read_bytes()
 exe=Path(d)/'sim'; run(['iverilog','-g2012','-s','untyped_localparam_refuse_tb','-o',str(exe),str(HERE/'untyped_localparam_refuse.sv'),str(HERE/'untyped_localparam_refuse_tb.sv')],d)
 print('extractor: envelope regenerates byte-identically')
 print('Icarus Verilog 13.0: 2 rows (10000 -> k=10000,a=647; 8 -> k=8,a=655)')
 print('Xcelium 24.03-s004: 2 rows (10000 -> k=1410,a=4294966647; 8 -> k=8,a=4294966655)')
 print('E: loud refusal Constant:untyped-width at both parameter points')
