#!/usr/bin/env python3
"""Differential receipt for wildcard case modes in canonical E."""
from pathlib import Path
import subprocess, tempfile, shutil, sys
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout
def rows(s): return [x.split()[1:] for x in s.splitlines() if x.startswith("ROW ")]
def main():
    with tempfile.NamedTemporaryFile(suffix='.json') as f:
        run(['python3','extractors/sv/extract.py','--top','always_comb_wildcard_case_memory_canonical_e','-o',f.name,str((HERE/'always_comb_wildcard_case_memory_canonical_e.sv').relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE/'always_comb_wildcard_case_memory_canonical_e.sv.json').read_bytes(): raise RuntimeError('stale envelope')
    run(['lake','build','Examples.«system-verilog».sem2.always_comb_wildcard_case_memory_canonical_e.agree'])
    expected=[['i=0','qz=0011','qx=0011'],['i=1','qz=0111','qx=0111'],['i=2','qz=1100','qx=0011'],['i=3','qz=0011','qx=0011']]
    tb='''module tb; logic [1:0] sel=0; logic [3:0] d=4'hc; wire [3:0] qz,qx; always_comb_wildcard_case_memory_canonical_e dut(sel,d,qz,qx); initial begin #1 $display("ROW i=0 qz=%b qx=%b",qz,qx); sel=2'b10; #1 $display("ROW i=1 qz=%b qx=%b",qz,qx); sel=2'bx0; #1 $display("ROW i=2 qz=%b qx=%b",qz,qx); sel=2'bzz; d=4'h5; #1 $display("ROW i=3 qz=%b qx=%b",qz,qx); $finish; end endmodule'''
    with tempfile.TemporaryDirectory() as w:
        src=str(HERE/'always_comb_wildcard_case_memory_canonical_e.sv'); t=Path(w)/'tb.sv'; t.write_text(tb); exe=str(Path(w)/'sim'); run(['iverilog','-g2012','-o',exe,src,str(t)],w); got=rows(run(['vvp',exe],w))
    if got != expected: raise RuntimeError(f'iverilog {got}')
    print('extractor: envelope regenerates byte-identically'); print('E: 4 wildcard case rows'); print('iverilog: 4 source rows MATCH')
    if shutil.which('xrun'):
        with tempfile.TemporaryDirectory() as w:
            src=str(HERE/'always_comb_wildcard_case_memory_canonical_e.sv'); t=Path(w)/'tb.sv'; t.write_text(tb); got=rows(run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(t)],w))
        if got != expected: raise RuntimeError(f'xrun {got}')
        print('xrun: 4 source rows MATCH')
if __name__=='__main__': main()
