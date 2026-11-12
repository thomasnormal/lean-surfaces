#!/usr/bin/env python3
from pathlib import Path
import subprocess,tempfile,shutil
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3]
def run(a,cwd=ROOT):
 p=subprocess.run(a,cwd=cwd,text=True,capture_output=True)
 if p.returncode: raise RuntimeError(p.stdout+p.stderr)
 return p.stdout+p.stderr
def main():
 run(['lake','build','Examples.«system-verilog».sem2.mem_twostate_start_e.agree'])
 with tempfile.TemporaryDirectory(prefix='sv-two-state-') as d:
  tb=Path(d)/'tb.sv';tb.write_text('module tb; logic [7:0] d=0; wire [7:0] q; mem_twostate_start_e dut(.*); initial begin #1 $display("ROW q=%b",q); $finish; end endmodule')
  src=str(HERE/'mem_twostate_start_e.sv'); exe=str(Path(d)/'a.out'); out=run(['iverilog','-g2012','-s','tb','-o',exe,src,str(tb)],d); out=run(['vvp',exe],d); assert 'ROW q=00000000' in out
 print('E and Icarus Verilog 13.0 agree on 2-state memory startup: q=00000000')
 if shutil.which('xrun'): print('Xcelium source row is available through the pinned simulator')
if __name__=='__main__':main()
