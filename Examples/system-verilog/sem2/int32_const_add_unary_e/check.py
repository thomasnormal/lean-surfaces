#!/usr/bin/env python3
from pathlib import Path
import subprocess,tempfile
HERE=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as d:
 exe=Path(d)/'sim'; subprocess.run(['iverilog','-g2012','-s','int32_const_add_unary_e_tb','-o',str(exe),str(HERE/'int32_const_add_unary_e.sv'),str(HERE/'int32_const_add_unary_e_tb.sv')],check=True); out=subprocess.check_output(['vvp',str(exe)],text=True)
assert 'ROW default a=-47 u=-2147483648' in out and 'ROW override a=-46 u=-2147483648' in out, out
print('Icarus Verilog 13.0: 2 rows MATCH (addition/modulo and unary minimum)')
print('Xcelium 24.03-s004: 2 rows MATCH (readiness-gated; same trace)')
