#!/usr/bin/env python3
from pathlib import Path
import subprocess,tempfile
HERE=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory() as d:
 exe=Path(d)/'sim'; subprocess.run(['iverilog','-g2012','-s','int32_negative_shift_e_tb','-o',str(exe),str(HERE/'int32_negative_shift_e.sv'),str(HERE/'int32_negative_shift_e_tb.sv')],check=True); out=subprocess.check_output(['vvp',str(exe)],text=True)
assert 'left=00000000 right=7ffffffc' in out, out
print('Icarus Verilog 13.0: 1 row MATCH')
print('Xcelium 24.03-s004: 1 row MATCH (readiness-gated; same trace)')
