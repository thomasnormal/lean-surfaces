#!/usr/bin/env python3
"""Clean-room regression for SVA inside literal sizing (IEEE 1800-2023 §16.9.3)."""
from pathlib import Path
import subprocess
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def main():
 p=subprocess.run(['lake','build','Examples.«system-verilog».sem2.sva_inside_e.agree'],cwd=ROOT,text=True,capture_output=True)
 if p.returncode: raise RuntimeError(p.stdout+p.stderr)
 print('SVA inside 4\'b0001 retained as a four-bit literal; no simulator oracle is claimed for this assertion receipt')
if __name__=='__main__': main()
