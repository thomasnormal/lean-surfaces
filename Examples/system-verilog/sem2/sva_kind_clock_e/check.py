#!/usr/bin/env python3
from pathlib import Path
import subprocess
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3]
def main():
 p=subprocess.run(['lake','build','Examples.«system-verilog».sem2.sva_kind_clock_e.agree'],cwd=ROOT,text=True,capture_output=True)
 if p.returncode: raise RuntimeError(p.stdout+p.stderr)
 print('restrict property and posedge clock retained from Slang metadata; no source-text regex classification')
if __name__=='__main__':main()
