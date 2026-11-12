#!/usr/bin/env python3
"""Extractor option receipt: -D selects source branches and $error stays named/loud."""
from pathlib import Path
import json, subprocess
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def run(a):
 p=subprocess.run(a,cwd=ROOT,text=True,capture_output=True)
 if p.returncode: raise RuntimeError(p.stderr)
 return p.stdout
def main():
 src='Examples/system-verilog/sem2/extractor_options_e/extractor_options_e.sv'
 en=HERE/'enabled.json'; dis=HERE/'disabled.json'
 run(['python3','extractors/sv/extract.py','--top','extractor_options_e','-D','ENABLED','-o',str(en),src])
 run(['python3','extractors/sv/extract.py','--top','extractor_options_e','-o',str(dis),src])
 je=json.loads(en.read_text()); jd=json.loads(dis.read_text())
 pe=je['design']['modules'][0]['processes']; pd=jd['design']['modules'][0]['processes']
 assert pe[0]['kind']=='Initial' and pe[0]['body']['name']=='$error'
 assert len(pd)==1 and pd[0]['value']['kind']=='Literal'
 run(['lake','build','Examples.«system-verilog».sem2.extractor_options_e.agree'])
 print('defines: ENABLED and disabled branches MATCH envelope')
 print('SysCall:$error: retained and loud by name; no oracle result is claimed for the refused initial task')
if __name__=='__main__': main()
