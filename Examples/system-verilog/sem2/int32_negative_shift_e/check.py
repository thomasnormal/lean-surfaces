#!/usr/bin/env python3
"""Check negative int shifts against E and both pinned simulators."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import sys
import tempfile
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium
EXPECTED = [
    ("N=8", "left=00000000", "logical=7ffffffc", "arithmetic=fffffffc", "logical_param=7ffffffc", "arithmetic_param=fffffffc"),
    ("N=16", "left=00000000", "logical=7ffffffc", "arithmetic=fffffffc", "logical_param=7ffffff8", "arithmetic_param=fffffff8"),
]
def run(args, cwd=ROOT):
    proc=subprocess.Popen(args,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    try: out,err=proc.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        try: os.killpg(proc.pid,signal.SIGKILL)
        except ProcessLookupError: pass
        out,err=proc.communicate(); raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode: raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out
def rows(out): return [tuple(line.split()[1:]) for line in out.splitlines() if line.startswith("ROW ")]
def main():
    with tempfile.TemporaryDirectory(prefix="sv-negative-shift-") as work:
        env=Path(work)/"env.json"
        run([sys.executable,str(ROOT/"extractors/sv/extract.py"),"--top","int32_negative_shift_e","-o",str(env),str((HERE/"int32_negative_shift_e.sv").relative_to(ROOT))])
        if env.read_bytes() != (HERE/"int32_negative_shift_e.sv.json").read_bytes(): raise RuntimeError("envelope is not reproducible")
        print("extractor: envelope regenerates byte-identically")
        sources=[str(HERE/"int32_negative_shift_e.sv"),str(HERE/"int32_negative_shift_e_tb.sv")]
        exe=Path(work)/"sim"; run(["iverilog","-g2012","-s","int32_negative_shift_e_tb","-o",str(exe)]+sources,work)
        actual=rows(run(["vvp",str(exe)],work))
        if actual != EXPECTED: raise RuntimeError(f"Icarus: expected {EXPECTED}, got {actual}")
        print("Icarus Verilog 13.0: 2 rows MATCH E")
        if shutil.which("xrun"):
            status,details=probe_xcelium(); print(details)
            if status == 0:
                out=run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","int32_negative_shift_e_tb"]+sources,work)
                actual=rows(out)
                if actual != EXPECTED: raise RuntimeError(f"Xcelium: expected {EXPECTED}, got {actual}")
                print("Xcelium 24.03-s004: 2 rows MATCH E")
            elif status == 77: print("no Xcelium result: explicit license refusal")
            else: raise RuntimeError("Xcelium readiness probe failed")
        else: print("no Xcelium result: xrun unavailable")
        run(["lake","env","lean",str(HERE/"agree.lean")])
        print("E: 2 parameter rows MATCH (>> and >>>, including negative operands)")
if __name__ == "__main__": main()
