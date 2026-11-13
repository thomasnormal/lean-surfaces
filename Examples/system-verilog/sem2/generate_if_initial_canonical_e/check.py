#!/usr/bin/env python3
"""Compare generated initial-process branches with Icarus and Xcelium."""
from pathlib import Path
import os, shutil, signal, subprocess, sys, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium  # noqa: E402

def run(args, cwd=ROOT):
    p = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); out, err = p.communicate()
        raise RuntimeError(f"{args[0]} timed out: {out}{err}")
    if p.returncode: raise RuntimeError(f"{args[0]} exited {p.returncode}: {out}{err}")
    return out

def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]

def tb(n):
    return f'''module tb; wire q; generate_if_initial_canonical_e #(.N({n})) dut(.q(q)); initial begin #1 $display("ROW n={n} q=%b", q); $finish; end endmodule\n'''

def main():
    fd, name = tempfile.mkstemp(prefix="sv-generate-initial-", suffix=".json"); os.close(fd)
    try:
        run(["python3", "extractors/sv/extract.py", "--top", "generate_if_initial_canonical_e", "-o", name,
             str((HERE / "generate_if_initial_canonical_e.sv").relative_to(ROOT))])
        if Path(name).read_bytes() != (HERE / "generate_if_initial_canonical_e.sv.json").read_bytes(): raise RuntimeError("stale envelope")
    finally: Path(name).unlink(missing_ok=True)
    run(["lake", "build", "Examples.«system-verilog».sem2.generate_if_initial_canonical_e.agree"])
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if expected != [["n=1", "q=0"], ["n=0", "q=1"]]: raise RuntimeError(expected)
    print("extractor: envelope regenerates byte-identically")
    print("E: 2 generated-branch initial rows MATCH")
    sims = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium(); print(details)
        if status == 0: sims.append("xrun")
        elif status != 77: raise RuntimeError("Xcelium readiness probe failed")
    for sim in sims:
        actual=[]
        for n in (1,0):
            with tempfile.TemporaryDirectory(prefix="sv-generate-initial-") as work:
                src=str(HERE / "generate_if_initial_canonical_e.sv"); t=Path(work)/"tb.sv"; t.write_text(tb(n))
                if sim == "iverilog":
                    exe=str(Path(work)/"sim"); run(["iverilog","-g2012","-s","tb","-o",exe,src,str(t)],work); out=run(["vvp",exe],work)
                else: out=run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",src,str(t)],work)
                actual.extend(rows(out))
        if actual != expected: raise RuntimeError(f"{sim}: {actual} != {expected}")
        print(f"{sim}: {len(actual)} rows MATCH E")
if __name__ == "__main__": main()
