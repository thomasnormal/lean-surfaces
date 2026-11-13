#!/usr/bin/env python3
from pathlib import Path
import os, shutil, signal, subprocess, tempfile, sys
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium

def run(args, cwd=ROOT):
    p = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True)
    try: out, err = p.communicate(timeout=180)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); out, err = p.communicate()
        raise RuntimeError(f"{args[0]} timed out: {out}{err}")
    if p.returncode: raise RuntimeError(f"{args[0]} exited {p.returncode}: {out}{err}")
    return out

def rows(out): return [line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]
def main():
    expected = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if expected != [["N=1", "W=1"], ["N=8", "W=3"], ["N=16", "W=4"]]:
        raise RuntimeError(f"E rows: {expected}")
    print("E: 3 package-function constant rows MATCH")
    src = str(HERE / "constant_function_package_e.sv")
    tb = '''module tb; localparam integer N = `N; logic [7:0] y; constant_function_package_e #(.N(N)) dut(.y(y)); initial begin #1 $display("ROW N=%0d W=%0d y=%0d", N, dut.W, y); $finish; end endmodule'''
    for sim in (["iverilog"] if shutil.which("iverilog") else []):
        actual = []
        for n in (1, 8, 16):
            with tempfile.TemporaryDirectory(prefix="sv-e-constant-function-") as w:
                t = Path(w) / "tb.sv"; t.write_text("`define N %d\n" % n + tb)
                exe = str(Path(w) / "sim")
                run([sim, "-g2012", "-s", "tb", "-o", exe, src, str(t)], w)
                actual.extend(rows(run(["vvp", exe], w)))
        if actual != [["N=1", "W=1", "y=1"], ["N=8", "W=3", "y=3"], ["N=16", "W=4", "y=4"]]:
            raise RuntimeError(f"{sim}: {actual}")
        print("Icarus Verilog 13.0: 3 rows MATCH E")
    if shutil.which("xrun"):
        status, details = probe_xcelium(); print(details)
        if status == 0:
            actual = []
            for n in (1, 8, 16):
                with tempfile.TemporaryDirectory(prefix="sv-e-constant-function-") as w:
                    t = Path(w) / "tb.sv"; t.write_text("`define N %d\n" % n + tb)
                    actual.extend(rows(run(["xrun", "-sv", "-q", "-define", f"N={n}", "-top", "tb", src, str(t)], w)))
            if actual != [["N=1", "W=1", "y=1"], ["N=8", "W=3", "y=3"], ["N=16", "W=4", "y=4"]]:
                raise RuntimeError(f"xrun: {actual}")
            print("Xcelium 24.03-s004: 3 rows MATCH E")
        elif status == 77: print("no Xcelium result: explicit license refusal")
        else: raise RuntimeError("Xcelium readiness failed")
if __name__ == "__main__": main()
