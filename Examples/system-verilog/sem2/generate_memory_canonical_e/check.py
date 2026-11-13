#!/usr/bin/env python3
"""Compare canonical-E nested generate expansion with Icarus and Xcelium."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium  # noqa: E402


def run(args, cwd=ROOT):
    proc = subprocess.Popen(args, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    try:
        out, err = proc.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out, err


def rows(output):
    answer = []
    for line in output.splitlines():
        if line.startswith("ROW "):
            fields = line.split()
            answer.append([fields[1], fields[2], fields[3], fields[4]])
    return answer


def testbench(n):
    return f'''module generate_memory_canonical_e_tb;
  logic clk=0; logic [3:0] d=0; wire [3:0] q;
  generate_memory_canonical_e #(.W(4), .N({n})) dut(.clk(clk), .d(d), .q(q));
  task show(input integer i);
    #1 $display("ROW W=4 N={n} i=%0d q=%b", i, q);
  endtask
  initial begin
    d=1; clk=0; show(0);
    clk=1; show(1);
    d=3; clk=0; show(2);
    clk=1; show(3); $finish;
  end
endmodule
'''


def source_rows(simulator, n):
    src = str(HERE / "generate_memory_canonical_e.sv")
    with tempfile.TemporaryDirectory(prefix="sv-e-generate-memory-") as work:
        tb = Path(work) / "tb.sv"
        tb.write_text(testbench(n))
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "generate_memory_canonical_e_tb",
                 "-o", exe, src, str(tb)], work)
            output, _ = run(["vvp", exe], work)
        else:
            output, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                             "-top", "generate_memory_canonical_e_tb", src,
                             str(tb)], work)
    return rows(output)


def main():
    fd, name = tempfile.mkstemp(prefix="sv-e-generate-envelope-", suffix=".json")
    os.close(fd)
    envelope = Path(name)
    try:
        run(["python3", "extractors/sv/extract.py", "--top",
             "generate_memory_canonical_e", "--retain-loops",
             "--retain-proc-rewrites", "-o", str(envelope),
             str((HERE / "generate_memory_canonical_e.sv").relative_to(ROOT))])
        if envelope.read_bytes() != (HERE / "generate_memory_canonical_e.sv.json").read_bytes():
            raise RuntimeError("extractor envelope is stale")
    finally:
        envelope.unlink(missing_ok=True)

    run(["lake", "build",
         "Examples.«system-verilog».sem2.generate_memory_canonical_e.agree"])
    e_output, _ = run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")])
    expected = rows(e_output)
    if expected != [
        ["W=4", "N=2", "i=0", "q=xxxx"],
        ["W=4", "N=2", "i=1", "q=0001"],
        ["W=4", "N=2", "i=2", "q=0001"],
        ["W=4", "N=2", "i=3", "q=0011"],
        ["W=4", "N=1", "i=0", "q=xxxx"],
        ["W=4", "N=1", "i=1", "q=0001"],
        ["W=4", "N=1", "i=2", "q=0001"],
        ["W=4", "N=1", "i=3", "q=0011"],
    ]:
        raise RuntimeError(f"unexpected E rows: {expected}")
    print("extractor: envelope regenerates byte-identically")
    print("E: nested GenerateIf/GenerateFor expands source processes: 8 rows MATCH")

    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
    iverilog_version, iverilog_err = run(["iverilog", "-V"])
    print((iverilog_version + iverilog_err).splitlines()[0])
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            version, err = run(["xrun", "-version"])
            print((version + err).strip())
            simulators.append("xrun")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result: xrun unavailable")

    for simulator in simulators:
        actual = source_rows(simulator, 2) + source_rows(simulator, 1)
        if actual != expected:
            raise RuntimeError(f"{simulator}: E {expected} != source {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
