#!/usr/bin/env python3
"""yosys_frontend.py : which of the register's "not synthesizable" constructs (principle P-SYNTHESIZABLE) does the
scored frontend, Yosys `read_verilog -sv`, actually fail to read?  One tiny module per construct; prints
READS / REJECTS (first error line) for each, plus slang's verdict (the full driver) so a row can be told apart from
"slang rejects it too".  Output is the table of docs/sv-tools-split-audit.md section 5.

    python3 harness/sv/tools_split_audit/yosys_frontend.py [--yosys PATH]
"""
import os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
YOSYS = "yosys"
if "--yosys" in sys.argv:
    YOSYS = sys.argv[sys.argv.index("--yosys") + 1]

CASES = [
    ("class declaration", """module t(input logic a, output logic y);
  class C; int x; function int f(); return x; endfunction endclass
  assign y = a;
endmodule"""),
    ("queue variable", """module t(input logic a, output logic y);
  int q[$];
  assign y = a;
endmodule"""),
    ("dynamic array variable", """module t(input logic a, output logic y);
  int d[];
  assign y = a;
endmodule"""),
    ("associative array variable", """module t(input logic a, output logic y);
  int m[int];
  assign y = a;
endmodule"""),
    ("string variable", """module t(input logic a, output logic y);
  string s;
  assign y = a;
endmodule"""),
    ("string parameter (typed)", """module t #(parameter string S = "ab") (input logic a, output logic y);
  assign y = a;
endmodule"""),
    ("real variable", """module t(input logic a, output logic y);
  real r;
  assign y = a;
endmodule"""),
    ("real constant in a localparam", """module t(input logic [7:0] a, output logic [7:0] y);
  localparam real R = 2.5;
  localparam integer K = $rtoi(R * 2.0);
  assign y = a + K;
endmodule"""),
    ("fork/join", """module t(input logic a, output logic y);
  initial begin fork y = a; join end
endmodule"""),
    ("program block", """program p; endprogram
module t(input logic a, output logic y);
  assign y = a;
endmodule"""),
    ("explicit port expression .q(y)", """module t (a, .q(y));
  input a;
  output y;
  logic y;
  assign y = a;
endmodule"""),
]

def sh(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=60)
    return p.returncode, p.stdout + p.stderr

def slang_verdict(path, cwd):
    rc, out = sh(["python3.12", os.path.join(HERE, "slangdiag.py"), "--top", "t", path], cwd)
    errs = [l for l in out.splitlines() if ": error:" in l]
    return "error: " + re.sub(r"^.*?error: ", "", errs[0])[:70] if errs else "clean"

with tempfile.TemporaryDirectory() as d:
    print(f"{'construct':34} {'Yosys read_verilog -sv':44} slang")
    for name, src in CASES:
        path = os.path.join(d, "t.sv")
        open(path, "w").write(src + "\n")
        rc, out = sh([YOSYS, "-q", "-p", "read_verilog -sv t.sv; hierarchy -check -top t"], d)
        err = [l for l in out.splitlines() if "ERROR" in l or "syntax error" in l]
        verdict = "READS" if rc == 0 else "REJECTS " + re.sub(r"^.*ERROR: ", "", err[0])[:60] if err else f"REJECTS rc={rc}"
        print(f"{name:34} {verdict:44} {slang_verdict(path, d)}")
