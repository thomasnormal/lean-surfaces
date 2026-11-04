#!/usr/bin/env python3.12
"""Create cases/<id>/{dut.sv,case.json}: fixtures copied from the repo (cases2.json rows) and
hand-written probes. case.json = {name, top, signals, stimulus, clock?, params?, row, rows, claim}."""
import json, os, shutil, itertools, sys
WT = os.environ["WT"]
HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("AUDIT_DIR") or os.path.join(HERE, "out")
CASES = os.path.join(DATA, "cases")
os.makedirs(CASES, exist_ok=True)
c2 = {r["name"]: r for r in json.load(open(f"{WT}/harness/sv/cases2.json"))["cases"]}

def put(cid, files, case):
    d = os.path.join(CASES, cid)
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    for fn, text in files.items():
        open(os.path.join(d, fn), "w").write(text)
    case = dict(case); case["name"] = cid
    json.dump(case, open(os.path.join(d, "case.json"), "w"), indent=1)

def fixture(row, as_id=None):
    r = c2[row]
    SIGNAL_FIX = {"pi_explicit": ["y"]}   # the explicit port expression .q(y) has no `dut.q` to sample
    ex = r["example"].split("/")[1]
    src = open(f"{WT}/Examples/system-verilog/sem2/{ex}/{ex}.sv").read()
    # the fixture headers are comments that mention tools by name ("// Verilator 5.042 ..." is read by
    # Verilator as a pragma): the svGolf source gate strips comments, so do the same here
    src = "".join(l for l in src.splitlines(True) if not l.lstrip().startswith("//"))
    case = {k: r[k] for k in ("top", "signals", "stimulus", "clock", "params") if k in r}
    if row in SIGNAL_FIX: case["signals"] = SIGNAL_FIX[row]
    case["row"] = row
    case["refusal"] = r.get("refusal")
    put(as_id or row, {"dut.sv": src}, case)

def bits(n, w):
    return format(n, "0%db" % w)

# ---- fixtures from the register's evidence rows
for row in ["vg_initc", "vg_initf", "vg_initq", "vh_initcomb",
            "vg_init", "vg_initn", "vh_init", "pi_in_init", "pi_in_init2", "pi_in_top", "pi_in_net",
            "fold_ovr", "fold_uwovr", "fold_ovrw",
            "rbw_comb", "rbw_held", "rbw_bits", "rbw_cond", "rbw_case_item", "rbw_dyn", "rbw_part",
            "rbw_nested", "rbw_child",
            "acg_alias_assign", "acg_alias_port", "acg_alias_chain", "acg_alias_not", "acg_alias_bits",
            "acg_alias_hier", "acg_alias_thru", "acg_alias_wr", "acg_alias_copy",
            "drv_pw_lit", "drv_pw_gv", "drv_pw_par_k0", "drv_pw_ff", "drv_mix_k0",
            "pi_explicit", "fold_ovrw_n1", "fold_ovrw_n24", "fold_uwovr_n0", "fold_sho_n40", "fold_sho_n1"]:
    fixture(row)

# ---- hand-written probes
def two(sig_a, sig_b, wa, wb):
    return [{sig_a: bits(i, wa), sig_b: bits(j, wb)} for i in range(2**wa) for j in range(2**wb)]

put("ctx_pq", {"dut.sv": """module ctx_child(input logic [3:0] i, output logic [3:0] o);
  assign o = i;
endmodule
module ctx_pq(input logic [1:0] p, input logic [1:0] q, output logic [3:0] y, output logic [3:0] z);
  ctx_child u (.i(p + q), .o(y));
  ctx_child v (.i(~p), .o(z));
endmodule
"""}, {"top": "ctx_pq", "signals": ["p", "q", "y", "z"], "stimulus": two("p", "q", 2, 2),
       "claim": "p+q and ~p into a 4-bit port: LRM context-width (0101 for p=2,q=3; ~p=1110) vs self-determined zero-pad (0001; 0010)"})
put("ctx_const40", {"dut.sv": """module ctx40_child(input logic [39:0] i, output logic [39:0] o);
  assign o = i;
endmodule
module ctx_const40(input logic d, output logic [39:0] y);
  ctx40_child u (.i(-1), .o(y));
endmodule
"""}, {"top": "ctx_const40", "signals": ["y"], "stimulus": [{"d": "0"}],
       "claim": "INT-class constant -1 into a 40-bit port: sign-extend (40 ones) vs 32-bit zero-pad"})

put("pr_init_fpga", {"dut.sv": """module pr_init_fpga(input logic clk, input logic d, output logic q);
  logic r = 1'b0;
  always_ff @(posedge clk) r <= d;
  assign q = r;
endmodule
"""}, {"top": "pr_init_fpga", "clock": "clk", "signals": ["q"],
       "stimulus": [{"d": "1"}, {"d": "0"}, {"d": "1"}, {"d": "1"}],
       "claim": "the common FPGA idiom: initialized variable, ONE always_ff writer"})
put("pr_init_comb_plain", {"dut.sv": """module pr_init_comb_plain(input logic [1:0] a, output logic [1:0] y);
  logic [1:0] t = 2'b10;
  always @* t = a;
  assign y = t;
endmodule
"""}, {"top": "pr_init_comb_plain", "signals": ["y"], "stimulus": [{"a": "01"}, {"a": "10"}, {"a": "11"}, {"a": "00"}],
       "claim": "control: initialized variable, plain always @* writer (no always_comb)"})

put("dc_port_net_init", {"dut.sv": """module dc_port_net_init(input logic [7:0] a, output wire [7:0] y = 8'd3);
endmodule
"""}, {"top": "dc_port_net_init", "signals": ["y"], "stimulus": [{"a": "00000001"}, {"a": "11111111"}],
       "claim": "output wire with an initializer = a continuous driver in disguise (IEEE 6.5/10.3.1)"})
put("dc_port_net_init2", {"dut.sv": """module dc_port_net_init2(input logic [7:0] a, output wire [7:0] y = 8'd3);
  assign y = a;
endmodule
"""}, {"top": "dc_port_net_init2", "signals": ["y"], "stimulus": [{"a": "00000001"}, {"a": "11111111"}],
       "claim": "output wire with an initializer AND an assign = two continuous drivers"})
for tag, esc in [("a", r"\a"), ("v", r"\v"), ("f", r"\f"), ("n", r"\n"), ("x41", r"\x41"), ("o101", r"\101")]:
    put("lit_str_" + tag, {"dut.sv": 'module lit_str_%s(input logic d, output logic [7:0] y);\n  assign y = "%s";\nendmodule\n' % (tag, esc)},
        {"top": "lit_str_" + tag, "signals": ["y"], "stimulus": [{"d": "0"}],
         "claim": 'string literal "%s" assigned to 8 bits' % esc})
put("lit_str_nonlatin", {"dut.sv": 'module lit_str_nonlatin(input logic d, output logic [7:0] y);\n  assign y = "é";\nendmodule\n'},
    {"top": "lit_str_nonlatin", "signals": ["y"], "stimulus": [{"d": "0"}], "claim": "latin-1 e-acute (2 UTF-8 bytes) in an 8-bit target"})
put("lit_str_nonlatin2", {"dut.sv": 'module lit_str_nonlatin2(input logic d, output logic [15:0] y);\n  assign y = "é";\nendmodule\n'},
    {"top": "lit_str_nonlatin2", "signals": ["y"], "stimulus": [{"d": "0"}], "claim": "e-acute in a 16-bit target (UTF-8 bytes c3a9)"})

# combinational loops
put("loop_osc", {"dut.sv": "module loop_osc(input logic d, output logic y);\n  logic a;\n  assign a = ~a;\n  assign y = a;\nendmodule\n"},
    {"top": "loop_osc", "signals": ["y"], "stimulus": [{"d": "0"}], "claim": "assign a = ~a (4-state: settles at x; 2-state: oscillates)"})
put("loop_osc2", {"dut.sv": "module loop_osc2(input logic en, output logic a);\n  assign a = en ? ~a : 1'b0;\nendmodule\n"},
    {"top": "loop_osc2", "signals": ["a"], "stimulus": [{"en": "0"}, {"en": "1"}, {"en": "0"}], "claim": "a = en ? ~a : 0: a true oscillator once en=1 (known start value)"})
put("loop_mux", {"dut.sv": "module loop_mux(input logic s, input logic d, output logic y);\n  assign y = s ? d : y;\nendmodule\n"},
    {"top": "loop_mux", "signals": ["y"], "stimulus": [{"s": "1", "d": "1"}, {"s": "0", "d": "0"}, {"s": "1", "d": "0"}, {"s": "0", "d": "1"}],
     "claim": "mux feedback y = s ? d : y (a latch: settles, but holds state)"})
put("loop_fn", {"dut.sv": """module loop_fn(input logic s, input logic d, output logic a, output logic b);
  assign a = s ? d : b;
  assign b = s ? a : d;
endmodule
""" }, {"top": "loop_fn", "signals": ["a", "b"], "stimulus": [{"s": "1", "d": "1"}, {"s": "0", "d": "0"}, {"s": "1", "d": "0"}, {"s": "0", "d": "1"}, {"s": "1", "d": "1"}],
        "claim": "structural loop a=s?d:b, b=s?a:d: settles to a=b=d for every input (functional, deterministic)"})
put("loop_sr", {"dut.sv": """module loop_sr(input logic s, input logic r, output logic q, output logic qn);
  assign q  = ~(r | qn);
  assign qn = ~(s | q);
endmodule
""" }, {"top": "loop_sr", "signals": ["q", "qn"], "stimulus": [{"s": "1", "r": "0"}, {"s": "0", "r": "0"}, {"s": "0", "r": "1"}, {"s": "0", "r": "0"}, {"s": "1", "r": "1"}, {"s": "0", "r": "0"}],
        "claim": "cross-coupled NOR SR latch (settles; state held; (1,1)->(0,0) race is nondeterministic)"})
put("loop_comb_block", {"dut.sv": """module loop_comb_block(input logic [1:0] a, output logic [1:0] y);
  logic [1:0] t;
  always_comb begin
    t = a;
    y = t;
  end
endmodule
""" }, {"top": "loop_comb_block", "signals": ["y"], "stimulus": [{"a": "01"}, {"a": "10"}, {"a": "11"}], "claim": "control: write-then-read always_comb (not a loop)"})

# always without event control
put("alw_nocontrol", {"dut.sv": "module alw_nocontrol(input logic [7:0] a, output logic [7:0] y);\n  always y = a;\nendmodule\n"},
    {"top": "alw_nocontrol", "signals": ["y"], "stimulus": [{"a": "00000001"}, {"a": "00000010"}], "claim": "always y = a;  (zero-delay, no event control)"})
put("alw_nocontrol_ff", {"dut.sv": "module alw_nocontrol_ff(input logic clk, input logic [7:0] a, output logic [7:0] y);\n  always_ff y <= a;\nendmodule\n"},
    {"top": "alw_nocontrol_ff", "clock": "clk", "signals": ["y"], "stimulus": [{"a": "00000001"}, {"a": "00000010"}], "claim": "always_ff y <= a;  (no event control)"})

# section A: frontend-rejected
put("a_st_invalid", {"dut.sv": "module a_st_invalid(input logic a, output logic y);\n  always_comb begin y = zzz; end\nendmodule\n"},
    {"top": "a_st_invalid", "signals": ["y"], "stimulus": [{"a": "0"}, {"a": "1"}], "claim": "undefined name in a procedural statement"})
put("a_st_invalid2", {"dut.sv": "module a_st_invalid2(input logic [1:0] a, input logic [1:0] b, output logic y);\n  always_comb begin a == b; y = 1'b0; end\nendmodule\n"},
    {"top": "a_st_invalid2", "signals": ["y"], "stimulus": [{"a": "00", "b": "00"}], "claim": "expression statement `a == b;` (not a legal statement)"})
put("a_ex_invalid", {"dut.sv": "module a_ex_invalid(input logic a, output logic y);\n  assign y = zzz;\nendmodule\n"},
    {"top": "a_ex_invalid", "signals": ["y"], "stimulus": [{"a": "0"}, {"a": "1"}], "claim": "undefined name in a continuous assign"})
put("a_ex_op_invalid", {"dut.sv": "module a_ex_op_invalid(input logic [3:0] a, input logic [3:0] b, output logic [3:0] y, output logic q);\n  assign y = a / b;\n  assign q = zzz2;\nendmodule\n"},
    {"top": "a_ex_op_invalid", "signals": ["y"], "stimulus": [{"a": "1000", "b": "0010"}], "claim": "division plus an unrelated frontend error"})
put("a_hi_uninst", {"dut.sv": "module a_hi_uninst(input logic a, output logic y);\n  nomod u (.a(a), .y(y));\nendmodule\n"},
    {"top": "a_hi_uninst", "signals": ["y"], "stimulus": [{"a": "0"}, {"a": "1"}], "claim": "instance of a module that has no definition"})
put("a_hi_uninst_gen", {"dut.sv": """module a_hi_uninst_gen #(parameter int P = 0) (input logic a, output logic y);
  if (P == 1) begin : g
    nomod u (.a(a), .y(y));
  end else begin : h
    assign y = a;
  end
endmodule
"""}, {"top": "a_hi_uninst_gen", "signals": ["y"], "stimulus": [{"a": "0"}, {"a": "1"}], "claim": "undefined module in an UNTAKEN generate branch (P=0)"})
put("a_drv_input_assign", {"dut.sv": "module a_drv_input_assign(input logic a, output logic y);\n  assign a = 1'b0;\n  assign y = a;\nendmodule\n"},
    {"top": "a_drv_input_assign", "signals": ["y"], "stimulus": [{"a": "0"}, {"a": "1"}], "claim": "continuous assign to the module's own input port"})
put("a_drv_input_proc", {"dut.sv": "module a_drv_input_proc(input logic a, output logic y);\n  always_comb begin a = 1'b0; y = a; end\nendmodule\n"},
    {"top": "a_drv_input_proc", "signals": ["y"], "stimulus": [{"a": "0"}, {"a": "1"}], "claim": "procedural write to the module's own input port"})
put("a_drv_input_inst", {"dut.sv": """module a_di_child(input logic d, output logic o);
  assign o = ~d;
endmodule
module a_drv_input_inst(input logic a, output logic y);
  a_di_child u (.d(1'b1), .o(a));
  assign y = a;
endmodule
"""}, {"top": "a_drv_input_inst", "signals": ["y"], "stimulus": [{"a": "0"}, {"a": "1"}], "claim": "child output connected to the module's own input"})
put("a_drv_mix_plain", {"dut.sv": """module a_drv_mix_plain(input logic a, input logic b, output logic [1:0] y);
  always_comb y[0] = a;
  assign y[0] = b;
  assign y[1] = a;
endmodule
"""}, {"top": "a_drv_mix_plain", "signals": ["y"], "stimulus": [{"a": "0", "b": "1"}, {"a": "1", "b": "0"}], "claim": "always_comb + assign on one bit (K=0 twin of drv_mix)"})
put("drv_pw_plain_always", {"dut.sv": """module drv_pw_plain_always(input logic clk, input logic rn, input logic d, output logic q);
  always @(posedge clk or negedge rn)
    if (!rn) q <= 1'b0; else q <= d;
endmodule
"""}, {"top": "drv_pw_plain_always", "clock": "clk", "signals": ["q"], "stimulus": [{"rn": "0", "d": "1"}, {"rn": "1", "d": "1"}, {"rn": "1", "d": "0"}],
       "claim": "legal single plain always with async reset (the register says the driver rule over-refuses it)"})

# ---- probes added after the adversarial review of 2026-10-31 (each answers one finding)
put("loop_lat_if", {"dut.sv": """module loop_lat_if(input logic a, output logic y);
  logic t;
  always_comb begin
    if (y) t = a; else t = 1'b0;
  end
  always_comb y = t;
endmodule
"""}, {"top": "loop_lat_if", "signals": ["y"], "stimulus": [{"a": "1"}, {"a": "1"}, {"a": "0"}, {"a": "1"}, {"a": "1"}, {"a": "0"}],
       "claim": "a latch built from a loop that spans two always_comb blocks and a procedural `if`: 4-state simulation takes the else branch for the x start (y = 0 forever), the netlist is y = y & a (two stable states at a = 1)"})
put("loop_lat_if_b", {"dut.sv": """module loop_lat_if_b(input logic a, output logic y);
  logic t;
  always_comb begin
    if (y) t = a; else t = 1'b0;
  end
  always_comb y = t;
endmodule
"""}, {"top": "loop_lat_if_b", "signals": ["y"], "stimulus": [{"a": "0"}, {"a": "1"}, {"a": "1"}, {"a": "0"}, {"a": "1"}],
       "claim": "same latch, stimulus starting with a = 0"})
put("two_plain", {"dut.sv": """module two_plain(input logic a, input logic b, output logic y);
  always @* y = a;
  always @* y = b;
endmodule
"""}, {"top": "two_plain", "signals": ["y"], "stimulus": [{"a": "0", "b": "1"}, {"a": "1", "b": "1"}, {"a": "1", "b": "0"}, {"a": "0", "b": "0"}, {"a": "1", "b": "0"}, {"a": "0", "b": "1"}],
       "claim": "two PLAIN always @* blocks writing one variable: legal text (slang clean), the winner is a scheduling choice"})
put("two_plain_ac", {"dut.sv": """module two_plain_ac(input logic a, input logic b, output logic y);
  always_comb y = a;
  always @* y = b;
endmodule
"""}, {"top": "two_plain_ac", "signals": ["y"], "stimulus": [{"a": "0", "b": "1"}, {"a": "1", "b": "1"}, {"a": "1", "b": "0"}, {"a": "0", "b": "0"}],
       "claim": "always_comb plus a plain always @* writing one variable (LRM 9.2.2.2: shall not be written by another process)"})
put("init_comb_proc", {"dut.sv": """module init_comb_proc(input logic a, output logic y);
  initial y = 1'b0;
  always_comb y = a;
endmodule
"""}, {"top": "init_comb_proc", "signals": ["y"], "stimulus": [{"a": "1"}, {"a": "0"}, {"a": "1"}],
       "claim": "an initial block and an always_comb writing one variable (9.2.2.2)"})
put("init_whole", {"dut.sv": """module init_whole(input logic [1:0] a, output logic [1:0] y);
  logic [1:0] t = 2'b10;
  always_comb t = {1'b0, a[0]};
  assign y = t;
endmodule
"""}, {"top": "init_whole", "signals": ["y"], "stimulus": [{"a": "01"}, {"a": "10"}, {"a": "11"}, {"a": "00"}],
       "claim": "declaration initializer plus a WHOLE-variable always_comb write (Verilator warns MULTIDRIVEN)"})
put("hex_guard", {"dut.sv": """module hex_guard(input logic [15:0] a, output logic [7:0] y);
  assign y = (a == 16'hBEEF) ? "\\x41" : 8'h41;
endmodule
"""}, {"top": "hex_guard", "signals": ["y"], "stimulus": [{"a": "1011111011101111"}, {"a": "0000000000000000"}],
       "claim": "a hex string escape confined to a rare region (the attack the fourstate docstring describes): 8'h31 in Yosys and Xcelium, 8'h41 in slang, Icarus, Verilator"})
put("lit_str_x4", {"dut.sv": 'module lit_str_x4(input logic d, output logic [7:0] y);\n  assign y = "\\x4";\nendmodule\n'},
    {"top": "lit_str_x4", "signals": ["y"], "stimulus": [{"d": "0"}], "claim": 'one-digit hex escape "\\x4"'})
print("cases:", len(os.listdir(CASES)))
