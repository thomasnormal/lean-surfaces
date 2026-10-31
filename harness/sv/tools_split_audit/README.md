# tools_split_audit: the multi-tool matrix behind docs/sv-tools-split-audit.md

Runs a set of SystemVerilog fixtures (the `Examples/system-verilog/sem2/*` rows the refusal register cites, comments stripped,
plus the hand-written probes in `build_cases.py`) through slang, Icarus, Verilator, Yosys and Xcelium and tabulates what each
tool does. Everything it writes goes under `$AUDIT_DIR` (default `out/` next to the scripts); nothing is written into the tree.

Needs `python3.12` with `pyslang` 11, `yosys`, `verilator`, `iverilog`; Xcelium is optional (`ssh vip-ng`, the fleet gate
`refsim`, one run at a time, remote directory removed afterwards).

```
export WT=$(git rev-parse --show-toplevel) AUDIT_DIR=/tmp/sv-tools-split-audit
A=$WT/harness/sv/tools_split_audit
python3.12 $A/build_cases.py                  # fixtures + probes -> $AUDIT_DIR/cases/<id>/{dut.sv,case.json}
python3.12 $A/tm.py [CASE ...]                # slang (full driver, analysis included), Icarus, Verilator (2-state), Yosys + netlist sim
python3 $A/xc.py CASE ...                     # Xcelium on vip-ng (batches of about 25 cases)
python3.12 $A/ext_all.py                      # what the ls-sv extractor emits (Unsupported kinds) -> ext_all.json
python3.12 $A/fs_all.py                       # svgolf/score/fourstate.py on every case -> fs_all.json
python3 $A/report.py > appendix.md            # the per-case matrix of the audit page
python3.12 $A/yosys_frontend.py               # which "not synthesizable" constructs the scored frontend (Yosys read_verilog -sv) fails on (P-SYNTHESIZABLE)
python3 $A/matrix.py CASE ... ; python3 $A/show.py CASE ...      # one case, compact / full
python3.12 $A/lean_cases.py                   # optional: the run2 column. Needs ext_all.py first; under the shared Lean slot:
#   leanslot.sh $A/lean_batch.sh $WT $AUDIT_DIR CASE ... > lean.out ; python3 $A/lean_parse.py lean.out
```

Testbenches are the cycle testbenches of `harness/sv/gen_tb2.py` (the ones the Xcelium pins use); Verilator gets x/z stimulus
digits as 0 (it is 2-state, and a testbench with `1'bx` literals is mis-simulated by it); the Yosys column simulates the
netlist of `synth -flatten` in Icarus. The slang column is `pyslang.driver.Driver` (parse, elaboration AND analysis):
`Compilation.getAllDiagnostics()` alone omits `multiple-always-assigns`, `mixed-var-assigns` and the always-deadlock error.

Round 2 (the adversarial review of the first draft) added the probes `loop_lat_if` / `loop_lat_if_b` (a state-holding loop the model
computes as constant 0), `two_plain` / `two_plain_ac` (two plain `always @*` writers; an `always_comb` plus a plain writer),
`init_comb_proc` (`initial` plus `always_comb`), `init_whole` (initializer plus a whole-variable `always_comb` write),
`hex_guard` / `lit_str_x4` (hex string escapes) and removed `dc_port_explicit` (a malformed mix of ANSI and non-ANSI ports; the
legal explicit-port case is `pi_explicit`).
