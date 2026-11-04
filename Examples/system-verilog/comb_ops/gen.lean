import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary

/-!
# `comb_ops` — the operators of the second `sv_comb` fragment (WP-G S2)

Four real envelopes, loaded by `load_design_sv2`:

* `add_mux.sv`: a ripple-carry adder written with `~` and `?:` (`e[i] = ~(a[i] ^ b[i])`,
  `c[i+1] = e[i] ? a[i] : c[i]`, `s[i] = ~(e[i] ^ c[i])`), the design behind `comb_proof.lean`;
* `ops_gen.sv`: every new operator (`~`, `!` of a vector, the six reductions, `&&`, `||`, `==`, `!=`, `?:`) in
  whole-signal and per-bit assigns at a symbolic width;
* `ops_flat.sv`: a FLAT netlist (no parameter, no loop) with the same operators: the tactics decide its
  obligations;
* `ops_proc.sv`: `always_comb` bodies whose conditions and leaves use them.

The guards are the non-vacuity checks: the assign-only designs are read by the old recognizer
(`PDesign.summary`), the `always_comb` design only by the proc-aware one (`PDesign.summaryP`).
-/

namespace Examples.«system-verilog».comb_ops.gen

open LeanModels.Sv LeanModels.Sv.CombView

load_design_sv2 add_mux from "Examples/system-verilog/comb_ops/add_mux.sv.json"
load_design_sv2 ops_gen from "Examples/system-verilog/comb_ops/ops_gen.sv.json"
load_design_sv2 ops_flat from "Examples/system-verilog/comb_ops/ops_flat.sv.json"
load_design_sv2 ops_proc from "Examples/system-verilog/comb_ops/ops_proc.sv.json"

#guard add_mux.pdesign.summary.toOption.isSome
#guard ops_gen.pdesign.summary.toOption.isSome
#guard ops_flat.pdesign.summary.toOption.isSome
#guard ops_proc.pdesign.summary.toOption.isNone
#guard ops_proc.pdesign.summaryP.toOption.isSome

-- the instantiations at small widths
#guard (add_mux.sem 3).processes.size == 11
#guard (ops_proc.sem 3).lowerComb.isSome
#guard ops_flat.sem.processes.size == 8

end Examples.«system-verilog».comb_ops.gen
