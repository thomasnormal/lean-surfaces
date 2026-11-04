import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary

/-!
# `comb_case` — a plain `case` in an `always_comb` (WP-G S3a)

Four real envelopes, loaded by `load_design_sv2`:

* `case_mux.sv`: a 4-way mux, `case (s)` with arms `y = a;`, `y = b;`, `y = c;` and a `default`;
* `case_lut.sv`: a 4-entry look-up table (constant items, constant values), the design behind `comb_proof.lean`;
* `case_multi.sv`: an item with several patterns (`2'd0, 2'd3:`), a repeated pattern (the first item wins) and
  gate-tree arms;
* `case_gen.sv`: a `case` on a gate-tree subject (`s ^ a[i]`) in a generate loop at symbolic width.

The fragment: a PLAIN `case` (not `unique`, `priority`, `inside`, `casez`, `casex`) with a `default`, whose
items are lists of known sized literals as wide as the subject and whose arms are single assignments of
the one target. `neg/` has one design per refused shape (`comb_errors.lean`).
-/

namespace Examples.«system-verilog».comb_case.gen

open LeanModels.Sv LeanModels.Sv.CombView

load_design_sv2 case_mux from "Examples/system-verilog/comb_case/case_mux.sv.json"
load_design_sv2 case_lut from "Examples/system-verilog/comb_case/case_lut.sv.json"
load_design_sv2 case_multi from "Examples/system-verilog/comb_case/case_multi.sv.json"
load_design_sv2 case_gen from "Examples/system-verilog/comb_case/case_gen.sv.json"

-- a procedural design is read only by the proc-aware summary
#guard case_mux.pdesign.summary.toOption.isNone
#guard case_mux.pdesign.summaryP.toOption.isSome
#guard case_lut.pdesign.summaryP.toOption.isSome
#guard case_multi.pdesign.summaryP.toOption.isSome
#guard case_gen.pdesign.summaryP.toOption.isSome

-- the lowering (each `always_comb` becomes the one assign it computes)
#guard case_mux.sem.lowerComb.isSome
#guard case_lut.sem.lowerComb.isSome
#guard case_multi.sem.lowerComb.isSome
#guard (case_gen.sem 3).lowerComb.isSome

end Examples.«system-verilog».comb_case.gen
