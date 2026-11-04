import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary

/-!
# `comb_ovr` — default-then-override in an `always_comb` (WP-G S3b)

Three real envelopes, loaded by `load_design_sv2`:

* `add_ovr.sv`: the ripple-carry adder of `comb_proc` with the carry cell written the way a player often writes
  it: `c[i+1] = a[i]; if (p[i]) c[i+1] = c[i];` (a default, then an override; the last write wins). Its netlist
  equation is the same `if p[i] then c[i] else a[i]` as the `if/else` form;
* `prio_enc.sv`: a priority encoder, `y = 0;` then three overrides `if (r[k]) y = k;` (the highest request wins);
* `case_tree.sv`: a `case` whose arms are trees (an `if/else`, a block with a default and an override) — NOT in
  the fragment yet: `comb_errors.lean` pins its refusal.

The fragment (the second): a block of statements all writing the SAME window — the first a tree that assigns it on
every path, each later one an `if (c) tree;` without `else` (its branch a tree that assigns it on every path).
A block with a second unconditional assignment, an `else` after the first statement or a read of the written
window stays outside (`neg/`, `comb_errors.lean`); a block that writes SEVERAL windows, each as such a fragment
in its own group of statements, is read as one site with further windows (S1b gate c: `comb_multi`).
-/

namespace Examples.«system-verilog».comb_ovr.gen

open LeanModels.Sv LeanModels.Sv.CombView

load_design_sv2 add_ovr from "Examples/system-verilog/comb_ovr/add_ovr.sv.json"
load_design_sv2 prio_enc from "Examples/system-verilog/comb_ovr/prio_enc.sv.json"
load_design_sv2 case_tree from "Examples/system-verilog/comb_ovr/case_tree.sv.json"

private def isComb : Process2 → Bool
  | .alwaysComb _ => true
  | _ => false

private def isAssign : Process2 → Bool
  | .assign .. => true
  | _ => false

-- the instantiated adder contains the procedural carry cells; the proc-aware recognizer accepts it
#guard ((add_ovr.sem 3).processes.toList.filter isComb).length == 3
#guard add_ovr.pdesign.summaryP.toOption.isSome
#guard add_ovr.pdesign.summary.toOption.isNone
#guard ((add_ovr.sem 3).lowerComb.map fun d => d.processes.toList.all isAssign) == some true
#guard (add_ovr.sem 1).lowerComb.isSome

-- the priority encoder: one `always_comb` with four statements, lowered to one assign
#guard prio_enc.pdesign.summaryP.toOption.isSome
#guard prio_enc.sem.lowerComb.isSome
#guard (prio_enc.sem.lowerComb.map fun d => d.processes.toList.all isAssign) == some true

-- a `case` with tree arms is outside the fragment (the recognizer refuses it)
#guard case_tree.pdesign.summaryP.toOption.isNone

end Examples.«system-verilog».comb_ovr.gen
