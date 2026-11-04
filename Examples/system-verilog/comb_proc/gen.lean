import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary

/-!
# `comb_proc` — an `always_comb` carry cell inside a generate loop (WP-G, G2.2)

`add_proc.sv` is the ripple-carry adder of `ripple_add` with the carry cell written as an `always_comb`
`if/else` (one written window, `c[i+1]`, a one-bit condition `p[i]`). `load_design_sv2` loads the real
envelope; the guards below are the non-vacuity checks of the whole directory:

* the instantiated design really CONTAINS the procedural processes (so `CombDesign (add_proc.sem N)` is false
  and the lowered shape of `comb_view.lean` is the right statement);
* the proc-aware recognizer (`PDesign.summaryP`) accepts it, and the lowering `Design2.lowerComb` turns every
  `always_comb` into one continuous assign.
-/

namespace Examples.«system-verilog».comb_proc.gen

open LeanModels.Sv LeanModels.Sv.CombView

load_design_sv2 add_proc from "Examples/system-verilog/comb_proc/add_proc.sv.json"

private def isComb : Process2 → Bool
  | .alwaysComb _ => true
  | _ => false

private def isAssign : Process2 → Bool
  | .assign .. => true
  | _ => false

-- The instantiation at `N = 3` has `2 + 3 * 3` processes, three of them `always_comb`.
#guard (add_proc.sem 3).processes.size == 11
#guard ((add_proc.sem 3).processes.toList.filter isComb).length == 3

-- The proc-aware recognizer accepts the design (the old one refuses the `always_comb`).
#guard add_proc.pdesign.summaryP.toOption.isSome
#guard add_proc.pdesign.summary.toOption.isNone

-- The lowering exists at several widths and leaves assigns only.
#guard ((add_proc.sem 3).lowerComb.map fun d => d.processes.toList.all isAssign) == some true
#guard ((add_proc.sem 5).lowerComb.map fun d => d.processes.size) == some 17
#guard (add_proc.sem 1).lowerComb.isSome

end Examples.«system-verilog».comb_proc.gen
