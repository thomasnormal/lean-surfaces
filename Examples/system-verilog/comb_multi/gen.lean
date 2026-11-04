import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcSummary

/-!
# `comb_multi` — an `always_comb` body that writes TWO windows (WP-G S1b, gate a)

`add_proc_m.sv` is the ripple adder with the whole bit cell in ONE body,
`if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i]; s[i] = p[i] ^ c[i];`: two written windows, `c[i+1]` and `s[i]`.
`Design2.lowerComb` already lowers it to ONE assign `{c[i+1], s[i]} = {…, …}`; `comb_semantic.lean` proves, from the
semantic core of `CombProcStmt.lean` (`lower_body`), that this IS the lowering, at a concrete width. Since S1b gate
c3 the summary reads such a body as ONE site with further windows (`TSite.more`), so `sv_structure` accepts it
(`comb_view.lean`); since gate d `sv_equations` states one equation and one knownness fact per window
(`comb_hint.lean`, `comb_proof.lean`).

`multi_flat.sv` is the same shape without a generate loop: one body writing `y` (a default and an override) and `z`.
-/

namespace Examples.«system-verilog».comb_multi.gen

open LeanModels.Sv LeanModels.Sv.CombView

load_design_sv2 add_proc_m from "Examples/system-verilog/comb_multi/add_proc_m.sv.json"
load_design_sv2 multi_flat from "Examples/system-verilog/comb_multi/multi_flat.sv.json"
load_design_sv2 multi_same from "Examples/system-verilog/comb_multi/multi_same.sv.json"

private def isComb : Process2 → Bool
  | .alwaysComb _ => true
  | _ => false

private def isAssign : Process2 → Bool
  | .assign .. => true
  | _ => false

-- the instantiated design contains the multi-window bodies, and lowers
#guard ((add_proc_m.sem 3).processes.toList.filter isComb).length == 3
#guard ((add_proc_m.sem 3).lowerComb.map fun d => d.processes.toList.all isAssign) == some true
-- the proc-aware summary reads the cell as ONE site with a further window: the sites' `more` lengths
#guard (add_proc_m.pdesign.summaryP.toOption.map fun s => s.lsites.map fun ls => ls.site.more.length) ==
  some [0, 0, 0, 1]
#guard add_proc_m.pdesign.summary.toOption.isNone

-- the flat body: one site (the two windows `y` and `z`), a design without a generate loop
#guard (multi_flat.pdesign.summaryP.toOption.map fun s => s.lsites.map fun ls => ls.site.more.length) == some [1]
#guard multi_flat.sem.lowerComb.isSome

-- two windows of ONE signal in one body (`y[0]`, `y[1]`): one site, one further window
#guard (multi_same.pdesign.summaryP.toOption.map fun s => s.lsites.map fun ls => ls.site.more.length) == some [1]
#guard multi_same.sem.lowerComb.isSome

end Examples.«system-verilog».comb_multi.gen
