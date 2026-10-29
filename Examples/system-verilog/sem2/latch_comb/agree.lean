/-
Examples/system-verilog/sem2/latch_comb — the differential fixture of the always_comb latch
(`harness/sv/cases2.json` row `latch_comb`: `run2` of THIS envelope against
Icarus), tied to the hand-built design `latchDesign` of
`LeanModels/Sv/Comb2ProcExample.lean` (`latch_symExec`, `latch_refused`,
`latch_not_acyclic`).

  latch_comb.sv      — the SystemVerilog source
  latch_comb.sv.json — generated envelope (extractors/sv/extract.py --top)
  agree.lean — THIS FILE: the instantiated design IS `latchDesign`
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2ProcExample

/-!
# The SV source instantiates to the proved design

`load_design_sv2` turns the envelope into the design `latch_comb.sem`. Its name
and declarations are exactly `latchDesign`'s, and its process list prints exactly
as `latchDesign`'s (`Process2` derives no `BEq`, so the printed forms are
compared); its `always_comb` body symbolically executes to the very
equations `latchSym` the theorems of `Comb2ProcExample` are about, and the
lowering refuses it (the equation reads `q` itself). These are
`#guard` evaluations of the instantiated design, not a theorem about the
instantiation.
-/

namespace Examples.«system-verilog».sem2.latch_comb.agree

open LeanModels.Sv LeanModels.Sv.Comb2ProcExample

load_design_sv2 latch_comb from "Examples/system-verilog/sem2/latch_comb/latch_comb.sv.json"

#guard latch_comb.sem.name == latchDesign.name
#guard latch_comb.sem.decls.toList == latchDesign.decls.toList
#guard toString (repr latch_comb.sem.processes) == toString (repr latchDesign.processes)
#guard match latch_comb.sem.processes.toList with
  | [.alwaysComb body] => body.symExec latch_comb.sem [] == some latchSym
  | _ => false
#guard latch_comb.sem.lowerComb.isNone

end Examples.«system-verilog».sem2.latch_comb.agree
