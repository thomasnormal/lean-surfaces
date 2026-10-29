/-
Examples/system-verilog/sem2/fa_comb_proc — the differential fixture of the full adder as one always_comb (temporary + if/else)
(`harness/sv/cases2.json` row `fa_comb_proc`: `run2` of THIS envelope against
Icarus), tied to the hand-built design `faDesign` of
`LeanModels/Sv/Comb2ProcExample.lean` (`fa_correct`, `fa_correct_stim`, `fa_terminates`).

  fa_comb_proc.sv      — the SystemVerilog source
  fa_comb_proc.sv.json — generated envelope (extractors/sv/extract.py --top)
  agree.lean — THIS FILE: the instantiated design IS `faDesign`
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2ProcExample

/-!
# The SV source instantiates to the proved design

`load_design_sv2` turns the envelope into the design `fa_comb_proc.sem`. Its name
and declarations are exactly `faDesign`'s, and its process list prints exactly
as `faDesign`'s (`Process2` derives no `BEq`, so the printed forms are
compared); its `always_comb` body symbolically executes to the very
equations `faSym` the theorems of `Comb2ProcExample` are about. These are
`#guard` evaluations of the instantiated design, not a theorem about the
instantiation.
-/

namespace Examples.«system-verilog».sem2.fa_comb_proc.agree

open LeanModels.Sv LeanModels.Sv.Comb2ProcExample

load_design_sv2 fa_comb_proc from "Examples/system-verilog/sem2/fa_comb_proc/fa_comb_proc.sv.json"

#guard fa_comb_proc.sem.name == faDesign.name
#guard fa_comb_proc.sem.decls.toList == faDesign.decls.toList
#guard toString (repr fa_comb_proc.sem.processes) == toString (repr faDesign.processes)
#guard match fa_comb_proc.sem.processes.toList with
  | [.alwaysComb body] => body.symExec fa_comb_proc.sem [] == some faSym
  | _ => false

end Examples.«system-verilog».sem2.fa_comb_proc.agree
