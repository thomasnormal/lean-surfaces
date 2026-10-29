/-
Examples/system-verilog/sem2/onehot_dec — the differential fixture of the
"default, then override one bit" one-hot decoder (`harness/sv/cases2.json`
row `onehot_dec`: `run2` of THIS envelope against Icarus), tied to the
hand-built design `decDesign` of `LeanModels/Sv/Comb2ProcExample.lean`
(`dec_correct`, `dec_terminates`).

  onehot_dec.sv      — the SystemVerilog source
  onehot_dec.sv.json — generated envelope (extractors/sv/extract.py --top)
  agree.lean — THIS FILE: the instantiated design IS `decDesign`
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2ProcExample
import LeanModels.Sv.CombAlias2Example

/-!
# The SV source instantiates to the proved design

`load_design_sv2` turns the envelope into the design `onehot_dec.sem`. Its name
and declarations are exactly `decDesign`'s, and its process list prints exactly
as `decDesign`'s (`Process2` derives no `BEq`, so the printed forms are
compared); its `always_comb` body symbolically executes to the very
equations `decSym` the theorems of `Comb2ProcExample` are about. These are
`#guard` evaluations of the instantiated design, not a theorem about the
instantiation.
-/

namespace Examples.«system-verilog».sem2.onehot_dec.agree

open LeanModels.Sv LeanModels.Sv.Comb2ProcExample

load_design_sv2 onehot_dec from "Examples/system-verilog/sem2/onehot_dec/onehot_dec.sv.json"

#guard onehot_dec.sem.name == decDesign.name
#guard onehot_dec.sem.decls.toList == decDesign.decls.toList
#guard toString (repr onehot_dec.sem.processes) == toString (repr decDesign.processes)
-- the always_comb alias guard (`CombAlias2.lean`) leaves the instantiated design unchanged
#guard toString (repr onehot_dec.sem.aliasGuard.processes) == toString (repr onehot_dec.sem.processes)
#guard match onehot_dec.sem.processes.toList with
  | [.alwaysComb body] => body.symExec onehot_dec.sem [] == some decSym
  | _ => false

end Examples.«system-verilog».sem2.onehot_dec.agree
