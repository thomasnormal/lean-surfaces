/-
Examples/system-verilog/sem2/mux4_case — the differential fixture of the default-then-case multiplexer
(`harness/sv/cases2.json` row `mux4_case`: `run2` of THIS envelope against
Icarus), tied to the hand-built design `muxDesign` of
`LeanModels/Sv/Comb2ProcExample.lean` (`mux_correct`, `mux_terminates`).

  mux4_case.sv      — the SystemVerilog source
  mux4_case.sv.json — generated envelope (extractors/sv/extract.py --top)
  agree.lean — THIS FILE: the instantiated design IS `muxDesign`
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2ProcExample

/-!
# The SV source instantiates to the proved design

`load_design_sv2` turns the envelope into the design `mux4_case.sem`. Its name
and declarations are exactly `muxDesign`'s, and its process list prints exactly
as `muxDesign`'s (`Process2` derives no `BEq`, so the printed forms are
compared); its `always_comb` body symbolically executes to the very
equations `muxSym` the theorems of `Comb2ProcExample` are about. These are
`#guard` evaluations of the instantiated design, not a theorem about the
instantiation.
-/

namespace Examples.«system-verilog».sem2.mux4_case.agree

open LeanModels.Sv LeanModels.Sv.Comb2ProcExample

load_design_sv2 mux4_case from "Examples/system-verilog/sem2/mux4_case/mux4_case.sv.json"

#guard mux4_case.sem.name == muxDesign.name
#guard mux4_case.sem.decls.toList == muxDesign.decls.toList
#guard toString (repr mux4_case.sem.processes) == toString (repr muxDesign.processes)
#guard match mux4_case.sem.processes.toList with
  | [.alwaysComb body] => body.symExec mux4_case.sem [] == some muxSym
  | _ => false

end Examples.«system-verilog».sem2.mux4_case.agree
