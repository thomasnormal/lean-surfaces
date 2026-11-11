import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemE

/-! Clean-room E admission receipt for a plain `always @*` case latch. -/
namespace Examples.«system-verilog».sem2.always_star_case_latch_e

open LeanModels.Sv
open LeanModels.Sv.Kernel

set_option maxRecDepth 100000 in
load_design_sv2 alwaysStarCaseLatchE
  from "Examples/system-verilog/sem2/always_star_case_latch_e/always_star_case_latch_e.sv.json"

#guard alwaysStarCaseLatchE.pdesign.others == []

#guard match alwaysStarCaseLatchE.pdesign.processes with
  | [.alwaysImplicit (.block [.caseStmt (.ident "sel") items none .normal .none])] =>
      items.length == 2
  | _ => false

/- The source process is retained by the parser, but the current memory
   profile has no implicit-wait scheduler and refuses it rather than silently
   skipping the latch. -/
#guard match MemEDesign.ofPDesign alwaysStarCaseLatchE.pdesign [4] with
  | .unsupported "E memory route does not yet admit implicit event-controlled processes" => true
  | _ => false

end Examples.«system-verilog».sem2.always_star_case_latch_e
