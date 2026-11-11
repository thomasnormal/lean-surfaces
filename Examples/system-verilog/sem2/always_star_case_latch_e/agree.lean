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

private def output (sel d : String) : Option LVec :=
  match MemEDesign.ofPDesign alwaysStarCaseLatchE.pdesign [4] with
  | .ok design =>
      (design.step design.init
        [("sel", LVec.lit sel), ("d", LVec.lit d)]).toOption.bind
        (fun s => SvState.lookup s.scalar "q")
  | .unsupported _ | .timeout => none

/- The source process is retained by the parser and its narrow case-arm slice
   executes the source-shaped first-match arm through E. -/
#guard match MemEDesign.ofPDesign alwaysStarCaseLatchE.pdesign [4] with
  | .ok _ => true
  | _ => false

#guard output "00" "0011" == some (LVec.lit "0011")
#guard output "01" "0011" == some (LVec.lit "1100")
#guard output "10" "0011" == some (LVec.xVec 4)

end Examples.«system-verilog».sem2.always_star_case_latch_e
