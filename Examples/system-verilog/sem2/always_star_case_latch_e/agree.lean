import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core0Entry

/-! Clean-room E-core-0 receipt for a plain `always @*` case latch. -/
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

private def E : Elab :=
  Elab.ofEDesign2 (alwaysStarCaseLatchE.pdesign.instantiateDE2 [4])

#guard match E.procs.toList with
  | [.implicit (.block #[.caseStmt (.ident "sel") items none .normal .none])] =>
      items.size == 2
  | _ => false

private def row (sel d : String) : SvState :=
  [("sel", LVec.lit sel), ("d", LVec.lit d)]

private def display (c : Config) : String :=
  SvState.showSignal (E.view c.store) "q"

private def runRows : Config → List SvState → List String
  | c, [] => []
  | c, input :: rest =>
      match exec E σ_src 100 (Config.nextSlot E c input) with
      | .closed c' => display c' :: runRows c' rest
      | .refused _ | .outOfBudget _ => ["REFUSE"]

private def run : List SvState → Option (List String)
  | [] => some []
  | first :: rest =>
      match exec E σ_src 100 (Config.start E first) with
      | .closed c => some (display c :: runRows c rest)
      | .refused _ | .outOfBudget _ => none

/- The retained implicit process starts waiting at time zero (LRM 9.4.2.2),
   so the first sample is x.  Input changes wake it; the source-shaped case
   then takes the first matching arm and holds q when no arm matches. -/
#guard run [row "00" "0011", row "01" "0011", row "10" "0011", row "10" "1010",
    row "00" "1010", row "xz" "1010", row "01" "zzzz", row "11" "zzzz"] ==
  some ["xxxx", "1100", "1100", "1100", "1010", "1010", "xxxx", "xxxx"]

end Examples.«system-verilog».sem2.always_star_case_latch_e
