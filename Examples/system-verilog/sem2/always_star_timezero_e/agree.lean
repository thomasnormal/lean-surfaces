import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core0Entry

/-! Clean-room E receipt for a plain `always @*` whose read is fed by a
continuous driver.  The parser node stays an implicit event; it is not
lowered to `always_comb`. -/
namespace Examples.«system-verilog».sem2.always_star_timezero_e.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 alwaysStarTimezeroE
  from "Examples/system-verilog/sem2/always_star_timezero_e/always_star_timezero_e.sv.json"

#guard alwaysStarTimezeroE.pdesign.others == []
#guard match alwaysStarTimezeroE.pdesign.processes with
  | [.assign "k" (.ident "a"),
      .alwaysImplicit (.blockingAssign "y_star" (.ident "k")),
      .alwaysComb (.blockingAssign "y_comb" (.ident "k"))] => true
  | _ => false

private def E : Elab :=
  Elab.ofEDesign2 (alwaysStarTimezeroE.pdesign.instantiateDE2 [4])

#guard match E.procs.toList with
  | [.assign (.ident "k") (.ident "a"), .implicit _, .comb _] => true
  | _ => false
#guard match E.procs[1]? with
  | some (LeanModels.Sv.Kernel.Proc0.implicit body) => E.sens 1 == body.rawReads
  | _ => false

private def row (a : String) : SvState := [("a", LVec.lit a)]

private def display (c : Config) : String :=
  String.intercalate " " [SvState.showSignal (E.view c.store) "k",
    SvState.showSignal (E.view c.store) "y_star",
    SvState.showSignal (E.view c.store) "y_comb"]

private def run (entries : List SvState) : List String :=
  match entries with
  | [] => []
  | first :: rest =>
      let rec go : Config → List SvState → List String
        | c, [] => []
        | c, e :: es =>
            match exec E σ_src 100 (Config.nextSlot E c e) with
            | .closed c' => display c' :: go c' es
            | _ => ["REFUSE"]
      match exec E σ_src 100 (Config.start E first) with
      | .closed c => display c :: go c rest
      | _ => ["REFUSE"]

/- The receipt below uses E's executable source-order choice.  The source
   checker records the independent Icarus startup schedule as well; the first
   observation is therefore not asserted as a unique IEEE outcome. -/
#guard run [row "0011", row "1010", row "xz01", row "zzzz"] ==
  ["0011 0011 0011", "1010 1010 1010", "xz01 xz01 xz01", "zzzz zzzz zzzz"]

end Examples.«system-verilog».sem2.always_star_timezero_e.agree
