import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Core0Entry

/-! E receipt for an initial process containing only elaboration checks.
The checks are evaluated in the package-aware constant environment. A passing
check is retained as an inert time-zero process; a failing `$fatal` remains a
loud `Initial:check` refusal. The packed enum itself stays a qualified
`EnumRef` in the continuous assignment. -/
namespace Examples.«system-verilog».sem2.initial_enum_checks_e.agree

open LeanModels.Sv
open LeanModels.Sv.Kernel

load_design_sv2 initialEnumChecksE
  from "Examples/system-verilog/sem2/initial_enum_checks_e/initial_enum_checks_e.sv.json"

#guard initialEnumChecksE.pdesign.others == []
#guard match initialEnumChecksE.pdesign.processes with
  | [.initial _, .assign "y" (.binary (.m0 .eq) (.ident "a")
      (.enumRef "mode_t" "RUN" (some "initial_enum_checks_pkg")))] => true
  | _ => false

private def E : Elab :=
  Elab.ofEDesign2 (initialEnumChecksE.pdesign.instantiateDE2 [])

#guard E.decls.size == 2
#guard match E.procs.toList with
  | [.comb (.block #[]), .assign (.ident "y")
      (.binary .eq (.ident "a") (.lit v))] => v == LVec.ofNat 2 1
  | _ => false

private def row (a : String) : SvState := [("a", LVec.lit a)]
private def out (c : Config) : String := SvState.showSignal (E.view c.store) "y"

private def run (entries : List SvState) : List String :=
  match entries with
  | [] => []
  | first :: rest =>
      match exec E σ_src 100 (Config.start E first) with
      | .closed c => out c :: go c rest
      | _ => ["REFUSE"]
where
  go (c : Config) : List SvState → List String
    | [] => []
    | e :: es =>
        match exec E σ_src 100 (Config.nextSlot E c e) with
        | .closed c' => out c' :: go c' es
        | _ => ["REFUSE"]

#guard run [row "00", row "01", row "10", row "11"] == ["0", "1", "0", "0"]

end Examples.«system-verilog».sem2.initial_enum_checks_e.agree
