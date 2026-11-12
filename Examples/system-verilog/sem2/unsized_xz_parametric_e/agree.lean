import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.unsized_xz_parametric_e.agree

open LeanModels.Sv

set_option maxRecDepth 100000 in
load_design_sv2 unsizedXZParametricE
  from "Examples/system-verilog/sem2/unsized_xz_parametric_e/unsized_xz_parametric_e.sv.json"

private def expected (n : Nat) : List LVec :=
  [LVec.xVec n,
   LVec.lit (String.ofList (List.replicate (n - 4) 'z') ++ "0001"),
   LVec.lit (String.ofList (List.replicate (n + 4) 'z') ++ "0001"),
   LVec.lit "0001"]

private def processValues (n : Int) : Option (List LVec) :=
  match unsizedXZParametricE.pdesign.instantiate2 [n] with
  | .ok d =>
      if d.hasUnsupported then none else
        match d.processes.toList with
        | [ .assign (.ident "qx") (.lit qx),
            .assign (.ident "qz") (.lit qz),
            .assign (.ident "qw") (.lit qw),
            .assign (.ident "qn") (.lit qn) ] => some [qx, qz, qw, qn]
        | _ => none
  | .unsupported _ | .timeout => none

#guard processValues 8 == some (expected 8)
#guard processValues 40 == some (expected 40)

private def runValues (n : Int) : Option (List LVec) :=
  (run2 (unsizedXZParametricE.pdesign.instantiateD2 [n]) σ_src 64 [[]]).toOption.map
    fun states =>
      match states with
      | [st] => [SvState.lookup st "qx", SvState.lookup st "qz",
                 SvState.lookup st "qw", SvState.lookup st "qn"]
          |>.map (·.getD (LVec.xVec n.toNat))
      | _ => []

#guard runValues 8 == some (expected 8)
#guard runValues 40 == some (expected 40)

end Examples.«system-verilog».sem2.unsized_xz_parametric_e.agree
