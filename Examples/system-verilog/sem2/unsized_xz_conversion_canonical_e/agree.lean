import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.unsized_xz_conversion_canonical_e.agree

open LeanModels.Sv

set_option maxRecDepth 100000 in
load_design_sv2 unsizedXZConversionCanonicalE
  from "Examples/system-verilog/sem2/unsized_xz_conversion_canonical_e/unsized_xz_conversion_canonical_e.sv.json"

#guard unsizedXZConversionCanonicalE.pdesign.others == []

private def expected (n : Nat) : List LVec :=
  [LVec.xVec n, LVec.replicate n .lz,
   LVec.lit (String.ofList (List.replicate (n - 4) 'x') ++ "0000"),
   LVec.lit (String.ofList (List.replicate (n - 4) 'z') ++ "0001")]

private def processValues (n : Int) : Option (List LVec) :=
  match unsizedXZConversionCanonicalE.pdesign.instantiate2 [n] with
  | .ok d =>
      if d.hasUnsupported then none else
        match d.processes.toList with
        | [ .assign (.ident "qx") (.lit qx),
            .assign (.ident "qz") (.lit qz),
            .assign (.ident "qhx") (.lit qhx),
            .assign (.ident "qhz") (.lit qhz) ] => some [qx, qz, qhx, qhz]
        | _ => none
  | .unsupported _ | .timeout => none

#guard processValues 40 == some (expected 40)
#guard processValues 8 == some (expected 8)

private def runValues (n : Int) : Option (List LVec) :=
  (run2 (unsizedXZConversionCanonicalE.pdesign.instantiateD2 [n]) σ_src 64 [[]]).toOption.map
    fun states =>
      match states with
      | [st] => [SvState.lookup st "qx", SvState.lookup st "qz",
                 SvState.lookup st "qhx", SvState.lookup st "qhz"]
          |>.map (·.getD (LVec.xVec n.toNat))
      | _ => []

#guard runValues 40 == some (expected 40)
#guard runValues 8 == some (expected 8)

end Examples.«system-verilog».sem2.unsized_xz_conversion_canonical_e.agree
