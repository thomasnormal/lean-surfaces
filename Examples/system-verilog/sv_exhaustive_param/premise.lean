import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombExhaustiveTactic

/-!
# The no-qualified-`case` premise of `sv_exhaustive`, at a parameter point of a parametric design

`sv_exhaustive` (`LeanModels/Sv/CombExhaustiveTactic.lean`) hands its lowering theorem the premise
`hnq : (X.sem N).processes.toList.any Process2.hasQualifiedCase = false`. It builds it from the static check
`NoQ.pdQ X.pdesign` (`ProcNoQualified.lean`). The family `X.sem N` is the alias-guarded instantiation
`X.pdesign.instantiateGDAlias2 [↑N]` (`CombAlias2.lean`), and the premise is `NoQ.semAlias_noQ` with the design
passed EXPLICITLY. Left to unification, the design is a metavariable: `X.sem N` does not unfold to
`?d.instantiateGDAlias2 ?args` below the `processes` projection, so the elaboration of `(by sv_decide)` against
`NoQ.pdQ ?d = true` stopped with "Expected type must not contain metavariables". The theorems below are the
premise as the tactic now builds it, at the default point `W = 2` and at every `W`.

The design (`sv_exhaustive_param.sv`) is continuous only, so the alias guard is inert at every point
(`PDesign.instantiateGDAlias2_of_aliasInert`, `CombAliasInert.lean`), and the comb tactics read it at a symbolic
width; `sv_structure` closes the parameter agreement `hag` there from the range premise `hR` (the exact 32-bit
`int` reading of `W`).

Build: `lake build Examples.«system-verilog».sv_exhaustive_param.premise`.
-/

open LeanModels.Sv LeanModels.Sv.CombView

namespace Examples.«system-verilog».sv_exhaustive_param.premise

load_design_sv2 sv_exhaustive_param from "Examples/system-verilog/sv_exhaustive_param/sv_exhaustive_param.sv.json"

/-- The premise as `sv_exhaustive` builds it, at the default point. -/
theorem noQ_default : (sv_exhaustive_param.sem 2).processes.toList.any Process2.hasQualifiedCase = false :=
  NoQ.semAlias_noQ (d := sv_exhaustive_param.pdesign) (by sv_decide) _

/-- … at every point: the static check does not depend on the width. -/
theorem noQ_all (W : Nat) :
    (sv_exhaustive_param.sem W).processes.toList.any Process2.hasQualifiedCase = false :=
  NoQ.semAlias_noQ (d := sv_exhaustive_param.pdesign) (by sv_decide) _

/-- The alias guard is inert at every point: the family is the unguarded instantiation. -/
theorem sem_eq (W : Nat) :
    sv_exhaustive_param.sem W = sv_exhaustive_param.pdesign.instantiateGD2 [(W : Int)] :=
  PDesign.instantiateGDAlias2_of_aliasInert (by decide) _

/-- The comb profile at every width in the `int` range, by `sv_structure` on the alias-guarded family. -/
theorem comb (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    CombDesign (sv_exhaustive_param.sem W) := by
  sv_structure
  all_goals (intros; omega)

/-- info: 'Examples.«system-verilog».sv_exhaustive_param.premise.noQ_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noQ_all

/-- info: 'Examples.«system-verilog».sv_exhaustive_param.premise.comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comb

end Examples.«system-verilog».sv_exhaustive_param.premise
