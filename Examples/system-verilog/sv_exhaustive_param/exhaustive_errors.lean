import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombExhaustiveTactic

/-!
# `sv_exhaustive` on a parametric design: refused, with the reason

`sv_exhaustive` decides a netlist WITHOUT parameters: it instantiates the design at the empty argument list and evaluates
every output exhaustively. On a parametric design (here `W`, the width) it used to stop deep inside with "a site is
outside the bitwise fragment", the parameter being unbound at the empty argument list; it now refuses up front, naming the
parameters and the routes that do apply: `sv_structure` and `sv_equations` for every width, and at a parameter point the
premise `NoQ.semAlias_noQ (d := X.pdesign)` of `premise.lean` (`X.sem N` is the alias-guarded family: the unguarded
`NoQ.sem_noQ` leaves the design a metavariable, the elaboration error "Expected type must not contain metavariables").
-/

open LeanModels.Sv

namespace Examples.«system-verilog».sv_exhaustive_param.exhaustive_errors

load_design_sv2 sv_exhaustive_param from "Examples/system-verilog/sv_exhaustive_param/sv_exhaustive_param.sv.json"

/--
error: sv_exhaustive: the design has the parameter(s) [W]; `sv_exhaustive` decides a netlist without parameters (it instantiates the design at the empty argument list and evaluates it exhaustively), so a parametric design is outside it. Prove a parametric design for every parameter value with `sv_structure` and `sv_equations`; at a parameter point, the no-qualified-`case` premise is `NoQ.semAlias_noQ (d := X.pdesign) (by decide) _` (`X.sem N` is the alias-guarded family, so `NoQ.sem_noQ` does not apply to it), see `Examples/system-verilog/sv_exhaustive_param/premise.lean`
-/
#guard_msgs (whitespace := lax) in
example : ∀ st : SvState, (sv_exhaustive_param.sem 2).decls = (sv_exhaustive_param.sem 2).decls := by
  sv_exhaustive

/-- The premise at the default point, with the design passed (the form the message names). -/
example : (sv_exhaustive_param.sem 2).processes.toList.any Process2.hasQualifiedCase = false :=
  NoQ.semAlias_noQ (d := sv_exhaustive_param.pdesign) (by decide) _

end Examples.«system-verilog».sv_exhaustive_param.exhaustive_errors
