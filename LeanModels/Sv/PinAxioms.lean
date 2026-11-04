import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# `#pin_axioms`

`#pin_axioms c₁ c₂ …`: an error unless every named constant depends on at most `propext`, `Classical.choice` and
`Quot.sound`; silent when it does. One command stands for one `#print axioms` pin per constant (moved here from
`CombProcEq.lean` so that the recognizer files below it can use it).
-/

open Lean Elab Command in
/-- `#pin_axioms c₁ c₂ …`: an error unless every named constant depends on at most `propext`,
`Classical.choice` and `Quot.sound`; silent when it does. -/
elab "#pin_axioms " ids:ident* : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
        throwErrorAt id m!"'{n}' depends on the axiom '{a}'"
