import LeanModels.Sv.Kernel.Core0E
import LeanModels.Sv.ObserveE

namespace LeanModels.Sv.Kernel

open LeanModels.Sv.Observe

set_option autoImplicit false

def inputSigsE (d : Design2) : List Sig :=
  d.decls.toList.filterMap fun dc => if dc.isInput then some (dc.name, dc.width) else none

def outputSigsE (d : Design2) : List Sig :=
  d.decls.toList.filterMap fun dc => if dc.isOutput then some (dc.name, dc.width) else none

/-! ## The backend -/

/-- The entry of slot `t`: slot `2c` carries entry `c`, slot `2c + 1` none. -/
def slotEntry (env : List SvState) (t : Nat) : SvState :=
  if t % 2 = 0 then (env[t / 2]?).getD [] else []

/-- **A behaviour of E-core-0** under an environment: slot `t` closes at `cfg t`, from time zero,
each slot opened by its input events. -/
def Behaves0 (E : Elab) (env : List SvState) (ch : Choice) (cfg : Nat → Config) : Prop :=
  SlotCloses E ch (Config.start E (slotEntry env 0)) (cfg 0) ∧
  ∀ t, SlotCloses E ch (Config.nextSlot E (cfg t) (slotEntry env (t + 1))) (cfg (t + 1))

/-- **E-core-0 as an `ESig`** (agent P's signature): two slots per cycle, the sample slot odd. -/
def E0 : ESig where
  Elab := Elab
  Choice := Choice
  Env := List SvState
  Config := SvState
  iface e := ⟨inputSigsE e.toDesign2, outputSigsE e.toDesign2⟩
  Disciplined _ _ := True
  read := SvState.lookup
  Behaves e env ch b := ∃ cfg, Behaves0 e env ch cfg ∧ ∀ t, b t = e.view (cfg t).store
  preponed b t := b (t - 1)
  cycles env := env.length
  edgeSlot _ c := 2 * c + 1

/-- **`Obs_E0`**: E-core-0 as an observation backend. -/
abbrev Obs_E0 : ObservationModel := Obs_E E0

/- The E wrapper is reducible, so backend-specific proofs can rewrite the
   observation directly instead of composing opaque `sample` facts. -/
example (E : Elab) (st : SvState) :
    Obs_E0.sample E st = (Obs_E E0).sample E st := rfl


end LeanModels.Sv.Kernel
