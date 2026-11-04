import Mathlib.Algebra.BigOperators.Group.List.Defs
import LeanModels.Circuit.Nature

/-!
# Discipline connection semantics

Natures declare physical quantities. Disciplines additionally determine how
ports connect. Conservative ports agree on potential and conserve signed
flow; signal ports use an explicit, model-selected resolution relation.

The carrier remains an analysis interpretation parameter. In particular,
this module does not force source declarations to choose `Rat`, `Real`, or
`Complex`.
-/

namespace LeanModels.Circuit

/-- One conservative port's quantities at a single observation point. -/
structure ConservativePortValue (Potential Flow : Type) where
  potential : Potential
  flow : Flow

/-- Every connected conservative terminal observes the same potential. -/
def PotentialsAgree {Potential Flow : Type} [DecidableEq Potential]
    (ports : List (ConservativePortValue Potential Flow)) : Prop :=
  match ports with
  | [] => True
  | first :: rest => ∀ port ∈ rest, port.potential = first.potential

/-- The algebraic sum of oriented terminal flows is zero. -/
def FlowsConserve {Potential Flow : Type} [AddCommMonoid Flow]
    (ports : List (ConservativePortValue Potential Flow)) : Prop :=
  (ports.map (·.flow)).sum = 0

/-- The wiring law for a conservative node. -/
def ConservativeConnection {Potential Flow : Type}
    [DecidableEq Potential] [AddCommMonoid Flow]
    (ports : List (ConservativePortValue Potential Flow)) : Prop :=
  PotentialsAgree ports ∧ FlowsConserve ports

/-- Signal disciplines connect through an explicit resolution relation.
They are not encoded as a degenerate conservative discipline. -/
structure SignalResolution (Driver Receiver : Type) where
  resolves : List Driver → Receiver → Prop

end LeanModels.Circuit
