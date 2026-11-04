import Mathlib.Data.Real.Basic

/-!
# Dense and hybrid time

Continuous DAE capabilities use `DenseTrace`. `HybridTime` is the common
timeline available to future event-driven mixed-signal semantics; its
microstep distinguishes multiple ordered events at one physical time.
-/

namespace LeanModels.Circuit

/-- Superdense time: physical time plus an event-order microstep. -/
structure HybridTime where
  physical : ℝ
  microstep : Nat

/-- A continuous-time trace used by dense DAE capabilities. -/
abbrev DenseTrace (Value : Type) := ℝ → Value

/-- A trace that can represent multiple discrete updates at one physical
instant. -/
abbrev HybridTrace (Value : Type) := HybridTime → Value

/-- Predicate `property` holds throughout the closed interval `[0, horizon]`. -/
def Throughout (horizon : ℝ) (property : ℝ → Prop) : Prop :=
  ∀ time, 0 ≤ time → time ≤ horizon → property time

end LeanModels.Circuit
