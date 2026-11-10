import LeanModels.Sv.Sva

/-!
# F2 — invariant safety over a transition system

This is the proof-side seam for unbounded safety. An E route supplies
`init`, one-cycle `step`, and the sampled assertion predicate `safe`; this
file supplies the induction rule. It contains no execution fuel and names
no run2 judgment. Concrete finite counterexamples remain evaluated by
`SvaCheck.evalEdges` in `Sva.lean`.
-/

namespace LeanModels.Sv

set_option autoImplicit false

structure SafetySystem where
  State : Type
  Input : Type
  init : State → Prop
  step : State → Input → State
  invariant : State → Prop
  safe : State → Prop

/-! A trace is a finite prefix of the system's unbounded transition relation.
The recursion is on the supplied input prefix, not a semantic fuel bound. -/
inductive SafetyTrace (S : SafetySystem) : S.State → List S.Input → S.State → Prop where
  | nil (s : S.State) : SafetyTrace S s [] s
  | cons {s : S.State} {u : S.Input} {us : List S.Input} {t : S.State} :
      SafetyTrace S (S.step s u) us t → SafetyTrace S s (u :: us) t

theorem invariant_from (S : SafetySystem)
    (hstep : ∀ s u, S.invariant s → S.invariant (S.step s u)) :
    ∀ {s t : S.State} {us : List S.Input},
      S.invariant s → SafetyTrace S s us t → S.invariant t
  | _, _, [], hs, .nil _ => hs
  | s, _, u :: us, hs, .cons htail =>
      invariant_from S hstep (hstep s u hs) htail

/-! Unbounded safety from reset: the base case establishes the invariant, the
one-cycle rule preserves it, and the invariant implies the sampled property. -/
theorem safe_of_trace (S : SafetySystem)
    (hinit : ∀ s, S.init s → S.invariant s)
    (hstep : ∀ s u, S.invariant s → S.invariant (S.step s u))
    (hsafe : ∀ s, S.invariant s → S.safe s)
    {s₀ s : S.State} {us : List S.Input}
    (hi : S.init s₀) (hr : SafetyTrace S s₀ us s) : S.safe s :=
  hsafe s (invariant_from S hstep (hinit s₀ hi) hr)

/-! A reset-preserving kernel-checked shape test for the F2 route. -/
namespace SafetySmoke

def resetSystem : SafetySystem where
  State := Bool
  Input := Bool
  init q := q = false
  step q reset := if reset then false else q
  invariant q := q = false
  safe q := q = false

theorem reset_invariant (q : Bool) (h : resetSystem.init q) :
    resetSystem.invariant q := h

theorem reset_step (q reset : Bool) (h : resetSystem.invariant q) :
    resetSystem.invariant (resetSystem.step q reset) := by
  simp only [resetSystem] at h ⊢
  cases reset <;> simp [h]

theorem reset_trace_safe {q : Bool} {us : List Bool}
    (hr : SafetyTrace resetSystem false us q) : resetSystem.safe q := by
  apply safe_of_trace resetSystem reset_invariant reset_step
    (fun q h => h) (s₀ := false) (s := q) (us := us)
  rfl
  exact hr

/-! A bounded counter-shaped invariant witness.  This is still an abstract
transition system; the later E elaborator will supply the concrete state and
one-cycle step for an RTL target. -/

def boundedCounter : SafetySystem where
  State := Nat
  Input := Bool
  init q := q = 0
  step q _ := if q = 3 then 0 else q + 1
  invariant q := q ≤ 3
  safe q := q ≤ 3

theorem boundedCounter_init (q : Nat) (h : boundedCounter.init q) :
    boundedCounter.invariant q := by
  simp only [boundedCounter] at h ⊢
  omega

theorem boundedCounter_step (q : Nat) (u : Bool)
    (h : boundedCounter.invariant q) :
    boundedCounter.invariant (boundedCounter.step q u) := by
  simp only [boundedCounter] at h ⊢
  split <;> omega

theorem boundedCounter_trace_safe {q : Nat} {us : List Bool}
    (hr : SafetyTrace boundedCounter (0 : Nat) us q) : boundedCounter.safe q := by
  apply safe_of_trace boundedCounter boundedCounter_init boundedCounter_step
    (fun q h => h) (s₀ := (0 : Nat)) (s := q) (us := us)
  exact rfl
  exact hr

end SafetySmoke

end LeanModels.Sv
