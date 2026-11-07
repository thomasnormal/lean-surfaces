import LeanModels.Refine.Commit

/-!
# Cycle-to-retirement refinement

`Machine` in `Commit.lean` describes an architectural step: one call consumes
one input and produces one retirement.  A clocked core has a different shape:
it may spend any number of cycles between commits, and a cycle with no commit
must leave the architectural state unchanged.  `CycleMachine` is that small
stuttering view.  It is an observation interface, not a second SV semantics.

`retireInputs` keeps the inputs presented on cycles that retire.  The theorem
`cycle_trace_refines` then compares the core's filtered retirement stream with
the ISA machine run on exactly those inputs.  The relation quantifies over
every admitted input and over every cycle; no scheduler or unknown-value
choice is hidden by this bridge.
-/

namespace LeanModels.Refine

/-! ## A cycle machine and its filtered stream -/

/-- A clocked machine may stutter (`none`) or retire one observation per cycle.
The one-retirement-per-cycle shape is the commit boundary; a later interface
can replace `Option` with a finite retirement packet without changing the
architectural observation type. -/
structure CycleMachine (State : Type) where
  init : State
  step : State → Input → State × Option Retirement

/-- Keep only observations produced by a finite cycle trace. -/
def cycleTrace {State : Type} (m : CycleMachine State) : State → List Input → List Retirement
  | _, [] => []
  | s, input :: inputs =>
      let (s', observation) := m.step s input
      match observation with
      | none => cycleTrace m s' inputs
      | some retirement => retirement :: cycleTrace m s' inputs

/-- The input presented on each cycle that produced a retirement. -/
def retireInputs {State : Type} (m : CycleMachine State) : State → List Input → List Input
  | _, [] => []
  | s, input :: inputs =>
      let (s', observation) := m.step s input
      match observation with
      | none => retireInputs m s' inputs
      | some _ => input :: retireInputs m s' inputs

/-! ## State-threaded cycle windows -/

/-- The cycle-machine state after a finite window, including stuttering
cycles.  The observation stream is discarded so an adjacent window can be
continued from the exact state reached by the first one. -/
def cycleStateAfter {State : Type} (m : CycleMachine State) :
    State → List Input → State
  | state, [] => state
  | state, input :: inputs =>
      cycleStateAfter m (m.step state input).1 inputs

theorem cycleStateAfter_append {State : Type}
    (m : CycleMachine State) (state : State)
    (first second : List Input) :
    cycleStateAfter m state (first ++ second) =
      cycleStateAfter m (cycleStateAfter m state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : m.step state input with
      | mk state' observation =>
          simp only [List.cons_append, cycleStateAfter, hstep]
          exact ih state'

theorem cycleTrace_append {State : Type}
    (m : CycleMachine State) (state : State)
    (first second : List Input) :
    cycleTrace m state (first ++ second) =
      cycleTrace m state first ++
        cycleTrace m (cycleStateAfter m state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : m.step state input with
      | mk state' observation =>
          simp only [List.cons_append, cycleTrace, cycleStateAfter, hstep]
          cases observation with
          | none =>
              change cycleTrace m state' (first ++ second) =
                cycleTrace m state' first ++
                  cycleTrace m (cycleStateAfter m state' first) second
              exact ih state'
          | some retirement =>
              change retirement :: cycleTrace m state' (first ++ second) =
                (retirement :: cycleTrace m state' first) ++
                  cycleTrace m (cycleStateAfter m state' first) second
              rw [ih state']
              simp only [List.cons_append]

theorem retireInputs_append {State : Type}
    (m : CycleMachine State) (state : State)
    (first second : List Input) :
    retireInputs m state (first ++ second) =
      retireInputs m state first ++
        retireInputs m (cycleStateAfter m state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : m.step state input with
      | mk state' observation =>
          simp only [List.cons_append, retireInputs, cycleStateAfter, hstep]
          cases observation with
          | none =>
              change retireInputs m state' (first ++ second) =
                retireInputs m state' first ++
                  retireInputs m (cycleStateAfter m state' first) second
              exact ih state'
          | some retirement =>
              change input :: retireInputs m state' (first ++ second) =
                (input :: retireInputs m state' first) ++
                  retireInputs m (cycleStateAfter m state' first) second
              rw [ih state']
              simp only [List.cons_append]

theorem cycleTrace_length_eq_retireInputs_length {State : Type}
    (m : CycleMachine State) (state : State) (inputs : List Input) :
    (cycleTrace m state inputs).length =
      (retireInputs m state inputs).length := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input inputs ih =>
      cases hstep : m.step state input with
      | mk state' observation =>
          simp only [cycleTrace, retireInputs, hstep]
          cases observation with
          | none => exact ih state'
          | some retirement =>
              simp only [List.length_cons]
              rw [ih state']

@[simp] theorem cycleTrace_nil {State : Type} (m : CycleMachine State) (s : State) :
    cycleTrace m s [] = [] := rfl

@[simp] theorem retireInputs_nil {State : Type} (m : CycleMachine State) (s : State) :
    retireInputs m s [] = [] := rfl

/-! ## The cycle-level forward simulation -/

/-- A cycle-level core relation.  On a stuttering cycle the ISA state is
unchanged.  On a retiring cycle the ISA takes exactly one step on that cycle's
input and the emitted observation agrees with it. -/
def CycleStepRefines {CoreState IsaState : Type}
    (core : CycleMachine CoreState) (isa : Machine IsaState)
    (rel : CoreState → IsaState → Prop) (admit : Input → Prop) : Prop :=
  rel core.init isa.init ∧
    ∀ (c : CoreState) (a : IsaState) (input : Input),
      rel c a → admit input →
      let (c', observation) := core.step c input
      match observation with
      | none => rel c' a
      | some coreRetirement =>
          let (a', isaRetirement) := isa.step a input
          rel c' a' ∧ coreRetirement = isaRetirement

/-! ## The finite trace theorem -/

theorem cycle_trace_refines {CoreState IsaState : Type}
    {core : CycleMachine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines core isa rel admit) :
    ∀ (c : CoreState) (a : IsaState) (inputs : List Input),
      rel c a → (∀ i ∈ inputs, admit i) →
      cycleTrace core c inputs = trace isa a (retireInputs core c inputs) := by
  intro c a inputs hrel
  induction inputs generalizing c a with
  | nil =>
      intro _
      rfl
  | cons input rest ih =>
      intro hall
      have hi : admit input := hall input (by simp)
      have hrest : ∀ i ∈ rest, admit i := by
        intro i hi'
        exact hall i (by simp [hi'])
      have hs := h.2 c a input hrel hi
      rcases hC : core.step c input with ⟨c', observation⟩
      simp only [cycleTrace, retireInputs, hC]
      simp only [hC] at hs
      cases observation with
      | none =>
          exact ih c' a hs hrest
      | some coreRetirement =>
          rcases hI : isa.step a input with ⟨a', isaRetirement⟩
          simp only [trace, hI]
          simp only [hI] at hs
          rcases hs with ⟨hrel', hRetirement⟩
          rw [hRetirement, ih c' a' hrel' hrest]

theorem cycleStateAfter_refines {CoreState IsaState : Type}
    {core : CycleMachine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Prop} {admit : Input → Prop}
    (h : CycleStepRefines core isa rel admit) :
    ∀ (coreState : CoreState) (isaState : IsaState) (inputs : List Input),
      rel coreState isaState →
      (∀ i ∈ inputs, admit i) →
      rel (cycleStateAfter core coreState inputs)
        (machineStateAfter isa isaState
          (retireInputs core coreState inputs)) := by
  intro coreState isaState inputs hrel
  induction inputs generalizing coreState isaState with
  | nil =>
      intro _
      exact hrel
  | cons input rest ih =>
      intro hall
      have hi : admit input := hall input (by simp)
      have hrest : ∀ i ∈ rest, admit i := by
        intro i hi'
        exact hall i (by simp [hi'])
      have hs := h.2 coreState isaState input hrel hi
      rcases hC : core.step coreState input with ⟨coreState', observation⟩
      simp only [cycleStateAfter, retireInputs, hC]
      simp only [hC] at hs
      cases observation with
      | none =>
          exact ih coreState' isaState hs hrest
      | some coreRetirement =>
          rcases hI : isa.step isaState input with ⟨isaState', isaRetirement⟩
          simp only [machineStateAfter, hI]
          simp only [hI] at hs
          rcases hs with ⟨hrel', hRetirement⟩
          exact ih coreState' isaState' hrel' hrest

end LeanModels.Refine

#print axioms LeanModels.Refine.cycle_trace_refines
#print axioms LeanModels.Refine.cycleStateAfter_refines
#print axioms LeanModels.Refine.cycleStateAfter_append
#print axioms LeanModels.Refine.cycleTrace_append
#print axioms LeanModels.Refine.retireInputs_append
#print axioms LeanModels.Refine.cycleTrace_length_eq_retireInputs_length
