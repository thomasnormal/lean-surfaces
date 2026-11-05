import LeanModels.Refine.Packet

/-!
# Flush-aware cycle refinement

Speculative cores may discard a branch, replay a load, or otherwise flush
microarchitectural state without retiring an architectural instruction.  A
plain packet machine can model this as a bubble, but naming the event keeps
the proof obligation visible: a flush may change the core state while the ISA
state and the committed stream stay unchanged.

`FlushStepRefines` adds that event to the same exact packet semantics.  The
finite theorem is safety-only and quantifies over every cycle; progress still
belongs to `Progress.lean`.
-/

namespace LeanModels.Refine

inductive FlushEvent where
  | flush
  | retire (packet : CommitPacket)

structure FlushMachine (State : Type) where
  init : State
  step : State → Input → State × FlushEvent

def flushTrace {State : Type} (machine : FlushMachine State) :
    State → List Input → List Retirement
  | _, [] => []
  | state, input :: inputs =>
      let (state', event) := machine.step state input
      match event with
      | .flush => flushTrace machine state' inputs
      | .retire packet =>
          packet.map Prod.snd ++ flushTrace machine state' inputs

def flushInputs {State : Type} (machine : FlushMachine State) :
    State → List Input → List Input
  | _, [] => []
  | state, input :: inputs =>
      let (state', event) := machine.step state input
      match event with
      | .flush => flushInputs machine state' inputs
      | .retire packet =>
          packet.map Prod.fst ++ flushInputs machine state' inputs

/-! ## State-threaded flush windows -/

/-- The state after a finite flush/retirement window.  Flushes still advance
the core state even though they contribute no architectural input. -/
def flushStateAfter {State : Type} (machine : FlushMachine State) :
    State → List Input → State
  | state, [] => state
  | state, input :: inputs =>
      flushStateAfter machine (machine.step state input).1 inputs

theorem flushStateAfter_append {State : Type}
    (machine : FlushMachine State) (state : State)
    (first second : List Input) :
    flushStateAfter machine state (first ++ second) =
      flushStateAfter machine
        (flushStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' event =>
          simp only [List.cons_append, flushStateAfter, hstep]
          exact ih state'

theorem flushTrace_append {State : Type}
    (machine : FlushMachine State) (state : State)
    (first second : List Input) :
    flushTrace machine state (first ++ second) =
      flushTrace machine state first ++
        flushTrace machine (flushStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' event =>
          simp only [List.cons_append, flushTrace, flushStateAfter, hstep]
          cases event with
          | flush =>
              change flushTrace machine state' (first ++ second) =
                flushTrace machine state' first ++
                  flushTrace machine (flushStateAfter machine state' first) second
              exact ih state'
          | retire packet =>
              change packet.map Prod.snd ++ flushTrace machine state' (first ++ second) =
                (packet.map Prod.snd ++ flushTrace machine state' first) ++
                  flushTrace machine (flushStateAfter machine state' first) second
              rw [ih state']
              rw [List.append_assoc]

theorem flushInputs_append {State : Type}
    (machine : FlushMachine State) (state : State)
    (first second : List Input) :
    flushInputs machine state (first ++ second) =
      flushInputs machine state first ++
        flushInputs machine (flushStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' event =>
          simp only [List.cons_append, flushInputs, flushStateAfter, hstep]
          cases event with
          | flush =>
              change flushInputs machine state' (first ++ second) =
                flushInputs machine state' first ++
                  flushInputs machine (flushStateAfter machine state' first) second
              exact ih state'
          | retire packet =>
              change packet.map Prod.fst ++ flushInputs machine state' (first ++ second) =
                (packet.map Prod.fst ++ flushInputs machine state' first) ++
                  flushInputs machine (flushStateAfter machine state' first) second
              rw [ih state']
              rw [List.append_assoc]

def FlushStepRefines {CoreState IsaState : Type}
    (core : FlushMachine CoreState) (isa : Machine IsaState)
    (rel : CoreState → IsaState → Prop) (admit : Input → Prop) : Prop :=
  rel core.init isa.init ∧
    ∀ (coreState : CoreState) (isaState : IsaState) (cycleInput : Input),
      rel coreState isaState →
      let (coreState', event) := core.step coreState cycleInput
      match event with
      | .flush => rel coreState' isaState
      | .retire packet =>
          ∃ isaState', rel coreState' isaState' ∧
            PacketRefines isa admit isaState packet isaState'

theorem flush_trace_refines {CoreState IsaState : Type}
    {core : FlushMachine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Prop} {admit : Input → Prop}
    (h : FlushStepRefines core isa rel admit) :
    ∀ (coreState : CoreState) (isaState : IsaState) (cycles : List Input),
      rel coreState isaState →
      flushTrace core coreState cycles =
        trace isa isaState (flushInputs core coreState cycles) := by
  intro coreState isaState cycles hrel
  induction cycles generalizing coreState isaState with
  | nil => rfl
  | cons cycleInput rest ih =>
      have hs := h.2 coreState isaState cycleInput hrel
      rcases hC : core.step coreState cycleInput with ⟨coreState', event⟩
      simp only [flushTrace, flushInputs, hC]
      simp only [hC] at hs
      cases event with
      | flush =>
          exact ih coreState' isaState hs
      | retire packet =>
          rcases hs with ⟨isaState', hrel', hpacket⟩
          rw [packet_refines_trace_append hpacket,
            ih coreState' isaState' hrel']

theorem flushStateAfter_refines {CoreState IsaState : Type}
    {core : FlushMachine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Prop} {admit : Input → Prop}
    (h : FlushStepRefines core isa rel admit) :
    ∀ (coreState : CoreState) (isaState : IsaState) (cycles : List Input),
      rel coreState isaState →
      rel (flushStateAfter core coreState cycles)
        (machineStateAfter isa isaState
          (flushInputs core coreState cycles)) := by
  intro coreState isaState cycles hrel
  induction cycles generalizing coreState isaState with
  | nil => exact hrel
  | cons cycleInput rest ih =>
      have hs := h.2 coreState isaState cycleInput hrel
      rcases hC : core.step coreState cycleInput with ⟨coreState', event⟩
      simp only [flushStateAfter, flushInputs, hC]
      simp only [hC] at hs
      cases event with
      | flush =>
          exact ih coreState' isaState hs
      | retire packet =>
          rcases hs with ⟨isaState', hrel', hpacket⟩
          have hstate := packet_refines_state hpacket
          rw [machineStateAfter_append, ← hstate]
          exact ih coreState' isaState' hrel'

end LeanModels.Refine

#print axioms LeanModels.Refine.flush_trace_refines
#print axioms LeanModels.Refine.flushStateAfter_refines
#print axioms LeanModels.Refine.flushStateAfter_append
#print axioms LeanModels.Refine.flushTrace_append
#print axioms LeanModels.Refine.flushInputs_append
