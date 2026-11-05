import LeanModels.Refine.Cycle

/-!
# Packet-level cycle refinement

`CycleMachine` handles one retirement at most per cycle.  Superscalar cores
and some RVFI configurations commit a finite packet instead.  This file
keeps the architectural observation unchanged and adds only the packet
boundary: each emitted retirement carries the `Input` on which its ISA step
is checked.  A packet may be empty, singleton, or wider without choosing a
microarchitectural order; the proof contract states the order in which the
core presents its committed entries.

`packet_trace_refines` is the finite-prefix theorem consumed by a later
out-of-order or multi-issue core proof.  It quantifies over every packet
entry admitted by the core relation.  No fairness or progress assumption is
smuggled in: an empty packet is a valid stutter, and liveness is a separate
contract.
-/

namespace LeanModels.Refine

/-! ## Packets and their architectural interpretation -/

/-- A committed entry paired with the architectural input it refines. -/
abbrev CommitPacket := List (Input × Retirement)

/-- A cycle machine that may emit a finite ordered commit packet. -/
structure PacketMachine (State : Type) where
  init : State
  step : State → Input → State × CommitPacket

/-- The retirement stream of a packet machine over a finite cycle prefix. -/
def packetTrace {State : Type} (machine : PacketMachine State) :
    State → List Input → List Retirement
  | _, [] => []
  | state, input :: inputs =>
      let (state', packet) := machine.step state input
      packet.map Prod.snd ++ packetTrace machine state' inputs

/-- The ISA inputs represented by the emitted packets, in commit order. -/
def packetInputs {State : Type} (machine : PacketMachine State) :
    State → List Input → List Input
  | _, [] => []
  | state, input :: inputs =>
      let (state', packet) := machine.step state input
      packet.map Prod.fst ++ packetInputs machine state' inputs

/-! ## State-threaded packet windows -/

/-- The packet-machine state after a finite cycle window.  Packet contents are
discarded here; the state is retained so an adjacent window can continue the
same core run. -/
def packetStateAfter {State : Type} (machine : PacketMachine State) :
    State → List Input → State
  | state, [] => state
  | state, input :: inputs =>
      packetStateAfter machine (machine.step state input).1 inputs

theorem packetStateAfter_append {State : Type}
    (machine : PacketMachine State) (state : State)
    (first second : List Input) :
    packetStateAfter machine state (first ++ second) =
      packetStateAfter machine
        (packetStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' packet =>
          simp only [List.cons_append, packetStateAfter, hstep]
          exact ih state'

theorem packetTrace_append {State : Type}
    (machine : PacketMachine State) (state : State)
    (first second : List Input) :
    packetTrace machine state (first ++ second) =
      packetTrace machine state first ++
        packetTrace machine (packetStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' packet =>
          simp only [List.cons_append, packetTrace, packetStateAfter, hstep]
          rw [ih state']
          rw [List.append_assoc]

theorem packetInputs_append {State : Type}
    (machine : PacketMachine State) (state : State)
    (first second : List Input) :
    packetInputs machine state (first ++ second) =
      packetInputs machine state first ++
        packetInputs machine (packetStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' packet =>
          simp only [List.cons_append, packetInputs, packetStateAfter, hstep]
          rw [ih state']
          rw [List.append_assoc]

/-! ## One packet against the ISA -/

/-- Every packet entry is one ISA step, and the final ISA state is threaded
through the entries in the packet's committed order. -/
inductive PacketRefines {IsaState : Type} (isa : Machine IsaState)
    (admit : Input → Prop) : IsaState → CommitPacket → IsaState → Prop where
  | nil (state : IsaState) : PacketRefines isa admit state [] state
  | cons {state state₁ state₂ : IsaState} {input : Input}
      {coreRetirement isaRetirement : Retirement} {rest : CommitPacket}
      (hi : admit input)
      (hstep : isa.step state input = (state₁, isaRetirement))
      (hretirement : coreRetirement = isaRetirement)
      (htail : PacketRefines isa admit state₁ rest state₂) :
      PacketRefines isa admit state ((input, coreRetirement) :: rest) state₂

theorem packet_refines_trace_append {IsaState : Type}
    {isa : Machine IsaState} {admit : Input → Prop}
    {state state' : IsaState} {packet : CommitPacket} :
    PacketRefines isa admit state packet state' →
      ∀ (tail : List Input),
        trace isa state (packet.map Prod.fst ++ tail) =
          packet.map Prod.snd ++ trace isa state' tail := by
  intro h
  induction h with
  | nil state => intro tail; rfl
  | @cons state state₁ state₂ input coreRetirement isaRetirement rest hi hstep hretirement htail ih =>
      intro tail
      simp only [List.map_cons, List.cons_append, trace, hstep]
      rw [hretirement, ih]

theorem packet_refines_trace {IsaState : Type}
    {isa : Machine IsaState} {admit : Input → Prop}
    {state state' : IsaState} {packet : CommitPacket} :
    PacketRefines isa admit state packet state' →
      packet.map Prod.snd = trace isa state (packet.map Prod.fst) := by
  intro h
  simpa [trace] using (packet_refines_trace_append h []).symm

/-! ## Cycle-level forward simulation and trace theorem -/

/-- A packet machine's one-cycle contract.  The cycle input is an environment
value; only entries actually emitted by the core become architectural steps. -/
def PacketStepRefines {CoreState IsaState : Type}
    (core : PacketMachine CoreState) (isa : Machine IsaState)
    (rel : CoreState → IsaState → Prop) (admit : Input → Prop) : Prop :=
  rel core.init isa.init ∧
    ∀ (coreState : CoreState) (isaState : IsaState) (cycleInput : Input),
      rel coreState isaState →
      let (coreState', packet) := core.step coreState cycleInput
      ∃ isaState', rel coreState' isaState' ∧
        PacketRefines isa admit isaState packet isaState'

/-- Equality of finite committed streams for zero-, one-, or multi-retirement
cycles. -/
theorem packet_trace_refines {CoreState IsaState : Type}
    {core : PacketMachine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Prop} {admit : Input → Prop}
    (h : PacketStepRefines core isa rel admit) :
    ∀ (coreState : CoreState) (isaState : IsaState) (cycles : List Input),
      rel coreState isaState →
      packetTrace core coreState cycles =
        trace isa isaState (packetInputs core coreState cycles) := by
  intro coreState isaState cycles hrel
  induction cycles generalizing coreState isaState with
  | nil => rfl
  | cons cycleInput rest ih =>
      have hs := h.2 coreState isaState cycleInput hrel
      rcases hC : core.step coreState cycleInput with ⟨coreState', packet⟩
      simp only [packetTrace, packetInputs, hC]
      simp only [hC] at hs
      rcases hs with ⟨isaState', hrel', hpacket⟩
      rw [packet_refines_trace_append hpacket, ih coreState' isaState' hrel']

end LeanModels.Refine

#print axioms LeanModels.Refine.packet_trace_refines
#print axioms LeanModels.Refine.packetStateAfter_append
#print axioms LeanModels.Refine.packetTrace_append
#print axioms LeanModels.Refine.packetInputs_append
