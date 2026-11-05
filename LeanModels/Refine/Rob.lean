import LeanModels.Refine.Packet

/-!
# Reorder-buffer commit order

Out-of-order completion is an implementation detail only while retirement is
in order.  `TaggedCommit` records the architectural sequence number carried by
one commit entry.  `TaggedPacketRefines` requires a packet's tags to be the
consecutive prefix beginning at the relation's `nextOrder`, then reuses
`PacketRefines` for the architectural effects.

`RobStepRefines` threads `nextOrder` through the core/ISA relation and requires
the next value to advance by exactly the packet width.  The resulting
`rob_trace_refines` theorem therefore covers bubbles, single retirement, and
multi-retirement while leaving completion order and buffering inside the core
state.  A real core proves this order certificate from its ROB invariant; this
file does not choose a scheduling policy or hide nondeterminism.
-/

namespace LeanModels.Refine

/-! ## Tagged commit packets -/

structure TaggedCommit where
  order : Nat
  input : Input
  retirement : Retirement

abbrev TaggedPacket := List TaggedCommit

def TaggedCommit.payload (entry : TaggedCommit) : Input × Retirement :=
  (entry.input, entry.retirement)

@[simp] theorem map_payload_fst (packet : TaggedPacket) :
    (packet.map TaggedCommit.payload).map Prod.fst =
      packet.map TaggedCommit.input := by
  induction packet with
  | nil => rfl
  | cons entry rest ih =>
      simp [TaggedCommit.payload, ih]

@[simp] theorem map_payload_snd (packet : TaggedPacket) :
    (packet.map TaggedCommit.payload).map Prod.snd =
      packet.map TaggedCommit.retirement := by
  induction packet with
  | nil => rfl
  | cons entry rest ih =>
      simp [TaggedCommit.payload, ih]

/-- The tag sequence expected for a packet of a given width. -/
def orderPrefix : Nat → Nat → List Nat
  | _, 0 => []
  | start, n + 1 => start :: orderPrefix (start + 1) n

@[simp] theorem orderPrefix_zero (start : Nat) : orderPrefix start 0 = [] := rfl

@[simp] theorem orderPrefix_succ (start n : Nat) :
    orderPrefix start (n + 1) = start :: orderPrefix (start + 1) n := rfl

/-- A packet's tags are exactly the consecutive sequence beginning at `start`.
This is the logical ROB commit-order invariant; completion may occur in any
other order inside the core state. -/
def InOrderTags (start : Nat) (packet : TaggedPacket) : Prop :=
  packet.map TaggedCommit.order = orderPrefix start packet.length

theorem inOrderTags_orders {start : Nat} {packet : TaggedPacket}
    (h : InOrderTags start packet) :
    packet.map TaggedCommit.order = orderPrefix start packet.length := h

/-- A tagged packet refines the ISA when its tag certificate and its erased
architectural packet both refine. -/
def TaggedPacketRefines {IsaState : Type}
    (isa : Machine IsaState) (admit : Input → Prop)
    (start : Nat) (state : IsaState) (packet : TaggedPacket)
    (state' : IsaState) : Prop :=
  InOrderTags start packet ∧
    PacketRefines isa admit state (packet.map TaggedCommit.payload) state'

theorem tagged_packet_refines_trace_append {IsaState : Type}
    {isa : Machine IsaState} {admit : Input → Prop}
    {start : Nat} {state state' : IsaState} {packet : TaggedPacket}
    (h : TaggedPacketRefines isa admit start state packet state')
    (tail : List Input) :
    trace isa state ((packet.map TaggedCommit.payload).map Prod.fst ++ tail) =
      (packet.map TaggedCommit.payload).map Prod.snd ++ trace isa state' tail := by
  exact packet_refines_trace_append h.2 tail

theorem tagged_packet_refines_trace {IsaState : Type}
    {isa : Machine IsaState} {admit : Input → Prop}
    {start : Nat} {state state' : IsaState} {packet : TaggedPacket}
    (h : TaggedPacketRefines isa admit start state packet state') :
    (packet.map TaggedCommit.payload).map Prod.snd =
      trace isa state ((packet.map TaggedCommit.payload).map Prod.fst) := by
  exact packet_refines_trace h.2

theorem tagged_packet_refines_state {IsaState : Type}
    {isa : Machine IsaState} {admit : Input → Prop}
    {start : Nat} {state state' : IsaState} {packet : TaggedPacket}
    (h : TaggedPacketRefines isa admit start state packet state') :
    state' = machineStateAfter isa state (packet.map TaggedCommit.input) := by
  calc
    state' = machineStateAfter isa state
        ((packet.map TaggedCommit.payload).map Prod.fst) :=
      packet_refines_state h.2
    _ = machineStateAfter isa state (packet.map TaggedCommit.input) := by
      rw [map_payload_fst]

/-! ## A packet machine with a threaded ROB order -/

structure RobMachine (State : Type) where
  init : State
  step : State → Input → State × TaggedPacket

def robTrace {State : Type} (machine : RobMachine State) :
    State → List Input → List Retirement
  | _, [] => []
  | state, input :: inputs =>
      let (state', packet) := machine.step state input
      packet.map TaggedCommit.retirement ++ robTrace machine state' inputs

def robInputs {State : Type} (machine : RobMachine State) :
    State → List Input → List Input
  | _, [] => []
  | state, input :: inputs =>
      let (state', packet) := machine.step state input
      packet.map TaggedCommit.input ++ robInputs machine state' inputs

/-! ## State-threaded ROB windows -/

/-- The ROB state after a finite cycle window.  The packet contents are
discarded, while the exact post-window state is retained for composition. -/
def robStateAfter {State : Type} (machine : RobMachine State) :
    State → List Input → State
  | state, [] => state
  | state, input :: inputs =>
      robStateAfter machine (machine.step state input).1 inputs

theorem robStateAfter_append {State : Type}
    (machine : RobMachine State) (state : State)
    (first second : List Input) :
    robStateAfter machine state (first ++ second) =
      robStateAfter machine
        (robStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' packet =>
          simp only [List.cons_append, robStateAfter, hstep]
          exact ih state'

theorem robTrace_append {State : Type}
    (machine : RobMachine State) (state : State)
    (first second : List Input) :
    robTrace machine state (first ++ second) =
      robTrace machine state first ++
        robTrace machine (robStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' packet =>
          simp only [List.cons_append, robTrace, robStateAfter, hstep]
          rw [ih state']
          rw [List.append_assoc]

theorem robInputs_append {State : Type}
    (machine : RobMachine State) (state : State)
    (first second : List Input) :
    robInputs machine state (first ++ second) =
      robInputs machine state first ++
        robInputs machine (robStateAfter machine state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons input first ih =>
      cases hstep : machine.step state input with
      | mk state' packet =>
          simp only [List.cons_append, robInputs, robStateAfter, hstep]
          rw [ih state']
          rw [List.append_assoc]

/-- A ROB emits one retirement and retains one input for each tagged commit,
so the two architectural projections always have the same finite length. -/
theorem robTrace_length_eq_robInputs_length {State : Type}
    (machine : RobMachine State) (state : State) (cycles : List Input) :
    (robTrace machine state cycles).length =
      (robInputs machine state cycles).length := by
  induction cycles generalizing state with
  | nil => rfl
  | cons cycleInput cycles ih =>
      cases hstep : machine.step state cycleInput with
      | mk state' packet =>
          simp only [robTrace, robInputs, hstep, List.length_append,
            List.length_map]
          exact congrArg (fun n => packet.length + n) (ih state')

/-- A one-cycle ROB refinement relation.  `order'` is explicit so the core
proof cannot forget to advance the commit sequence after a packet. -/
def RobStepRefines {CoreState IsaState : Type}
    (core : RobMachine CoreState) (isa : Machine IsaState)
    (rel : CoreState → IsaState → Nat → Prop) (start : Nat)
    (admit : Input → Prop) : Prop :=
  rel core.init isa.init start ∧
    ∀ (coreState : CoreState) (isaState : IsaState) (order : Nat)
      (cycleInput : Input),
      rel coreState isaState order →
      let (coreState', packet) := core.step coreState cycleInput
      ∃ isaState' order',
        rel coreState' isaState' order' ∧
        order' = order + packet.length ∧
        TaggedPacketRefines isa admit order isaState packet isaState'

theorem rob_trace_refines {CoreState IsaState : Type}
    {core : RobMachine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Nat → Prop} {start : Nat}
    {admit : Input → Prop}
    (h : RobStepRefines core isa rel start admit) :
    ∀ (coreState : CoreState) (isaState : IsaState) (order : Nat)
      (cycles : List Input),
      rel coreState isaState order →
      robTrace core coreState cycles =
        trace isa isaState (robInputs core coreState cycles) := by
  intro coreState isaState order cycles hrel
  induction cycles generalizing coreState isaState order with
  | nil => rfl
  | cons cycleInput rest ih =>
      have hs := h.2 coreState isaState order cycleInput hrel
      rcases hC : core.step coreState cycleInput with ⟨coreState', packet⟩
      simp only [robTrace, robInputs, hC]
      simp only [hC] at hs
      rcases hs with ⟨isaState', order', hrel', horder', hpacket⟩
      rw [← map_payload_snd packet, ← map_payload_fst packet]
      rw [tagged_packet_refines_trace_append hpacket,
        ih coreState' isaState' order' hrel']

theorem robStateAfter_refines {CoreState IsaState : Type}
    {core : RobMachine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Nat → Prop} {start : Nat}
    {admit : Input → Prop}
    (h : RobStepRefines core isa rel start admit) :
    ∀ (coreState : CoreState) (isaState : IsaState) (order : Nat)
      (cycles : List Input),
      rel coreState isaState order →
      ∃ finalOrder,
        rel (robStateAfter core coreState cycles)
          (machineStateAfter isa isaState
            (robInputs core coreState cycles)) finalOrder ∧
        finalOrder = order + (robInputs core coreState cycles).length := by
  intro coreState isaState order cycles hrel
  induction cycles generalizing coreState isaState order with
  | nil =>
      exact ⟨order, hrel, by rfl⟩
  | cons cycleInput rest ih =>
      have hs := h.2 coreState isaState order cycleInput hrel
      rcases hC : core.step coreState cycleInput with ⟨coreState', packet⟩
      simp only [robStateAfter, robInputs, hC]
      simp only [hC] at hs
      rcases hs with ⟨isaState', order', hrel', horder', hpacket⟩
      rcases ih coreState' isaState' order' hrel' with
        ⟨finalOrder, hfinal, hfinalOrder⟩
      refine ⟨finalOrder, ?_, ?_⟩
      · rw [machineStateAfter_append, ← tagged_packet_refines_state hpacket]
        exact hfinal
      · rw [hfinalOrder, horder']
        simp only [List.length_append, List.length_map]
        omega

end LeanModels.Refine

#print axioms LeanModels.Refine.rob_trace_refines
#print axioms LeanModels.Refine.tagged_packet_refines_state
#print axioms LeanModels.Refine.robStateAfter_refines
#print axioms LeanModels.Refine.robStateAfter_append
#print axioms LeanModels.Refine.robTrace_append
#print axioms LeanModels.Refine.robInputs_append
#print axioms LeanModels.Refine.robTrace_length_eq_robInputs_length
