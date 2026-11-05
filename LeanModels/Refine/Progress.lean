import LeanModels.Refine.Packet
import LeanModels.Refine.Rob

/-!
# Explicit progress for finite prefixes

The finite packet theorem is a safety result: a core may emit no packet
forever and still satisfy it.  A production refinement also needs a separate
progress assumption.  This file states that assumption without importing an
infinite-trace semantics: a schedule is a `Nat → Input`, and
`RetiresTarget` says that every finite prefix of the target architectural
stream appears at some finite cycle boundary.

`progress_trace_refines` combines that certificate with
`packet_trace_refines`.  It proves exactly the finite trace prefix justified
by the witness; it makes no claim about a missing witness and hides no
fairness or scheduler choice.
-/

namespace LeanModels.Refine

/-! ## Finite prefixes of an infinite schedule -/

/-- The first `n` values of a natural-number schedule. -/
def schedulePrefix {α : Type} (schedule : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => schedule n :: schedulePrefix schedule n

@[simp] theorem schedulePrefix_zero {α : Type} (schedule : Nat → α) :
    schedulePrefix schedule 0 = [] := rfl

@[simp] theorem schedulePrefix_succ {α : Type} (schedule : Nat → α) (n : Nat) :
    schedulePrefix schedule (n + 1) =
      schedule n :: schedulePrefix schedule n := rfl

/-! ## The explicit progress certificate -/

/-- Every finite target prefix is emitted at some finite cycle boundary.  The
target may be chosen by a program/environment oracle; this definition does
not assume that the cycle schedule itself is architectural commit order. -/
def RetiresTarget {State : Type}
    (core : PacketMachine State) (initial : State)
    (schedule target : Nat → Input) : Prop :=
  ∀ k : Nat, ∃ n : Nat,
    packetInputs core initial (schedulePrefix schedule n) =
      schedulePrefix target k

/-- A packet refinement plus an explicit finite-prefix progress certificate
gives the matching ISA trace prefix at the same witness cycle. -/
theorem progress_trace_refines {CoreState IsaState : Type}
    {core : PacketMachine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Prop} {admit : Input → Prop}
    (h : PacketStepRefines core isa rel admit)
    {schedule target : Nat → Input}
    (progress : RetiresTarget core core.init schedule target) :
    ∀ k : Nat, ∃ n : Nat,
      packetTrace core core.init (schedulePrefix schedule n) =
        trace isa isa.init (schedulePrefix target k) := by
  intro k
  rcases progress k with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have htrace := packet_trace_refines h core.init isa.init
      (schedulePrefix schedule n) h.1
  rw [htrace, hn]

/-! ## Progress at a tagged ROB packet boundary -/

/-- Concatenate the first `n` target packets in chronological order.  A ROB
may retire several instructions at one boundary, so its progress target is a
packet schedule rather than a one-input-at-a-time stream. -/
def packetSchedulePrefix {α : Type} (schedule : Nat → List α) : Nat → List α
  | 0 => []
  | n + 1 => packetSchedulePrefix schedule n ++ schedule n

/-- Every finite target packet prefix is emitted at some finite ROB cycle
boundary.  The target packet widths are explicit and need not be uniform. -/
def RobRetiresTarget {State : Type}
    (core : RobMachine State) (initial : State)
    (schedule : Nat → Input) (targetPackets : Nat → List Input) : Prop :=
  ∀ k : Nat, ∃ n : Nat,
    robInputs core initial (schedulePrefix schedule n) =
      packetSchedulePrefix targetPackets k

/-- A ROB refinement plus an explicit packet-boundary progress certificate gives
the matching ISA trace for every finite target packet prefix. -/
theorem rob_progress_trace_refines {CoreState IsaState : Type}
    {core : RobMachine CoreState} {isa : Machine IsaState}
    {rel : CoreState → IsaState → Nat → Prop} {start : Nat}
    {admit : Input → Prop}
    (h : RobStepRefines core isa rel start admit)
    {schedule : Nat → Input} {targetPackets : Nat → List Input}
    (progress : RobRetiresTarget core core.init schedule targetPackets) :
    ∀ k : Nat, ∃ n : Nat,
      robTrace core core.init (schedulePrefix schedule n) =
        trace isa isa.init (packetSchedulePrefix targetPackets k) := by
  intro k
  rcases progress k with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have htrace := rob_trace_refines h core.init isa.init start
      (schedulePrefix schedule n) h.1
  rw [htrace, hn]

end LeanModels.Refine

#print axioms LeanModels.Refine.progress_trace_refines
#print axioms LeanModels.Refine.rob_progress_trace_refines
