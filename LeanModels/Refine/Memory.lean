import LeanModels.Refine.Bus
import LeanModels.Refine.Rob

/-!
# Tagged memory commits

An out-of-order core may complete data requests in any order, but its
architectural memory effects are exposed at the reorder buffer's commit
boundary.  `TaggedMemoryCommit` is the memory-only analogue of `TaggedCommit`:
the tag and packet order are explicit evidence, while the supplied
`MemoryEffect` must be checked against the exact byte-addressed memory at the
architectural commit point.

`MemoryPacketRefines` is an inductive certificate rather than a sorting
function.  It consumes the packet in the order the core presents it and
requires every effect to equal `serviceBusRequest`; no completion order is
chosen or reconstructed here.  A core relation may keep an arbitrary
completion buffer and prove separately that its in-order packet has this
certificate (and that its tags are consecutive).
-/

namespace LeanModels.Refine

/-! ## Tagged packets and the memory certificate -/

structure TaggedMemoryCommit where
  order : Nat
  request : BusRequest
  effect : MemoryEffect
  deriving DecidableEq, Repr

abbrev TaggedMemoryPacket := List TaggedMemoryCommit

def memoryOrderTags (start : Nat) (packet : TaggedMemoryPacket) : Prop :=
  packet.map TaggedMemoryCommit.order = orderPrefix start packet.length

@[simp] theorem memoryOrderTags_nil (start : Nat) :
    memoryOrderTags start [] := rfl

/-- A completion-order certificate may name any permutation of the committed
tags.  The refinement theorem below never inspects this list: its purpose is
to make the proof obligation for an implementation's arbitrary completion
order explicit at the boundary. -/
def CompletionOrder (completed : List Nat) (packet : TaggedMemoryPacket) : Prop :=
  List.Perm completed (packet.map TaggedMemoryCommit.order)

inductive MemoryPacketRefines : Memory → TaggedMemoryPacket → Memory → Prop where
  | nil (memory : Memory) : MemoryPacketRefines memory [] memory
  | cons {memory finalMemory : Memory}
      {entry : TaggedMemoryCommit} {rest : TaggedMemoryPacket}
      (hEffect : entry.effect = (serviceBusRequest memory entry.request).2)
      (hTail : MemoryPacketRefines
        (serviceBusRequest memory entry.request).1 rest finalMemory) :
      MemoryPacketRefines memory (entry :: rest) finalMemory

def TaggedMemoryPacketRefines (start : Nat) (memory : Memory)
    (packet : TaggedMemoryPacket) (finalMemory : Memory) : Prop :=
  memoryOrderTags start packet ∧ MemoryPacketRefines memory packet finalMemory

/-! ## Exact projection to the direct memory run -/

theorem memoryPacket_refines_direct
    {memory finalMemory : Memory} {packet : TaggedMemoryPacket}
    (h : MemoryPacketRefines memory packet finalMemory) :
    finalMemory = (directRun memory (packet.map TaggedMemoryCommit.request)).1 ∧
      packet.map TaggedMemoryCommit.effect =
        (directRun memory (packet.map TaggedMemoryCommit.request)).2 := by
  induction h with
  | nil memory =>
      simp [directRun]
  | @cons memory finalMemory entry rest hEffect hTail ih =>
      simp only [List.map_cons, directRun]
      constructor
      · exact ih.1
      · rw [hEffect, ih.2]

theorem taggedMemoryPacket_refines_direct
    {start : Nat} {memory finalMemory : Memory}
    {packet : TaggedMemoryPacket}
    (h : TaggedMemoryPacketRefines start memory packet finalMemory) :
    finalMemory = (directRun memory (packet.map TaggedMemoryCommit.request)).1 ∧
      packet.map TaggedMemoryCommit.effect =
        (directRun memory (packet.map TaggedMemoryCommit.request)).2 :=
  memoryPacket_refines_direct h.2

/-! ## Timing erasure at the tagged commit boundary -/

/-- A tagged memory packet remains exact when the requests are sent through a
timed FIFO bus.  The packet's commit order is preserved by `completed`, while
the latency oracle may insert any finite number of response bubbles. -/
theorem taggedMemoryPacket_refines_bus
    {start : Nat} {memory finalMemory : Memory}
    {packet : TaggedMemoryPacket}
    (h : TaggedMemoryPacketRefines start memory packet finalMemory)
    (latency : LatencyOracle) :
    finalMemory =
        (runBus memory (scheduleWith latency
          (packet.map TaggedMemoryCommit.request))).1 ∧
      packet.map TaggedMemoryCommit.effect =
        completed (runBus memory (scheduleWith latency
          (packet.map TaggedMemoryCommit.request))).2 := by
  have hdirect := taggedMemoryPacket_refines_direct h
  have hbus := runBus_oracle_projection memory latency
    (packet.map TaggedMemoryCommit.request)
  constructor
  · exact hdirect.1.trans hbus.1.symm
  · exact hdirect.2.trans hbus.2.symm

/-- Adjacent tagged memory packets compose through the same latency oracle.
The second packet starts after the first packet's tag range, and its schedule
uses the latency entries after the first packet.  The combined request and
effect streams therefore refine one timed bus run without choosing a delay
pattern or a completion order. -/
theorem taggedMemoryPacket_refines_bus_append
    {start : Nat} {memory middle finalMemory : Memory}
    {first second : TaggedMemoryPacket}
    (hfirst : TaggedMemoryPacketRefines start memory first middle)
    (hsecond : TaggedMemoryPacketRefines (start + first.length)
      middle second finalMemory)
    (latency : LatencyOracle) :
    finalMemory =
        (runBus memory (scheduleWith latency
          ((first ++ second).map TaggedMemoryCommit.request))).1 ∧
      (first ++ second).map TaggedMemoryCommit.effect =
        completed (runBus memory (scheduleWith latency
          ((first ++ second).map TaggedMemoryCommit.request))).2 := by
  have hfirstBus := taggedMemoryPacket_refines_bus hfirst latency
  have hsecondBus := taggedMemoryPacket_refines_bus hsecond
    (latencyShift latency first.length)
  have hschedule :
      scheduleWith latency
          ((first ++ second).map TaggedMemoryCommit.request) =
        scheduleWith latency (first.map TaggedMemoryCommit.request) ++
          scheduleWith (latencyShift latency first.length)
            (second.map TaggedMemoryCommit.request) := by
    rw [List.map_append]
    simpa using scheduleWith_append latency
      (first.map TaggedMemoryCommit.request)
      (second.map TaggedMemoryCommit.request)
  have hrun := runBus_append memory
    (scheduleWith latency (first.map TaggedMemoryCommit.request))
    (scheduleWith (latencyShift latency first.length)
      (second.map TaggedMemoryCommit.request))
  have hcompleted := completed_runBus_append memory
    (scheduleWith latency (first.map TaggedMemoryCommit.request))
    (scheduleWith (latencyShift latency first.length)
      (second.map TaggedMemoryCommit.request))
  constructor
  · rw [hschedule, hrun.1]
    simpa [hfirstBus.1] using hsecondBus.1
  · rw [List.map_append, hschedule, hcompleted, hfirstBus.2, hsecondBus.2,
      hfirstBus.1]

end LeanModels.Refine

#print axioms LeanModels.Refine.memoryPacket_refines_direct
#print axioms LeanModels.Refine.taggedMemoryPacket_refines_direct
#print axioms LeanModels.Refine.taggedMemoryPacket_refines_bus
#print axioms LeanModels.Refine.taggedMemoryPacket_refines_bus_append
