import LeanModels.Refine.Memory

/-!
# Tagged memory commit example

The completion list is intentionally in a different order from the commit
packet.  The proof consumes only the packet's consecutive tags and exact
memory effects; it does not sort or otherwise select a completion order.
-/

namespace Examples.«system-verilog».cores.toy_rv32i.memory_proof

open LeanModels.Rv
open LeanModels.Refine

def zeroMemory : Memory := fun _ => 0

def requests : List BusRequest :=
  [ .write 0x100 .word 0xDEADBEEF
  , .read 0x100 .word false
  , .read 0x101 .half false
  , .read 0x103 .byte true ]

def packet : TaggedMemoryPacket :=
  [ { order := 0, request := .write 0x100 .word 0xDEADBEEF,
      effect := .write 0x100 .word 0xDEADBEEF }
  , { order := 1, request := .read 0x100 .word false,
      effect := .read 0x100 .word 0xDEADBEEF }
  , { order := 2, request := .read 0x101 .half false,
      effect := .read 0x101 .half 0x0000ADBE }
  , { order := 3, request := .read 0x103 .byte true,
      effect := .read 0x103 .byte 0xFFFFFFDE } ]

def completionOrder : List Nat := [3, 1, 0, 2]

theorem completion_order_is_a_permutation :
    CompletionOrder completionOrder packet := by
  change List.Perm [3, 1, 0, 2] [0, 1, 2, 3]
  have h1 : List.Perm [3, 1, 0, 2] [3, 0, 1, 2] :=
    List.Perm.cons 3 (List.Perm.swap 1 0 [2]).symm
  have h2 : List.Perm [3, 0, 1, 2] [0, 3, 1, 2] :=
    (List.Perm.swap 3 0 [1, 2]).symm
  have h3 : List.Perm [0, 3, 1, 2] [0, 1, 3, 2] :=
    List.Perm.cons 0 ((List.Perm.swap 3 1 [2]).symm)
  have h4 : List.Perm [0, 1, 3, 2] [0, 1, 2, 3] :=
    List.Perm.cons 0 (List.Perm.cons 1 ((List.Perm.swap 3 2 []).symm))
  exact h1.trans (h2.trans (h3.trans h4))

theorem packet_certificate :
    TaggedMemoryPacketRefines 0 zeroMemory packet
      (directRun zeroMemory requests).1 := by
  constructor
  · rfl
  · refine MemoryPacketRefines.cons (by decide) ?_
    refine MemoryPacketRefines.cons (by decide) ?_
    refine MemoryPacketRefines.cons (by decide) ?_
    refine MemoryPacketRefines.cons (by decide) ?_
    exact MemoryPacketRefines.nil _

theorem packet_projects_to_direct :
    (directRun zeroMemory requests).1 =
        (directRun zeroMemory (packet.map TaggedMemoryCommit.request)).1 ∧
      packet.map TaggedMemoryCommit.effect =
        (directRun zeroMemory (packet.map TaggedMemoryCommit.request)).2 := by
  exact taggedMemoryPacket_refines_direct packet_certificate

#guard completionOrder == [3, 1, 0, 2]
#guard packet.map TaggedMemoryCommit.order == [0, 1, 2, 3]

#print axioms packet_certificate
#print axioms packet_projects_to_direct

end Examples.«system-verilog».cores.toy_rv32i.memory_proof
