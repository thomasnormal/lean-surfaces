import Examples.«system-verilog».cores.toy_rv32i.packet_proof

/-!
# Explicit progress certificate example

`packet_step_refines` alone is compatible with an always-stalled machine.
This example supplies a concrete schedule and proves a witness for every
finite ADDI prefix, then invokes `progress_trace_refines`.
-/

namespace Examples.«system-verilog».cores.toy_rv32i.progress_proof

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.toy_rv32i.proof
open Examples.«system-verilog».cores.toy_rv32i.packet_proof

def addiSchedule : Nat → Input := fun _ => addiInput

theorem schedulePrefix_addi (n : Nat) :
    schedulePrefix addiSchedule n = List.replicate n addiInput := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [schedulePrefix, addiSchedule, List.replicate_succ]
      rw [ih]

theorem packet_inputs_prefix (s : PacketState) (n : Nat) :
    packetInputs packetMachine s
      (schedulePrefix addiSchedule n) = List.replicate n addiInput := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [schedulePrefix, addiSchedule, packetInputs,
        List.replicate_succ]
      change [addiInput] ++ packetInputs packetMachine
        { arch := toyNext s.arch } (schedulePrefix addiSchedule n) =
        addiInput :: List.replicate n addiInput
      rw [ih]
      rfl

theorem addi_progress :
    RetiresTarget packetMachine packetMachine.init addiSchedule addiSchedule := by
  intro k
  refine ⟨k, ?_⟩
  rw [packet_inputs_prefix, schedulePrefix_addi]

theorem progress_trace_prefix :
    ∀ k : Nat, ∃ n : Nat,
      packetTrace packetMachine packetMachine.init
          (schedulePrefix addiSchedule n) =
        trace rvMachine rvMachine.init (schedulePrefix addiSchedule k) := by
  exact progress_trace_refines packet_step_refines addi_progress

#guard (schedulePrefix addiSchedule 3).length == 3
#guard (packetInputs packetMachine packetMachine.init
    (schedulePrefix addiSchedule 3)).length == 3

#print axioms addi_progress
#print axioms progress_trace_prefix

end Examples.«system-verilog».cores.toy_rv32i.progress_proof
