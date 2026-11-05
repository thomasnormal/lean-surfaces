import Examples.«system-verilog».cores.toy_rv32i.packet_proof

/-!
# Reorder-buffer order certificate example

The state records completions in the physical order `[second, first]`, while
the emitted packet carries consecutive architectural tags.  The relation
ignores the completion list and proves the in-order commit certificate needed
by `rob_trace_refines`.
-/

namespace Examples.«system-verilog».cores.toy_rv32i.rob_proof

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.toy_rv32i.proof

structure RobState where
  arch : ArchState
  next : Nat
  completed : List Nat

def robMachine : RobMachine RobState where
  init := { arch := ArchState.init 0, next := 0, completed := [] }
  step s _ :=
    let first := toyNext s.arch
    let second := toyNext first
    let base := s.next
    ({ arch := second, next := base + 2, completed := [base + 1, base] },
      [ { order := base, input := addiInput,
          retirement := Retirement.ofRvStep s.arch addiInput first (toyEffects s.arch) }
      , { order := base + 1, input := addiInput,
          retirement := Retirement.ofRvStep first addiInput second (toyEffects first) } ])

def robRel (r : RobState) (a : ArchState) (order : Nat) : Prop :=
  r.arch = a ∧ r.next = order ∧ a.csrs = {} ∧ a.WF

theorem rob_step (r : RobState) (a : ArchState) (order : Nat)
    (hrel : robRel r a order) (cycleInput : Input) :
    let (r', packet) := robMachine.step r cycleInput
    ∃ a' order', robRel r' a' order' ∧
      order' = order + packet.length ∧
      TaggedPacketRefines rvMachine toyAdmits order a packet a' := by
  rcases hrel with ⟨harch, hnext, hcsrs, hWF⟩
  cases r with
  | mk rArch rNext completed =>
      simp only [robMachine] at harch hnext ⊢
      subst rArch
      subst rNext
      let first := toyNext a
      let second := toyNext first
      have hWF1 : first.WF := by
        simpa [first, toyNext, ArchState.WF] using hWF
      have hWF2 : second.WF := by
        simpa [second, first, toyNext, ArchState.WF] using hWF
      refine ⟨second, order + 2, ?_, ?_, ?_⟩
      · exact ⟨rfl, rfl, hcsrs, hWF2⟩
      · rfl
      · constructor
        · rfl
        · have hstep1 :
              rvMachine.step a addiInput =
                (first, Retirement.ofRvStep a addiInput first (toyEffects a)) := by
            simp only [first, rvMachine, addiInput]
            rw [isa_addi_step a zeroMem hcsrs hWF]
          have hstep2 :
              rvMachine.step first addiInput =
                (second, Retirement.ofRvStep first addiInput second
                  (toyEffects first)) := by
            simp only [second, first, rvMachine, addiInput]
            rw [isa_addi_step first zeroMem hcsrs hWF1]
          refine PacketRefines.cons ?_ hstep1 rfl ?_
          · simp [toyAdmits, addiInput, zeroMem]
          · refine PacketRefines.cons ?_ hstep2 rfl (PacketRefines.nil _)
            simp [toyAdmits, addiInput, zeroMem]

theorem rob_step_refines :
    RobStepRefines robMachine rvMachine robRel 0 toyAdmits := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  intro r a order cycleInput hrel
  exact rob_step r a order hrel cycleInput

theorem rob_one_cycle :
    robTrace robMachine robMachine.init [addiInput] =
      trace rvMachine rvMachine.init [addiInput, addiInput] := by
  have h := rob_trace_refines rob_step_refines
      robMachine.init rvMachine.init 0 [addiInput]
      (by exact ⟨rfl, rfl, rfl, rfl⟩)
  simpa [robMachine, robTrace, robInputs] using h

#guard (robMachine.init.completed == ([] : List Nat))
#guard ((robMachine.step robMachine.init addiInput).1.completed == [1, 0])
#guard (robTrace robMachine robMachine.init [addiInput]).length == 2

#print axioms rob_step_refines
#print axioms rob_one_cycle

end Examples.«system-verilog».cores.toy_rv32i.rob_proof
