import Examples.«system-verilog».cores.toy_rv32i.proof

/-!
# Packet-level refinement example

This wraps the ADDI worker in a commit packet.  The packet has one entry in
this small example, but the proof uses `PacketRefines` and the packet theorem;
the same relation admits a wider packet without changing the ISA model.
-/

namespace Examples.«system-verilog».cores.toy_rv32i.packet_proof

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.toy_rv32i.proof

structure PacketState where
  arch : ArchState

def packetMachine : PacketMachine PacketState where
  init := { arch := ArchState.init 0 }
  step s _ :=
    let next := toyNext s.arch
    ({ arch := next },
      [(addiInput, Retirement.ofRvStep s.arch addiInput next (toyEffects s.arch))])

def packetRel (p : PacketState) (a : ArchState) : Prop :=
  p.arch = a ∧ a.csrs = {} ∧ a.WF

theorem packet_step (p : PacketState) (a : ArchState)
    (hrel : packetRel p a) (cycleInput : Input) :
    let (p', packet) := packetMachine.step p cycleInput
    ∃ a', packetRel p' a' ∧
      PacketRefines rvMachine toyAdmits a packet a' := by
  rcases hrel with ⟨hpa, hcsrs, hWF⟩
  cases p with
  | mk pArch =>
      simp only [packetMachine] at hpa ⊢
      subst pArch
      refine ⟨toyNext a, ?_, ?_⟩
      · exact ⟨rfl, hcsrs, by simpa [toyNext, ArchState.WF] using hWF⟩
      · have hstep :
            rvMachine.step a addiInput =
              (toyNext a, Retirement.ofRvStep a addiInput
                (toyNext a) (toyEffects a)) := by
          simp only [rvMachine, addiInput]
          rw [isa_addi_step a zeroMem hcsrs hWF]
        refine PacketRefines.cons ?_ hstep rfl (PacketRefines.nil _)
        simp [toyAdmits, addiInput, zeroMem]

theorem packet_step_refines :
    PacketStepRefines packetMachine rvMachine packetRel toyAdmits := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  intro p a cycleInput hrel
  exact packet_step p a hrel cycleInput

/-! The same state can emit two consecutive commits in one cycle. -/

def widePacketMachine : PacketMachine PacketState where
  init := { arch := ArchState.init 0 }
  step s _ :=
    let first := toyNext s.arch
    let second := toyNext first
    ({ arch := second },
      [ (addiInput, Retirement.ofRvStep s.arch addiInput first (toyEffects s.arch))
      , (addiInput, Retirement.ofRvStep first addiInput second (toyEffects first)) ])

theorem wide_packet_step (p : PacketState) (a : ArchState)
    (hrel : packetRel p a) (cycleInput : Input) :
    let (p', packet) := widePacketMachine.step p cycleInput
    ∃ a', packetRel p' a' ∧
      PacketRefines rvMachine toyAdmits a packet a' := by
  rcases hrel with ⟨hpa, hcsrs, hWF⟩
  cases p with
  | mk pArch =>
      simp only [widePacketMachine] at hpa ⊢
      subst pArch
      let first := toyNext a
      let second := toyNext first
      have hWF1 : first.WF := by
        simpa [first, toyNext, ArchState.WF] using hWF
      have hWF2 : second.WF := by
        simpa [second, first, toyNext, ArchState.WF] using hWF
      refine ⟨second, ?_, ?_⟩
      · exact ⟨rfl, hcsrs, hWF2⟩
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

theorem wide_packet_step_refines :
    PacketStepRefines widePacketMachine rvMachine packetRel toyAdmits := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  intro p a cycleInput hrel
  exact wide_packet_step p a hrel cycleInput

theorem packet_one_cycle :
    packetTrace packetMachine packetMachine.init [addiInput] =
      trace rvMachine rvMachine.init [addiInput] := by
  have h := packet_trace_refines packet_step_refines
      packetMachine.init rvMachine.init [addiInput]
      (by exact ⟨rfl, rfl, rfl⟩)
  simpa [packetMachine, packetTrace, packetInputs] using h

theorem wide_packet_one_cycle :
    packetTrace widePacketMachine widePacketMachine.init [addiInput] =
      trace rvMachine rvMachine.init [addiInput, addiInput] := by
  have h := packet_trace_refines wide_packet_step_refines
      widePacketMachine.init rvMachine.init [addiInput]
      (by exact ⟨rfl, rfl, rfl⟩)
  simpa [widePacketMachine, packetTrace, packetInputs] using h

theorem wide_packet_state_projection :
    let first := toyNext rvMachine.init
    let second := toyNext first
    second = machineStateAfter rvMachine rvMachine.init
      [addiInput, addiInput] := by
  let first := toyNext rvMachine.init
  let second := toyNext first
  have hw := wide_packet_step widePacketMachine.init rvMachine.init
      (by exact ⟨rfl, rfl, rfl⟩) addiInput
  simp only [widePacketMachine] at hw
  rcases hw with ⟨a', hrel, hp⟩
  have hstate := packet_refines_state hp
  exact hrel.1.trans hstate

theorem wide_packet_state_after_refines :
    packetRel
      (packetStateAfter widePacketMachine widePacketMachine.init [addiInput])
      (machineStateAfter rvMachine rvMachine.init
        (packetInputs widePacketMachine widePacketMachine.init [addiInput])) := by
  exact LeanModels.Refine.packetStateAfter_refines wide_packet_step_refines
    widePacketMachine.init rvMachine.init [addiInput]
    (by exact ⟨rfl, rfl, rfl⟩)

theorem wide_packet_windows_state :
    packetStateAfter widePacketMachine widePacketMachine.init
        ([addiInput] ++ [addiInput]) =
      packetStateAfter widePacketMachine
        (packetStateAfter widePacketMachine widePacketMachine.init [addiInput])
        [addiInput] := by
  exact packetStateAfter_append widePacketMachine widePacketMachine.init
    [addiInput] [addiInput]

theorem wide_packet_windows_trace :
    packetTrace widePacketMachine widePacketMachine.init
        ([addiInput] ++ [addiInput]) =
      packetTrace widePacketMachine widePacketMachine.init [addiInput] ++
        packetTrace widePacketMachine
          (packetStateAfter widePacketMachine widePacketMachine.init [addiInput])
          [addiInput] := by
  exact packetTrace_append widePacketMachine widePacketMachine.init
    [addiInput] [addiInput]

theorem wide_packet_windows_inputs :
    packetInputs widePacketMachine widePacketMachine.init
        ([addiInput] ++ [addiInput]) =
      packetInputs widePacketMachine widePacketMachine.init [addiInput] ++
        packetInputs widePacketMachine
          (packetStateAfter widePacketMachine widePacketMachine.init [addiInput])
          [addiInput] := by
  exact packetInputs_append widePacketMachine widePacketMachine.init
    [addiInput] [addiInput]

#guard (packetTrace packetMachine packetMachine.init [addiInput]).length == 1
#guard (packetTrace widePacketMachine widePacketMachine.init [addiInput]).length == 2
#guard (packetTrace widePacketMachine widePacketMachine.init
  ([addiInput] ++ [addiInput])).length == 4
#guard (packetInputs widePacketMachine widePacketMachine.init
  ([addiInput] ++ [addiInput])).length == 4

#print axioms packet_step_refines
#print axioms packet_one_cycle
#print axioms wide_packet_step_refines
#print axioms wide_packet_one_cycle
#print axioms wide_packet_state_after_refines
#print axioms wide_packet_windows_state
#print axioms wide_packet_windows_trace
#print axioms wide_packet_windows_inputs

end Examples.«system-verilog».cores.toy_rv32i.packet_proof
