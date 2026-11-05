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

def robSchedule : Nat → Input := fun _ => addiInput

def robTargetPackets : Nat → List Input := fun _ => [addiInput, addiInput]

theorem replicate_append (a : Input) : ∀ n m : Nat,
    List.replicate n a ++ List.replicate m a = List.replicate (n + m) a := by
  intro n
  induction n with
  | zero => intro m; simp
  | succ n ih =>
      intro m
      simp only [List.replicate_succ, List.cons_append, Nat.succ_add]
      rw [ih]

theorem rob_schedule_prefix (n : Nat) :
    schedulePrefix robSchedule n = List.replicate n addiInput := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [schedulePrefix, robSchedule, List.replicate_succ]
      rw [ih]

theorem rob_packet_schedule_prefix (n : Nat) :
    packetSchedulePrefix robTargetPackets n =
      List.replicate (2 * n) addiInput := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [packetSchedulePrefix, robTargetPackets]
      rw [ih]
      simpa [Nat.mul_succ, Nat.add_comm] using
        (replicate_append addiInput (2 * n) 2)

theorem rob_inputs_prefix (s : RobState) (n : Nat) :
    robInputs robMachine s (schedulePrefix robSchedule n) =
      List.replicate (2 * n) addiInput := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [schedulePrefix, robSchedule, robInputs]
      have hinputs :
          (robMachine.step s addiInput).2.map TaggedCommit.input =
            [addiInput, addiInput] := by
        rfl
      rw [hinputs, ih]
      simpa [Nat.mul_succ, Nat.add_comm] using
        (replicate_append addiInput 2 (2 * n))

theorem rob_progress :
    RobRetiresTarget robMachine robMachine.init robSchedule robTargetPackets := by
  intro k
  refine ⟨k, ?_⟩
  rw [rob_inputs_prefix, rob_packet_schedule_prefix]

theorem rob_progress_trace_prefix :
    ∀ k : Nat, ∃ n : Nat,
      robTrace robMachine robMachine.init (schedulePrefix robSchedule n) =
        trace rvMachine rvMachine.init (packetSchedulePrefix robTargetPackets k) := by
  exact rob_progress_trace_refines rob_step_refines rob_progress

#guard (robMachine.init.completed == ([] : List Nat))
#guard ((robMachine.step robMachine.init addiInput).1.completed == [1, 0])
#guard (robTrace robMachine robMachine.init [addiInput]).length == 2
#guard (packetSchedulePrefix robTargetPackets 3).length == 6
#guard (robInputs robMachine robMachine.init
    (schedulePrefix robSchedule 3)).length == 6

#print axioms rob_step_refines
#print axioms rob_one_cycle
#print axioms rob_progress
#print axioms rob_progress_trace_prefix

end Examples.«system-verilog».cores.toy_rv32i.rob_proof
