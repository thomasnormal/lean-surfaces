import LeanModels.Refine.RvfiRv32i
import Examples.«system-verilog».cores.picorv32.rvfi_prefix_boundary

/-!
# PicoRV32 unified RV32I RVFI boundary witness

The measured non-trapping PicoRV32 prefix is certified through the indexed
`Rv32iBoundary` dispatcher.  This keeps the concrete RVFI rows tied to the
threaded architectural post-state and retirement without claiming a symbolic
RTL invariant while the loader still refuses the upstream register memory.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_rv32i_boundary

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary
open Examples.«system-verilog».cores.picorv32.rvfi_lw_boundary
open Examples.«system-verilog».cores.picorv32.rvfi_prefix_boundary
open Examples.«system-verilog».cores.picorv32.rvfi_proof
open Examples.«system-verilog».cores.picorv32.rvfi_sw_boundary
open Examples.«system-verilog».cores.picorv32.trace_proof

theorem pinned_addi_unified :
    Rv32iBoundary (ArchState.init 0) addiInput addi1
      { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
        memory := addiInput.memory }
      (aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)) := by
  exact RvfiObservation.addiBoundary_rv32i
    0x00500093 1 0 5 pinned_addi_boundary

theorem pinned_store_unified :
    Rv32iBoundary storeState storeInput storeRaw
      { arch := memNext storeState storeInput.memory (.store .word) 1 0 0x100,
        memory := memAfter storeInput.memory storeState (.store .word) 1 0 0x100 }
      (memRetirement storeState storeInput (.store .word) 1 0 0x100) := by
  exact RvfiObservation.swBoundary_rv32i
    0x10102023 0 1 0x100 pinned_store_boundary

theorem pinned_load_unified :
    Rv32iBoundary loadState loadInput loadRaw
      { arch := memNext loadState loadInput.memory (.load true .word) 2 0 0x100,
        memory := memAfter loadInput.memory loadState (.load true .word) 2 0 0x100 }
      (memRetirement loadState loadInput (.load true .word) 2 0 0x100) := by
  exact RvfiObservation.lwBoundary_rv32i
    0x10002103 2 0 0x100 pinned_load_boundary

theorem pinned_addi2_unified :
    Rv32iBoundary addi2State addi2Input addi2Raw
      { arch := aluNext addi2State .add 3 (.reg 2) (.imm 1),
        memory := addi2Input.memory }
      (aluRetirement addi2State addi2Input .add 3 (.reg 2) (.imm 1)) := by
  exact RvfiObservation.addiBoundary_rv32i
    0x00110193 3 2 1 pinned_addi2_boundary

theorem pinned_unified_boundary_window :
    Rv32iBoundary (ArchState.init 0) addiInput addi1
        { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
          memory := addiInput.memory }
        (aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)) ∧
    Rv32iBoundary storeState storeInput storeRaw
        { arch := memNext storeState storeInput.memory (.store .word) 1 0 0x100,
          memory := memAfter storeInput.memory storeState (.store .word) 1 0 0x100 }
        (memRetirement storeState storeInput (.store .word) 1 0 0x100) ∧
    Rv32iBoundary loadState loadInput loadRaw
        { arch := memNext loadState loadInput.memory (.load true .word) 2 0 0x100,
          memory := memAfter loadInput.memory loadState (.load true .word) 2 0 0x100 }
        (memRetirement loadState loadInput (.load true .word) 2 0 0x100) ∧
    Rv32iBoundary addi2State addi2Input addi2Raw
        { arch := aluNext addi2State .add 3 (.reg 2) (.imm 1),
          memory := addi2Input.memory }
        (aluRetirement addi2State addi2Input .add 3 (.reg 2) (.imm 1)) := by
  exact ⟨pinned_addi_unified, pinned_store_unified,
    pinned_load_unified, pinned_addi2_unified⟩

theorem pinned_unified_machine_commits :
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := ArchState.init 0, memory := addiInput.memory } addiInput =
      ({ arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
          memory := addiInput.memory },
        aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)) ∧
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := storeState, memory := storeInput.memory } storeInput =
      (({ arch := memNext storeState storeInput.memory (.store .word) 1 0 0x100,
          memory := memAfter storeInput.memory storeState (.store .word) 1 0 0x100 } : RvMemoryState),
        memRetirement storeState storeInput (.store .word) 1 0 0x100) ∧
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := loadState, memory := loadInput.memory } loadInput =
      (({ arch := memNext loadState loadInput.memory (.load true .word) 2 0 0x100,
          memory := memAfter loadInput.memory loadState (.load true .word) 2 0 0x100 } : RvMemoryState),
        memRetirement loadState loadInput (.load true .word) 2 0 0x100) ∧
    (rvMemoryMachineWith cv32e40pProfile).step
        { arch := addi2State, memory := addi2Input.memory } addi2Input =
      ({ arch := aluNext addi2State .add 3 (.reg 2) (.imm 1),
          memory := addi2Input.memory },
        aluRetirement addi2State addi2Input .add 3 (.reg 2) (.imm 1)) := by
  exact ⟨pinned_addi_unified.rvMemoryMachineWith cv32e40pProfile,
    pinned_store_unified.rvMemoryMachineWith cv32e40pProfile,
    pinned_load_unified.rvMemoryMachineWith cv32e40pProfile,
    pinned_addi2_unified.rvMemoryMachineWith cv32e40pProfile⟩

/-! ## A finite core-facing cycle obligation -/

/-- A one-bit finite machine that emits the measured ADDI row once and then
stutters.  The input admission predicate below pins the measured parcel; the
machine shape is only a concrete consumer of the generic cycle constructor,
not a model of PicoRV32's blocked RTL. -/
def pinnedAddiCycleMachine : RvfiCycleMachine Bool where
  init := false
  step done _ :=
    if done then (true, bubbleObservation) else (true, addi1)

def pinnedAddiCycleRel (done : Bool) (state : RvMemoryState) : Prop :=
  if done then
    state =
      { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
        memory := addiInput.memory }
  else state = { arch := ArchState.init 0, memory := addiInput.memory }

def pinnedAddiCycleAdmit (input : Input) : Prop := input = addiInput

theorem pinned_addi_cycle_refines :
    RvfiCycleStepRefines pinnedAddiCycleMachine
      (rvMemoryMachineWith cv32e40pProfile)
      pinnedAddiCycleRel pinnedAddiCycleAdmit := by
  apply rvfiCycleStepRefines_of_rv32i_memory cv32e40pProfile
    pinnedAddiCycleMachine pinnedAddiCycleRel pinnedAddiCycleAdmit
  · rfl
  · intro state memoryState input hrel hadmit
    cases state with
    | false =>
        have hinput : input = addiInput := hadmit
        subst input
        have hmem : memoryState =
            { arch := ArchState.init 0, memory := addiInput.memory } := by
          simpa [pinnedAddiCycleRel] using hrel
        subst memoryState
        simp only [pinnedAddiCycleMachine]
        refine ⟨
          { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
            memory := addiInput.memory },
          aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5),
          by simp, pinned_addi_unified, ?_⟩
        simp [pinnedAddiCycleRel]
    | true =>
        simpa [pinnedAddiCycleMachine, bubbleObservation] using hrel

def pinnedAddiCycleInputs : List Input := [addiInput, addiInput]

def pinnedAddiCycleRetirements : List Retirement :=
  [aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)]

theorem pinned_addi_cycle_observations_normalize :
    normalizeRvfiTrace? 0
        (rvfiObservations pinnedAddiCycleMachine
          pinnedAddiCycleMachine.init pinnedAddiCycleInputs) =
      some pinnedAddiCycleRetirements := by
  decide

theorem pinned_addi_cycle_trace_refines :
    pinnedAddiCycleRetirements =
      trace (rvMemoryMachineWith cv32e40pProfile)
        (rvMemoryMachineWith cv32e40pProfile).init
        (retireInputs pinnedAddiCycleMachine.toCycleMachine
          pinnedAddiCycleMachine.init pinnedAddiCycleInputs) := by
  exact rvfiCycleStepRefines_normalized_trace_refines
    pinned_addi_cycle_refines pinnedAddiCycleMachine.init
    (rvMemoryMachineWith cv32e40pProfile).init pinnedAddiCycleInputs
    (by rfl)
    (by
      intro input hinput
      simpa [pinnedAddiCycleInputs, pinnedAddiCycleAdmit] using hinput)
    pinned_addi_cycle_observations_normalize

theorem pinned_addi_cycle_normalized_refines :
    (pinnedAddiCycleRetirements =
      trace (rvMemoryMachineWith cv32e40pProfile)
        (rvMemoryMachineWith cv32e40pProfile).init
        (retireInputs pinnedAddiCycleMachine.toCycleMachine
          pinnedAddiCycleMachine.init pinnedAddiCycleInputs)) ∧
    pinnedAddiCycleRel
      (rvfiStateAfter pinnedAddiCycleMachine
        pinnedAddiCycleMachine.init pinnedAddiCycleInputs)
      (machineStateAfter (rvMemoryMachineWith cv32e40pProfile)
        (rvMemoryMachineWith cv32e40pProfile).init
        (retireInputs pinnedAddiCycleMachine.toCycleMachine
          pinnedAddiCycleMachine.init pinnedAddiCycleInputs)) := by
  exact rvfiCycleStepRefines_normalized
    pinned_addi_cycle_refines pinnedAddiCycleMachine.init
    (rvMemoryMachineWith cv32e40pProfile).init pinnedAddiCycleInputs
    (by rfl)
    (by
      intro input hinput
      simpa [pinnedAddiCycleInputs, pinnedAddiCycleAdmit] using hinput)
    pinned_addi_cycle_observations_normalize

inductive PinnedWindowPhase where
  | bubble0
  | addi
  | bubble1
  | store
  | bubble2
  | load
  | bubble3
  | addi2
  | done
  deriving DecidableEq, Repr

abbrev pinnedWindowMatch (input : Input) (fetched : Fetched)
    (memoryValue : BitVec 8) : Prop :=
  input.fetched = fetched ∧ input.irq = 0 ∧
    input.memory 0x100 = memoryValue

def pinnedWindowMachine : RvfiCycleMachine PinnedWindowPhase where
  init := .bubble0
  step phase input :=
    match phase with
    | .bubble0 =>
        if pinnedWindowMatch input (.word 0) 0 then
          (.addi, bubbleObservation) else (.bubble0, bubbleObservation)
    | .addi =>
        if pinnedWindowMatch input (.word 0x00500093) 0 then
          (.bubble1, addi1) else (.addi, bubbleObservation)
    | .bubble1 =>
        if pinnedWindowMatch input (.word 0) 0 then
          (.store, bubbleObservation) else (.bubble1, bubbleObservation)
    | .store =>
        if pinnedWindowMatch input (.word 0x10102023) 0 then
          (.bubble2, storeRaw) else (.store, bubbleObservation)
    | .bubble2 =>
        if pinnedWindowMatch input (.word 0) 0 then
          (.load, bubbleObservation) else (.bubble2, bubbleObservation)
    | .load =>
        if pinnedWindowMatch input (.word 0x10002103) 5 then
          (.bubble3, loadRaw) else (.load, bubbleObservation)
    | .bubble3 =>
        if pinnedWindowMatch input (.word 0) 0 then
          (.addi2, bubbleObservation) else (.bubble3, bubbleObservation)
    | .addi2 =>
        if pinnedWindowMatch input (.word 0x00110193) 5 then
          (.done, addi2Raw) else (.addi2, bubbleObservation)
    | .done => (.done, bubbleObservation)

def pinnedWindowAdmit (input : Input) : Prop :=
  (input.memory = memZero ∨ input.memory = memFive) ∧ input.irq = 0

def pinnedWindowInputs : List Input :=
  [ bubbleInput, addiInput, bubbleInput, storeInput
  , bubbleInput, loadInput, bubbleInput, addi2Input ]

def pinnedWindowRetirements : List Retirement :=
  [ aluRetirement (ArchState.init 0) addiInput .add 1 (.reg 0) (.imm 5)
  , memRetirement storeState storeInput (.store .word) 1 0 0x100
  , memRetirement loadState loadInput (.load true .word) 2 0 0x100
  , aluRetirement addi2State addi2Input .add 3 (.reg 2) (.imm 1) ]

theorem pinned_window_observations_normalize :
    normalizeRvfiTrace? 0
        (rvfiObservations pinnedWindowMachine pinnedWindowMachine.init
          pinnedWindowInputs) = some pinnedWindowRetirements := by
  decide

def pinnedWindowS0 : RvMemoryState :=
  { arch := ArchState.init 0, memory := addiInput.memory }

def pinnedWindowS1 : RvMemoryState :=
  { arch := aluNext (ArchState.init 0) .add 1 (.reg 0) (.imm 5),
    memory := addiInput.memory }

def pinnedWindowS2 : RvMemoryState :=
  { arch := memNext storeState storeInput.memory (.store .word) 1 0 0x100,
    memory := memAfter storeInput.memory storeState (.store .word) 1 0 0x100 }

def pinnedWindowS3 : RvMemoryState :=
  { arch := memNext loadState loadInput.memory (.load true .word) 2 0 0x100,
    memory := memAfter loadInput.memory loadState (.load true .word) 2 0 0x100 }

def pinnedWindowS4 : RvMemoryState :=
  { arch := aluNext addi2State .add 3 (.reg 2) (.imm 1),
    memory := addi2Input.memory }

theorem pinned_window_store_memory : pinnedWindowS2.memory = memFive := by
  simp [pinnedWindowS2, memAfter, storeInput,
    pinned_store_state.2.1, pinned_store_state.2.2]
  funext a
  simp only [storeVal, memFive, memZero, MemW.bytes, BitVec.toNat_sub]
  simp [BitVec.toNat_ofNat]
  have ha_lt : a.toNat < 4294967296 := by exact a.isLt
  by_cases hsmall : a.toNat < 256
  · have hoff : (4294967040 + a.toNat) % 4294967296 =
        4294967040 + a.toNat := by omega
    have hnot : ¬ (4294967040 + a.toNat) % 4294967296 < 4 := by
      rw [hoff]
      omega
    have hnot' : ¬ (4294967040 + a.toNat) < 4 := by omega
    have hne : a ≠ (256 : BitVec 32) := by
      intro ha
      subst a
      simp at hsmall
    have hbool : ¬ (a == (256 : BitVec 32)) = true := by
      simp
      exact hne
    simp [hoff, hnot']
    exact hne
  · have hbig : 256 ≤ a.toNat := by omega
    by_cases hnear : a.toNat < 260
    · have hcases : a.toNat = 256 ∨ a.toNat = 257 ∨
          a.toNat = 258 ∨ a.toNat = 259 := by omega
      rcases hcases with h256 | h257 | h258 | h259
      · have ha : a = (256 : BitVec 32) :=
          BitVec.eq_of_toNat_eq (by simpa using h256)
        subst a
        simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
      · have ha : a = (257 : BitVec 32) :=
          BitVec.eq_of_toNat_eq (by simpa using h257)
        subst a
        simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
      · have ha : a = (258 : BitVec 32) :=
          BitVec.eq_of_toNat_eq (by simpa using h258)
        subst a
        simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
      · have ha : a = (259 : BitVec 32) :=
          BitVec.eq_of_toNat_eq (by simpa using h259)
        subst a
        simp [BitVec.toNat_sub, BitVec.toNat_ofNat]
    · have hfar : 260 ≤ a.toNat := by omega
      have hoff : (4294967040 + a.toNat) % 4294967296 =
          a.toNat - 256 := by omega
      have hnot : ¬ (4294967040 + a.toNat) % 4294967296 < 4 := by
        rw [hoff]
        omega
      have hnot' : ¬ a.toNat - 256 < 4 := by omega
      have hne : a ≠ (256 : BitVec 32) := by
        intro ha
        subst a
        simp at hfar
      have hbool : ¬ (a == (256 : BitVec 32)) = true := by
        simp
        exact hne
      simp [hoff, hnot']
      exact hne

inductive PinnedWindowRel : PinnedWindowPhase → RvMemoryState → Prop where
  | bubble0 : PinnedWindowRel .bubble0 pinnedWindowS0
  | addi : PinnedWindowRel .addi pinnedWindowS0
  | bubble1 : PinnedWindowRel .bubble1 pinnedWindowS1
  | store : PinnedWindowRel .store pinnedWindowS1
  | bubble2 : PinnedWindowRel .bubble2 pinnedWindowS2
  | load : PinnedWindowRel .load pinnedWindowS2
  | bubble3 : PinnedWindowRel .bubble3 pinnedWindowS3
  | addi2 : PinnedWindowRel .addi2 pinnedWindowS3
  | done : PinnedWindowRel .done pinnedWindowS4

theorem pinned_window_cycle_refines :
    RvfiCycleStepRefines pinnedWindowMachine
      (rvMemoryMachineWith cv32e40pProfile)
      PinnedWindowRel pinnedWindowAdmit := by
  apply rvfiCycleStepRefines_of_rv32i_memory cv32e40pProfile
    pinnedWindowMachine PinnedWindowRel pinnedWindowAdmit
  · exact PinnedWindowRel.bubble0
  · intro phase memoryState input hrel hadmit
    cases hrel with
    | bubble0 =>
        by_cases hmatch : pinnedWindowMatch input (.word 0) 0
        · have hstep : pinnedWindowMachine.step .bubble0 input =
              (.addi, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_pos hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.addi
        · have hstep : pinnedWindowMachine.step .bubble0 input =
              (.bubble0, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_neg hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.bubble0
    | addi =>
        by_cases hmatch : pinnedWindowMatch input (.word 0x00500093) 0
        · have hstep : pinnedWindowMachine.step .addi input =
              (.bubble1, addi1) := by
            simp only [pinnedWindowMachine]
            rw [if_pos hmatch]
          rw [hstep]
          simp only [addi1]
          simp
          have hmem : input.memory = memZero := by
            rcases hadmit.1 with hzero | hfive
            · exact hzero
            · exfalso
              have hval := hmatch.2.2
              rw [hfive] at hval
              simp [memFive] at hval
          have hin : input = addiInput := by
            cases input with
            | mk fetched memory irq =>
                change fetched = .word 0x00500093 ∧ irq = 0 ∧
                  memory 0x100 = 0 at hmatch
                change memory = memZero at hmem
                have hfetched := hmatch.1
                have hirq := hmatch.2.1
                subst fetched
                subst memory
                subst irq
                rfl
          subst input
          refine ⟨rfl, pinnedWindowS1, ?_, PinnedWindowRel.bubble1⟩
          exact ⟨aluRetirement (ArchState.init 0) addiInput
            .add 1 (.reg 0) (.imm 5), pinned_addi_unified⟩
        · have hstep : pinnedWindowMachine.step .addi input =
              (.addi, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_neg hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.addi
    | bubble1 =>
        by_cases hmatch : pinnedWindowMatch input (.word 0) 0
        · have hstep : pinnedWindowMachine.step .bubble1 input =
              (.store, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_pos hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.store
        · have hstep : pinnedWindowMachine.step .bubble1 input =
              (.bubble1, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_neg hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.bubble1
    | store =>
        by_cases hmatch : pinnedWindowMatch input (.word 0x10102023) 0
        · have hstep : pinnedWindowMachine.step .store input =
              (.bubble2, storeRaw) := by
            simp only [pinnedWindowMachine]
            rw [if_pos hmatch]
          rw [hstep]
          simp only [storeRaw]
          simp
          have hmem : input.memory = memZero := by
            rcases hadmit.1 with hzero | hfive
            · exact hzero
            · exfalso
              have hval := hmatch.2.2
              rw [hfive] at hval
              simp [memFive] at hval
          have hin : input = storeInput := by
            cases input with
            | mk fetched memory irq =>
                change fetched = .word 0x10102023 ∧ irq = 0 ∧
                  memory 0x100 = 0 at hmatch
                change memory = memZero at hmem
                have hfetched := hmatch.1
                have hirq := hmatch.2.1
                subst fetched
                subst memory
                subst irq
                rfl
          subst input
          refine ⟨rfl, pinnedWindowS2, ?_, PinnedWindowRel.bubble2⟩
          exact ⟨memRetirement storeState storeInput (.store .word) 1 0 0x100,
            pinned_store_unified⟩
        · have hstep : pinnedWindowMachine.step .store input =
              (.store, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_neg hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.store
    | bubble2 =>
        by_cases hmatch : pinnedWindowMatch input (.word 0) 0
        · have hstep : pinnedWindowMachine.step .bubble2 input =
              (.load, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_pos hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.load
        · have hstep : pinnedWindowMachine.step .bubble2 input =
              (.bubble2, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_neg hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.bubble2
    | load =>
        by_cases hmatch : pinnedWindowMatch input (.word 0x10002103) 5
        · have hstep : pinnedWindowMachine.step .load input =
              (.bubble3, loadRaw) := by
            simp only [pinnedWindowMachine]
            rw [if_pos hmatch]
          rw [hstep]
          simp only [loadRaw]
          simp
          have hmem : input.memory = memFive := by
            rcases hadmit.1 with hzero | hfive
            · exfalso
              have hval := hmatch.2.2
              rw [hzero] at hval
              simp [memZero] at hval
            · exact hfive
          have hin : input = loadInput := by
            cases input with
            | mk fetched memory irq =>
                change fetched = .word 0x10002103 ∧ irq = 0 ∧
                  memory 0x100 = 5 at hmatch
                change memory = memFive at hmem
                have hfetched := hmatch.1
                have hirq := hmatch.2.1
                subst fetched
                subst memory
                subst irq
                rfl
          subst input
          have hwindow : loadInput.memory = pinnedWindowS2.memory := by
            simpa [loadInput] using pinned_window_store_memory.symm
          refine ⟨hwindow, pinnedWindowS3, ?_, PinnedWindowRel.bubble3⟩
          exact ⟨memRetirement loadState loadInput (.load true .word) 2 0 0x100,
            pinned_load_unified⟩
        · have hstep : pinnedWindowMachine.step .load input =
              (.load, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_neg hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.load
    | bubble3 =>
        by_cases hmatch : pinnedWindowMatch input (.word 0) 0
        · have hstep : pinnedWindowMachine.step .bubble3 input =
              (.addi2, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_pos hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.addi2
        · have hstep : pinnedWindowMachine.step .bubble3 input =
              (.bubble3, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_neg hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.bubble3
    | addi2 =>
        by_cases hmatch : pinnedWindowMatch input (.word 0x00110193) 5
        · have hstep : pinnedWindowMachine.step .addi2 input =
              (.done, addi2Raw) := by
            simp only [pinnedWindowMachine]
            rw [if_pos hmatch]
          rw [hstep]
          simp only [addi2Raw]
          simp
          have hmem : input.memory = memFive := by
            rcases hadmit.1 with hzero | hfive
            · exfalso
              have hval := hmatch.2.2
              rw [hzero] at hval
              simp [memZero] at hval
            · exact hfive
          have hin : input = addi2Input := by
            cases input with
            | mk fetched memory irq =>
                change fetched = .word 0x00110193 ∧ irq = 0 ∧
                  memory 0x100 = 5 at hmatch
                change memory = memFive at hmem
                have hfetched := hmatch.1
                have hirq := hmatch.2.1
                subst fetched
                subst memory
                subst irq
                rfl
          subst input
          refine ⟨rfl, pinnedWindowS4, ?_, PinnedWindowRel.done⟩
          exact ⟨aluRetirement addi2State addi2Input
            .add 3 (.reg 2) (.imm 1), pinned_addi2_unified⟩
        · have hstep : pinnedWindowMachine.step .addi2 input =
              (.addi2, bubbleObservation) := by
            simp only [pinnedWindowMachine]
            rw [if_neg hmatch]
          rw [hstep]
          simp [bubbleObservation]
          exact PinnedWindowRel.addi2
    | done =>
        simp [pinnedWindowMachine, bubbleObservation]
        exact PinnedWindowRel.done

theorem pinned_window_trace_refines :
    pinnedWindowRetirements =
      trace (rvMemoryMachineWith cv32e40pProfile)
        (rvMemoryMachineWith cv32e40pProfile).init
        (retireInputs pinnedWindowMachine.toCycleMachine
          pinnedWindowMachine.init pinnedWindowInputs) := by
  exact rvfiCycleStepRefines_normalized_trace_refines
    pinned_window_cycle_refines pinnedWindowMachine.init
    (rvMemoryMachineWith cv32e40pProfile).init pinnedWindowInputs
    (by
      simpa [pinnedWindowMachine, pinnedWindowS0, addiInput,
        rvMemoryMachineWith] using PinnedWindowRel.bubble0)
    (by
      intro input hinput
      simp only [pinnedWindowInputs, List.mem_cons, List.not_mem_nil,
        or_false] at hinput
      rcases hinput with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨Or.inl rfl, rfl⟩
      · refine ⟨?_, rfl⟩
        left
        funext x
        rfl
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr rfl, rfl⟩
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr rfl, rfl⟩)
    pinned_window_observations_normalize

#print axioms pinned_addi_unified
#print axioms pinned_store_unified
#print axioms pinned_load_unified
#print axioms pinned_addi2_unified
#print axioms pinned_unified_boundary_window
#print axioms pinned_unified_machine_commits
#print axioms pinned_addi_cycle_refines
#print axioms pinned_addi_cycle_observations_normalize
#print axioms pinned_addi_cycle_trace_refines
#print axioms pinned_addi_cycle_normalized_refines
#print axioms pinned_window_store_memory
#print axioms pinned_window_observations_normalize
#print axioms pinned_window_cycle_refines
#print axioms pinned_window_trace_refines

end Examples.«system-verilog».cores.picorv32.rvfi_rv32i_boundary
