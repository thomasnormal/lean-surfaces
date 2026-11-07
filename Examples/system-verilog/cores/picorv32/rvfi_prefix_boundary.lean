import LeanModels.Refine.MemoryMachine
import LeanModels.Refine.RvfiMem
import Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary
import Examples.«system-verilog».cores.picorv32.rvfi_sw_boundary
import Examples.«system-verilog».cores.picorv32.rvfi_lw_boundary
import Examples.«system-verilog».cores.picorv32.trace_proof

/-!
# PicoRV32 stateful memory-prefix boundary

The first three non-trapping instructions are an ADDI, a store, and a load.
This witness evaluates them through the stateful memory machine and exposes
the concrete architectural state and memory view consumed by the next ADDI.
-/

namespace Examples.«system-verilog».cores.picorv32.rvfi_prefix_boundary

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.rvfi_proof
open Examples.«system-verilog».cores.picorv32.trace_proof
open Examples.«system-verilog».cores.picorv32.rvfi_addi_boundary
open Examples.«system-verilog».cores.picorv32.rvfi_sw_boundary
open Examples.«system-verilog».cores.picorv32.rvfi_lw_boundary

def prefixS0 : ArchState := ArchState.init 0
def prefixS1 : ArchState := addiNext prefixS0 1 0 5
def prefixS2 : ArchState := swNext prefixS1

def prefixState : RvMemoryState :=
  rvMemoryStateAfter cv32e40pProfile
    { arch := rvMachine.init, memory := memZero }
    (nontrapInputs.take 3)

def fullState : RvMemoryState :=
  rvMemoryStateAfter cv32e40pProfile prefixState
    [{ fetched := .word 0x00110193, memory := memFive }]

theorem pinned_prefix_architecture :
    prefixState.arch.pc = 12 ∧ prefixState.arch.readReg 2 = 5 ∧
      prefixState.arch.readReg 0 = 0 := by
  decide

theorem pinned_prefix_memory :
    ∀ a, prefixState.memory a = memFive a := by
  intro a
  have h1 : isaStepWith cv32e40pProfile (ArchState.init 0) memZero
      (.word 0x00500093) 0 =
      (addiNext (ArchState.init 0) 1 0 5,
        addiEffects (ArchState.init 0)) :=
    isaStepWith_addi cv32e40pProfile (ArchState.init 0) memZero 0x00500093 1 0 5
      (by decide)
  have h2 : isaStepWith cv32e40pProfile
      (addiNext (ArchState.init 0) 1 0 5) memZero
      (.word 0x10102023) 0 =
      (swNext (addiNext (ArchState.init 0) 1 0 5),
        swEffects (addiNext (ArchState.init 0) 1 0 5) 0 1 0x100) :=
    isaStepWith_sw cv32e40pProfile (addiNext (ArchState.init 0) 1 0 5)
      memZero 0x10102023 0 1 0x100
      (by decide)
  have h3 : isaStepWith cv32e40pProfile
      (swNext (addiNext (ArchState.init 0) 1 0 5))
      (storeVal memZero .word 0x100 5) (.word 0x10002103) 0 =
      (lwNext (swNext (addiNext (ArchState.init 0) 1 0 5))
          (storeVal memZero .word 0x100 5) 2 0 0x100,
        lwEffects (swNext (addiNext (ArchState.init 0) 1 0 5)) 0 0x100) :=
    isaStepWith_lw cv32e40pProfile (swNext (addiNext (ArchState.init 0) 1 0 5))
      (storeVal memZero .word 0x100 5) 0x10002103 2 0 0x100
      (by decide)
  have hs1 :
      ((rvMemoryMachineWith cv32e40pProfile).step
        { arch := ArchState.init 0, memory := memZero }
        { fetched := .word 0x00500093, memory := memZero }).fst =
      { arch := addiNext (ArchState.init 0) 1 0 5, memory := memZero } := by
    simp only [rvMemoryMachineWith]
    rw [h1]
    rfl
  have hs2 :
      ((rvMemoryMachineWith cv32e40pProfile).step
        { arch := addiNext (ArchState.init 0) 1 0 5, memory := memZero }
        { fetched := .word 0x10102023, memory := memZero }).fst =
      { arch := swNext (addiNext (ArchState.init 0) 1 0 5),
        memory := storeVal memZero .word 0x100 5 } := by
    simp only [rvMemoryMachineWith]
    rw [h2]
    rfl
  have hs3 :
      ((rvMemoryMachineWith cv32e40pProfile).step
        { arch := swNext (addiNext (ArchState.init 0) 1 0 5),
          memory := storeVal memZero .word 0x100 5 }
        { fetched := .word 0x10002103, memory := memFive }).fst =
      { arch := lwNext (swNext (addiNext (ArchState.init 0) 1 0 5))
          (storeVal memZero .word 0x100 5) 2 0 0x100,
        memory := storeVal memZero .word 0x100 5 } := by
    simp only [rvMemoryMachineWith]
    rw [h3]
    rfl
  simp only [prefixState, rvMemoryStateAfter, machineStateAfter,
    nontrapInputs, List.take, rvMachine]
  rw [hs1, hs2, hs3]
  have hstore : storeVal memZero .word 0x100 5 = memFive := by
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
  rw [hstore]

theorem pinned_prefix_state :
    prefixState.arch.pc = 12 ∧ prefixState.arch.readReg 2 = 5 ∧
      prefixState.arch.readReg 0 = 0 ∧
      (∀ a, prefixState.memory a = memFive a) := by
  exact ⟨pinned_prefix_architecture.1, pinned_prefix_architecture.2.1,
    pinned_prefix_architecture.2.2, pinned_prefix_memory⟩

theorem pinned_full_state :
    fullState.arch.pc = 16 ∧ fullState.arch.readReg 2 = 5 ∧
      fullState.arch.readReg 3 = 6 ∧ fullState.arch.readReg 0 = 0 ∧
      (∀ a, fullState.memory a = memFive a) := by
  have h4 : isaStepWith cv32e40pProfile prefixState.arch prefixState.memory
      (.word 0x00110193) 0 =
      (addiNext prefixState.arch 3 2 1, addiEffects prefixState.arch) :=
    isaStepWith_addi cv32e40pProfile prefixState.arch prefixState.memory
      0x00110193 3 2 1 (by decide)
  have hs4 :
      ((rvMemoryMachineWith cv32e40pProfile).step prefixState
        { fetched := .word 0x00110193, memory := memFive }).fst =
      { arch := addiNext prefixState.arch 3 2 1,
        memory := prefixState.memory } := by
    simp only [rvMemoryMachineWith]
    rw [h4]
    rfl
  simp only [fullState, rvMemoryStateAfter, machineStateAfter]
  rw [hs4]
  have harch := pinned_prefix_architecture
  have hmem := pinned_prefix_memory
  rcases harch with ⟨hpc, h2, h0⟩
  change prefixState.arch.regs 2 = 5 at h2
  change prefixState.arch.regs 0 = 0 at h0
  simp only [addiNext, ArchState.readReg, ArchState.writeReg]
  simp [hpc, h2, h0, hmem]

/-- The concrete stateful window ends at the same architectural state as the
stateless adapter after it has been given the memory views threaded from the
initial byte memory.  This is the state endpoint that a loaded-core relation
will consume after connecting its RVFI memory port to `threadRvInputs`. -/
theorem pinned_full_state_machine :
    fullState.arch = machineStateAfter (rvMachineWith cv32e40pProfile)
      rvMachine.init
      (threadRvInputs cv32e40pProfile rvMachine.init memZero nontrapInputs) := by
  change (rvMemoryStateAfter cv32e40pProfile
      { arch := rvMachine.init, memory := memZero } nontrapInputs).arch = _
  exact rvMemoryStateAfter_arch cv32e40pProfile rvMachine.init memZero nontrapInputs

/-- The stateful memory machine produces exactly the four measured
non-trapping retirements, so its final state and its commit stream are one
window-level certificate. -/
theorem pinned_full_window_trace :
    trace (rvMemoryMachineWith cv32e40pProfile)
        { arch := rvMachine.init, memory := memZero } nontrapInputs =
      nontrapExpected := by
  decide

/-- The normalized measured RVFI observations are the same trace when the
memory views are threaded through the stateful machine. -/
theorem pinned_full_window_observed :
    normalizeRvfiTrace? 0 nontrapObservations = some
      (trace (rvMemoryMachineWith cv32e40pProfile)
        { arch := rvMachine.init, memory := memZero } nontrapInputs) := by
  rw [pinned_nontrap_trace_certificate]
  decide

/-- One bundled certificate for every measured non-trapping row.  The first
component retains the raw RVFI predicates; the second component gives the
corresponding stateful machine commits, so a future loaded-core proof can
consume the whole window without choosing between a wire-level and a memory
level premise. -/
theorem pinned_raw_stateful_window_certificate :
    (RvfiObservation.addiBoundary (ArchState.init 0) addiInput addi1
        0x00500093 1 0 5 ∧
      RvfiObservation.swBoundary storeState storeInput storeRaw
        0x10102023 0 1 0x100 ∧
      RvfiObservation.lwBoundary loadState loadInput loadRaw
        0x10002103 2 0 0x100 ∧
      RvfiObservation.addiBoundary addi2State addi2Input addi2Raw
        0x00110193 3 2 1) ∧
    ((rvMemoryMachineWith cv32e40pProfile).step
        { arch := ArchState.init 0, memory := addiInput.memory } addiInput =
      ({ arch := addiNext (ArchState.init 0) 1 0 5,
          memory := addiInput.memory },
        addiRetirement (ArchState.init 0) addiInput 1 0 5) ∧
      (rvMemoryMachineWith cv32e40pProfile).step
        { arch := storeState, memory := storeInput.memory } storeInput =
      ({ arch := swNext storeState,
          memory := storeVal storeInput.memory .word 0x100 5 },
        swRetirement storeState storeInput 0 1 0x100) ∧
      (rvMemoryMachineWith cv32e40pProfile).step
        { arch := loadState, memory := loadInput.memory } loadInput =
      ({ arch := lwNext loadState loadInput.memory 2 0 0x100,
          memory := loadInput.memory },
        lwRetirement loadState loadInput 2 0 0x100) ∧
      (rvMemoryMachineWith cv32e40pProfile).step
        { arch := addi2State, memory := addi2Input.memory } addi2Input =
      ({ arch := addiNext addi2State 3 2 1,
          memory := addi2Input.memory },
        addiRetirement addi2State addi2Input 3 2 1)) := by
  exact ⟨⟨pinned_addi_boundary, pinned_store_boundary,
    pinned_load_boundary, pinned_addi2_boundary⟩,
    ⟨pinned_addi_stateful_machine_commit,
      pinned_store_stateful_machine_commit,
      pinned_load_stateful_machine_commit,
      pinned_addi2_stateful_machine_commit⟩⟩

#guard prefixState.arch.pc = 12
#guard prefixState.arch.readReg 2 = 5
#guard prefixState.arch.readReg 0 = 0
#guard fullState.arch.pc = 16
#guard fullState.arch.readReg 2 = 5
#guard fullState.arch.readReg 3 = 6
#guard fullState.arch.readReg 0 = 0
#guard trace (rvMemoryMachineWith cv32e40pProfile)
  { arch := rvMachine.init, memory := memZero } nontrapInputs == nontrapExpected
#guard normalizeRvfiTrace? 0 nontrapObservations == some
  (trace (rvMemoryMachineWith cv32e40pProfile)
    { arch := rvMachine.init, memory := memZero } nontrapInputs)

#print axioms pinned_prefix_architecture
#print axioms pinned_prefix_memory
#print axioms pinned_prefix_state
#print axioms pinned_full_state
#print axioms pinned_full_state_machine
#print axioms pinned_full_window_trace
#print axioms pinned_full_window_observed
#print axioms pinned_raw_stateful_window_certificate

end Examples.«system-verilog».cores.picorv32.rvfi_prefix_boundary
