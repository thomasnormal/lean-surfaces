import LeanModels.Sv.Ingest2
import LeanModels.Refine.RvfiE
import LeanModels.Refine.RvfiPorts
import LeanModels.Refine.RvfiProgress
import LeanModels.Refine.RvfiRv32iProgram

/-!
# PicoRV32 R2 statement

This is the first core-specific statement for R2.  The backend `E` remains an
explicit parameter: the mixed E implementation will be supplied by the
general lane.  The loaded design below is the unmodified YosysHQ
`RISCV_FORMAL` build; its current E admission is intentionally a loud
unsupported design, so this file states the obligations without claiming an
RTL theorem.

The environment is deliberately fixed.  Program memory is always ready,
reset is held for a named number of cycles, interrupts and `pcpi_ready` are
low, and every other input is represented by a one-bit `BitVec`, hence is a
real 0/1 value.  The encoder into `E.Env` is a backend parameter until mixed
E exists.  `admit_inhabited` is the explicit non-vacuity witness for that
encoder; it does not assert that E has completed a run.

The safety conclusion uses the exact RVFI decoder from `RvfiPorts`, ties every
valid fetched word to the byte-addressed program memory, and keeps the
stateful ISA trace from `RvfiE.TraceRefines`.  Progress is a separate
bounded-next-retirement contract below.
-/

namespace Examples.«system-verilog».cores.picorv32

open LeanModels.Rv
open LeanModels.Sv
open LeanModels.Sv.Observe
open LeanModels.Refine
open LeanModels.Refine.RvfiPorts

set_option autoImplicit false

set_option maxRecDepth 100000 in
load_design_sv2 picorv32_r2
  from "Examples/system-verilog/cores/picorv32/picorv32_r2.sv.json"

/-! ## The named RISCV_FORMAL design -/

/-- Every PicoRV32 parameter is named here, even when its pinned value is
zero.  The order is the declaration order in the loaded envelope. -/
structure PicoRV32Parameters where
  ENABLE_COUNTERS : Nat
  ENABLE_COUNTERS64 : Nat
  ENABLE_REGS_16_31 : Nat
  ENABLE_REGS_DUALPORT : Nat
  LATCHED_MEM_RDATA : Nat
  TWO_STAGE_SHIFT : Nat
  BARREL_SHIFTER : Nat
  TWO_CYCLE_COMPARE : Nat
  TWO_CYCLE_ALU : Nat
  COMPRESSED_ISA : Nat
  CATCH_MISALIGN : Nat
  CATCH_ILLINSN : Nat
  ENABLE_PCPI : Nat
  ENABLE_MUL : Nat
  ENABLE_FAST_MUL : Nat
  ENABLE_DIV : Nat
  ENABLE_IRQ : Nat
  ENABLE_IRQ_QREGS : Nat
  ENABLE_IRQ_TIMER : Nat
  ENABLE_TRACE : Nat
  REGS_INIT_ZERO : Nat
  MASKED_IRQ : Nat
  LATCHED_IRQ : Nat
  PROGADDR_RESET : Nat
  PROGADDR_IRQ : Nat
  STACKADDR : Nat
  deriving Repr, DecidableEq

def picorv32RISCVFormalParameters : PicoRV32Parameters :=
  { ENABLE_COUNTERS := 1
    ENABLE_COUNTERS64 := 1
    ENABLE_REGS_16_31 := 1
    ENABLE_REGS_DUALPORT := 1
    LATCHED_MEM_RDATA := 0
    TWO_STAGE_SHIFT := 1
    BARREL_SHIFTER := 0
    TWO_CYCLE_COMPARE := 0
    TWO_CYCLE_ALU := 0
    COMPRESSED_ISA := 0
    CATCH_MISALIGN := 1
    CATCH_ILLINSN := 1
    ENABLE_PCPI := 0
    ENABLE_MUL := 0
    ENABLE_FAST_MUL := 0
    ENABLE_DIV := 0
    ENABLE_IRQ := 0
    ENABLE_IRQ_QREGS := 1
    ENABLE_IRQ_TIMER := 1
    ENABLE_TRACE := 0
    REGS_INIT_ZERO := 0
    MASKED_IRQ := 0
    LATCHED_IRQ := 0xffffffff
    PROGADDR_RESET := 0
    PROGADDR_IRQ := 16
    STACKADDR := 0xffffffff }

def PicoRV32Parameters.toArgs (p : PicoRV32Parameters) : List Int :=
  [p.ENABLE_COUNTERS, p.ENABLE_COUNTERS64, p.ENABLE_REGS_16_31,
   p.ENABLE_REGS_DUALPORT, p.LATCHED_MEM_RDATA, p.TWO_STAGE_SHIFT,
   p.BARREL_SHIFTER, p.TWO_CYCLE_COMPARE, p.TWO_CYCLE_ALU, p.COMPRESSED_ISA,
   p.CATCH_MISALIGN, p.CATCH_ILLINSN, p.ENABLE_PCPI, p.ENABLE_MUL,
   p.ENABLE_FAST_MUL, p.ENABLE_DIV, p.ENABLE_IRQ, p.ENABLE_IRQ_QREGS,
   p.ENABLE_IRQ_TIMER, p.ENABLE_TRACE, p.REGS_INIT_ZERO, p.MASKED_IRQ,
   p.LATCHED_IRQ, p.PROGADDR_RESET, p.PROGADDR_IRQ, p.STACKADDR]

#guard picorv32RISCVFormalParameters.toArgs ==
  [1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0,
   4294967295, 0, 16, 4294967295]

/-- The literal parametric envelope and its explicit pinned instantiation.
`Design2` may contain the loader's loud refusal while the corresponding E
backend is being completed; retaining that value is provenance, not a claim
that the core already runs. -/
def picorv32RISCVFormalPDesign : PDesign := picorv32_r2.pdesign

def picorv32RISCVFormalDesign : Design2 :=
  picorv32RISCVFormalPDesign.instantiateD2 picorv32RISCVFormalParameters.toArgs

/-! ## Fixed environment -/

/-- The fixed R2 environment.  `otherInputs` has a one-bit type, so the
environment cannot contain an x/z value at those ports.  The `programRegion`
predicate and its `programReadOnly` field are the memory-model hypothesis. -/
structure PicoRV32Environment where
  program : Memory
  programRegion : Word → Bool
  resetCycles : Nat
  reset : Nat → Bool
  memoryReady : Word → Bool
  interrupts : Word
  pcpiReady : Bool
  otherInputs : String → BitVec 1
  programReadOnly : ∀ address width value,
    programRegion address = true → storeVal program width address value = program
  resetHeld : ∀ cycle, cycle < resetCycles → reset cycle = true
  resetReleased : reset resetCycles = false
  alwaysReady : ∀ address, memoryReady address = true
  noInterrupts : interrupts = 0
  noPcpiReady : pcpiReady = false

/-- A concrete fixed timing used by examples: reset is high for two cycles and
low thereafter. -/
def fixedEnvironment (program : Memory) (programRegion : Word → Bool)
    (hreadonly : ∀ address width value,
      programRegion address = true → storeVal program width address value = program) :
    PicoRV32Environment :=
  { program := program
    programRegion := programRegion
    resetCycles := 2
    reset := fun cycle => if cycle < 2 then true else false
    memoryReady := fun _ => true
    interrupts := 0
    pcpiReady := false
    otherInputs := fun _ => 0
    programReadOnly := hreadonly
    resetHeld := by intro cycle h; simp [h]
    resetReleased := by simp
    alwaysReady := by intro; rfl
    noInterrupts := rfl
    noPcpiReady := rfl }

/-! ## Backend parameter and safety claim -/

/-- The E-specific part of the loaded-core setup.  `design` and `realize`
remain named parameters until mixed E exists; `loaded` is nevertheless fixed
to the explicit RISCV_FORMAL envelope above. -/
structure PicoRV32Backend (E : ESig) where
  design : E.Elab
  loaded : Design2
  loadedIsPinned : loaded = picorv32RISCVFormalDesign
  environment : PicoRV32Environment
  realize : PicoRV32Environment → E.Env
  clocking : Clocking

def PicoRV32Backend.admit {E : ESig} (b : PicoRV32Backend E) (env : E.Env) : Prop :=
  env = b.realize b.environment

/-- The fixed environment admission is inhabited by the backend's explicit
encoder. -/
theorem PicoRV32Backend.admit_inhabited {E : ESig} (b : PicoRV32Backend E) :
    ∃ env, b.admit env := by
  exact ⟨b.realize b.environment, rfl⟩

/-- Reset starts the ISA at the pinned `PROGADDR_RESET = 0` and keeps the
loaded program as the initial byte memory. -/
def picoRV32Initial {E : ESig} (b : PicoRV32Backend E) : RvMemoryState :=
  { arch := ArchState.init 0, memory := b.environment.program }

/-- A valid RVFI row fetches the word held by program memory at its reported
PC.  Invalid rows carry no instruction meaning. -/
def fetchProgramTie (program : Memory) (row : RvfiObservation) : Prop :=
  row.valid = false ∨ row.insn = loadVal program .word false row.pcRdata

/-- The fetch tie is required on every decoded E cycle. -/
def PicoRV32FetchTie {E : ESig} (b : PicoRV32Backend E) : Prop :=
  ∀ ch env trace,
    b.admit env → E.Disciplined b.clocking env → E.Behaves b.design env ch trace →
    ∀ cycle, cycle < E.cycles env →
      ∀ row,
        decodePost "rvfi_" (RvfiE.sample E b.design env trace cycle) = some row →
          fetchProgramTie b.environment.program row

/-! ## Indexed safety invariant and the R2 statement -/

structure PicoRV32Invariant {E : ESig} (b : PicoRV32Backend E)
    (profile : PlatformProfile) (initial : RvMemoryState)
    (rel : Nat → E.Config → RvMemoryState → Prop) where
  init : ∀ ch env trace, b.admit env → E.Disciplined b.clocking env →
    E.Behaves b.design env ch trace →
    rel 0 (RvfiE.boundary E env trace 0) initial
  step : ∀ ch env trace, b.admit env → E.Disciplined b.clocking env →
    E.Behaves b.design env ch trace →
    RvfiE.StepRefines E b.design (decodePost "rvfi_") rel env trace

theorem PicoRV32Invariant.safe {E : ESig} {b : PicoRV32Backend E}
    {profile : PlatformProfile} {initial : RvMemoryState}
    {rel : Nat → E.Config → RvMemoryState → Prop}
    (h : PicoRV32Invariant b profile initial rel) :
    (Obs_E E).SafeOn b.clocking b.design b.admit
      (fun _ samples => RvfiE.TraceRefines profile initial
        (decodePost "rvfi_") samples) := by
  exact RvfiE.safe_of_invariant E b.design b.clocking b.admit profile initial
    (decodePost "rvfi_") rel h.init h.step

/-- The core-specific R2 claim.  Its safety conclusion is the stateful ISA
trace for the loaded program's initial memory; `fetchTie` supplies the missing
word-to-memory link that the generic `TraceRefines` theorem intentionally
leaves to each core. -/
structure PicoRV32R2Statement (E : ESig) (b : PicoRV32Backend E)
    (profile : PlatformProfile) (initial : RvMemoryState)
    (rel : Nat → E.Config → RvMemoryState → Prop) where
  initialMemory : initial.memory = b.environment.program
  resetPc : initial.arch.pc = 0
  environmentInhabited : ∃ env, b.admit env
  invariant : PicoRV32Invariant b profile initial rel
  fetchTie : PicoRV32FetchTie b

theorem PicoRV32R2Statement.safety {E : ESig} {b : PicoRV32Backend E}
    {profile : PlatformProfile} {initial : RvMemoryState}
    {rel : Nat → E.Config → RvMemoryState → Prop}
    (s : PicoRV32R2Statement E b profile initial rel) :
    (Obs_E E).SafeOn b.clocking b.design b.admit
      (fun _ samples => RvfiE.TraceRefines profile initial
        (decodePost "rvfi_") samples) :=
  s.invariant.safe

/-! ## Separate bounded progress theorem -/

/-- The explicit liveness premise: one retirement occurs within `bound`
cycles of reset release, and another target retirement occurs within `bound`
cycles after every target prefix already reached. -/
structure BoundedNextRetirement {State : Type}
    (machine : RvfiCycleMachine State) (initial : State)
    (schedule target : Nat → Input) (resetRelease bound : Nat) : Prop where
  first : ∃ n, n ≤ resetRelease + bound ∧
    retireInputs machine.toCycleMachine initial (schedulePrefix schedule n) =
      schedulePrefix target 1
  next : ∀ k n,
    retireInputs machine.toCycleMachine initial (schedulePrefix schedule n) =
      schedulePrefix target (k + 1) →
    ∃ n', n' ≤ n + 1 + bound ∧
      retireInputs machine.toCycleMachine initial (schedulePrefix schedule n') =
        schedulePrefix target (k + 2)

theorem BoundedNextRetirement.toRetiresTarget {State : Type}
    {machine : RvfiCycleMachine State} {initial : State}
    {schedule target : Nat → Input} {resetRelease bound : Nat}
    (h : BoundedNextRetirement machine initial schedule target resetRelease bound) :
    Rv32iRetiresTarget machine initial schedule target := by
  intro k
  cases k with
  | zero => exact ⟨0, rfl⟩
  | succ k =>
      induction k with
      | zero =>
          obtain ⟨n, _, hn⟩ := h.first
          exact ⟨n, hn⟩
      | succ k ih =>
          obtain ⟨n, hn⟩ := ih
          obtain ⟨n', _, hn'⟩ := h.next k n hn
          exact ⟨n', by simpa [Nat.add_assoc] using hn'⟩

/-- The separate R2 progress theorem.  The bounded next-retirement premise
is the only liveness assumption; safety above does not imply it. -/
theorem picoRV32_progress {State : Type}
    (profile : PlatformProfile) (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : Rv32iCycleStepRefines machine rel admit)
    (start : Nat) (coreState : State) (memoryState : RvMemoryState)
    (hrel : rel coreState memoryState)
    {schedule target : Nat → Input}
    (hschedule : ∀ n, admit (schedule n))
    {resetRelease bound : Nat}
    (progress : BoundedNextRetirement machine coreState schedule target
      resetRelease bound) :
    ∀ k : Nat, ∃ n : Nat, ∃ program : List Rv32iInstruction,
      Rv32iRvfiCycleTrace machine start coreState memoryState
        (schedulePrefix schedule n) program ∧
      normalizeRvfiTrace? start
        (rvfiObservations machine coreState (schedulePrefix schedule n)) =
        some (trace (rvMemoryMachineWith profile) memoryState
          (schedulePrefix target k)) := by
  have htarget := progress.toRetiresTarget
  intro k
  obtain ⟨n, program, certificate, htrace, _⟩ :=
    rv32i_progress_trace_refines profile machine rel admit hstep start
      coreState memoryState hrel hschedule htarget k
  exact ⟨n, program, certificate, htrace⟩

end Examples.«system-verilog».cores.picorv32
