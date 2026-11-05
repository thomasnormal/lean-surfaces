import Examples.«system-verilog».cores.picorv32.rvfi_proof
import LeanModels.Refine.Bus
import LeanModels.Refine.MemoryMachine
import LeanModels.Refine.RvfiPacket
import LeanModels.Refine.RvfiRob

/-!
# PicoRV32 finite RVFI-to-ISA trace witness

The first four non-trapping RVFI rows from `rvfi_probe.v` are fed to the
always-ready `rvMachine` adapter with explicit instruction and data memories.
The theorem is a finite observation witness for the pinned real core; it is
not a refinement theorem for the blocked RTL semantics.  The measured
`ebreak` row is kept in `rvfi_proof.lean`, but is intentionally outside this
trace equality because PicoRV32 reports `pcWdata = 16` on that trap while the
architectural model enters `mtvec = 0`.
-/

namespace Examples.«system-verilog».cores.picorv32.trace_proof

open LeanModels.Rv
open LeanModels.Refine
open Examples.«system-verilog».cores.picorv32.rvfi_proof

/-- Empty byte memory for the instruction and store steps. -/
def memZero : Memory := fun _ => 0

/-- The explicit load response after the measured store to address `0x100`. -/
def memFive : Memory := fun a => if a == 0x100 then 5 else 0

def nontrapMemoryRequests : List BusRequest :=
  [ .write 0x100 .word 5
  , .read 0x100 .word false ]

def nontrapMemoryEffects : List MemoryEffect :=
  [ .write 0x100 .word 5
  , .read 0x100 .word 5 ]

def bubbleObservation : RvfiObservation :=
  { valid := false, insn := 0, pcRdata := 0, pcWdata := 0 }

def bubbleInput : Input := { fetched := .word 0, memory := memZero }

/-- The four non-trapping instruction parcels emitted by the pinned witness. -/
def nontrapInputs : List Input :=
  [ { fetched := .word 0x00500093, memory := memZero }
  , { fetched := .word 0x10102023, memory := memZero }
  , { fetched := .word 0x10002103, memory := memFive }
  , { fetched := .word 0x00110193, memory := memFive } ]

def nontrapObservations : List RvfiObservation := observations.take 4

def nontrapExpected : List Retirement := expected.take 4

def nontrapFirstObservations : List RvfiObservation := [addi1, store1]

def nontrapSecondObservations : List RvfiObservation := [load1, addi2]

def nontrapFirstExpected : List Retirement := expected.take 2

def nontrapSecondExpected : List Retirement := (expected.drop 2).take 2

def cycleObservations : List RvfiObservation :=
  [ bubbleObservation, addi1, bubbleObservation, store1
  , bubbleObservation, load1, bubbleObservation, addi2 ]

def cycleInputs : List Input :=
  [ bubbleInput, { fetched := .word 0x00500093, memory := memZero }
  , bubbleInput, { fetched := .word 0x10102023, memory := memZero }
  , bubbleInput, { fetched := .word 0x10002103, memory := memFive }
  , bubbleInput, { fetched := .word 0x00110193, memory := memFive } ]

def pinnedCycleMachine : RvfiCycleMachine (List RvfiObservation) where
  init := cycleObservations
  step remaining _ :=
    match remaining with
    | [] => ([], bubbleObservation)
    | observation :: rest => (rest, observation)

def packetRows : List (List RvfiPacketEntry) :=
  [ [ { input := bubbleInput, observation := bubbleObservation }
      , { input := { fetched := .word 0x00500093, memory := memZero },
          observation := addi1 } ]
  , [ { input := bubbleInput, observation := bubbleObservation }
      , { input := { fetched := .word 0x10102023, memory := memZero },
          observation := store1 } ]
  , [ { input := bubbleInput, observation := bubbleObservation }
      , { input := { fetched := .word 0x10002103, memory := memFive },
          observation := load1 } ]
  , [ { input := bubbleInput, observation := bubbleObservation }
      , { input := { fetched := .word 0x00110193, memory := memFive },
          observation := addi2 } ] ]

def packetCycleInputs : List Input :=
  [ bubbleInput, bubbleInput, bubbleInput, bubbleInput ]

def pinnedPacketMachine : RvfiPacketMachine (List (List RvfiPacketEntry)) where
  init := packetRows
  step remaining _ :=
    match remaining with
    | [] => ([], [])
    | packet :: rest => (rest, packet)

theorem pinned_nontrap_rows_normalize :
    nontrapObservations.map RvfiObservation.toRetirement? =
      nontrapExpected.map some := by
  decide

theorem pinned_nontrap_trace_certificate :
    normalizeRvfiTrace? 0 nontrapObservations = some nontrapExpected := by
  decide

theorem pinned_nontrap_trace_chunks :
    normalizeRvfiTrace? 0 nontrapFirstObservations = some nontrapFirstExpected ∧
    normalizeRvfiTrace? 2 nontrapSecondObservations = some nontrapSecondExpected := by
  decide

theorem pinned_nontrap_trace_append :
    normalizeRvfiTrace? 0
        (nontrapFirstObservations ++ nontrapSecondObservations) =
      some (nontrapFirstExpected ++ nontrapSecondExpected) := by
  rw [normalizeRvfiTrace?_append]
  rw [pinned_nontrap_trace_chunks.1]
  simp only [Option.map, Nat.zero_add]
  have hlen : nontrapFirstExpected.length = 2 := by decide
  rw [hlen]
  rw [pinned_nontrap_trace_chunks.2]

/-- The measured non-trapping PicoRV32 stream has exactly the ISA effects. -/
theorem pinned_nontrap_trace_refines_isa :
    trace rvMachine rvMachine.init nontrapInputs = nontrapExpected := by
  decide

theorem pinned_nontrap_memory_effects :
    (directRun memZero nontrapMemoryRequests).2 = nontrapMemoryEffects := by
  decide

theorem pinned_cycle_retire_inputs :
    retireInputs pinnedCycleMachine.toCycleMachine
        pinnedCycleMachine.toCycleMachine.init cycleInputs = nontrapInputs := by
  rfl

theorem pinned_cycle_observations_normalize :
    normalizeRvfiTrace? 0
        (rvfiObservations pinnedCycleMachine pinnedCycleMachine.init cycleInputs) =
      some nontrapExpected := by
  decide

theorem pinned_packet_observations_normalize :
    normalizeRvfiTrace? 0
        (rvfiPacketObservations pinnedPacketMachine pinnedPacketMachine.init
          packetCycleInputs) = some nontrapExpected := by
  decide

theorem pinned_cycle_trace :
    cycleTrace pinnedCycleMachine.toCycleMachine
        pinnedCycleMachine.toCycleMachine.init cycleInputs = nontrapExpected := by
  exact normalizeRvfiCycleTrace pinnedCycleMachine pinnedCycleMachine.init cycleInputs
    pinned_cycle_observations_normalize

theorem pinned_rob_trace :
    robTrace pinnedCycleMachine.toRobMachine
        pinnedCycleMachine.toRobMachine.init cycleInputs = nontrapExpected := by
  exact normalizeRvfiRobTrace pinnedCycleMachine pinnedCycleMachine.init cycleInputs
    pinned_cycle_observations_normalize

theorem pinned_rob_inputs :
    robInputs pinnedCycleMachine.toRobMachine
        pinnedCycleMachine.toRobMachine.init cycleInputs = nontrapInputs := by
  rw [RvfiCycleMachine.toRobMachine_inputs]
  exact pinned_cycle_retire_inputs

theorem pinned_packet_trace :
    packetTrace pinnedPacketMachine.toPacketMachine
        pinnedPacketMachine.toPacketMachine.init packetCycleInputs =
      nontrapExpected := by
  exact normalizeRvfiPacketTrace pinnedPacketMachine pinnedPacketMachine.init
    packetCycleInputs pinned_packet_observations_normalize

theorem pinned_packet_inputs :
    packetInputs pinnedPacketMachine.toPacketMachine
        pinnedPacketMachine.toPacketMachine.init packetCycleInputs =
      nontrapInputs := by
  rfl

theorem pinned_packet_rob_trace :
    robTrace pinnedPacketMachine.toRobMachine
        pinnedPacketMachine.toRobMachine.init packetCycleInputs =
      nontrapExpected := by
  exact normalizeRvfiPacketRobTrace pinnedPacketMachine pinnedPacketMachine.init
    packetCycleInputs pinned_packet_observations_normalize

theorem pinned_packet_rob_inputs :
    robInputs pinnedPacketMachine.toRobMachine
        pinnedPacketMachine.toRobMachine.init packetCycleInputs =
      nontrapInputs := by
  rw [RvfiPacketMachine.toRobMachine_inputs]
  exact pinned_packet_inputs

theorem pinned_cycle_trace_refines_isa :
    cycleTrace pinnedCycleMachine.toCycleMachine
        pinnedCycleMachine.toCycleMachine.init cycleInputs =
      trace rvMachine rvMachine.init
        (retireInputs pinnedCycleMachine.toCycleMachine
          pinnedCycleMachine.toCycleMachine.init cycleInputs) := by
  calc
    cycleTrace pinnedCycleMachine.toCycleMachine
        pinnedCycleMachine.toCycleMachine.init cycleInputs = nontrapExpected :=
      pinned_cycle_trace
    _ = trace rvMachine rvMachine.init nontrapInputs :=
      pinned_nontrap_trace_refines_isa.symm
    _ = trace rvMachine rvMachine.init
        (retireInputs pinnedCycleMachine.toCycleMachine
          pinnedCycleMachine.toCycleMachine.init cycleInputs) := by
      rw [pinned_cycle_retire_inputs]

theorem pinned_stateful_memory_trace :
    trace (rvMemoryMachineWith cv32e40pProfile)
        { arch := rvMachine.init, memory := memZero } nontrapInputs =
      trace rvMachine rvMachine.init
        (threadRvInputs cv32e40pProfile rvMachine.init memZero nontrapInputs) := by
  exact rvMemoryMachine_trace cv32e40pProfile rvMachine.init memZero nontrapInputs

/-- The measured packed stream and the ISA stream are connected by one
trace-level equality, rather than by separate row and architectural checks. -/
theorem pinned_nontrap_observed_trace_refines_isa :
    normalizeRvfiTrace? 0 nontrapObservations =
      some (trace rvMachine rvMachine.init nontrapInputs) := by
  rw [pinned_nontrap_trace_certificate, pinned_nontrap_trace_refines_isa]

#guard trace rvMachine rvMachine.init nontrapInputs == nontrapExpected
#guard (directRun memZero nontrapMemoryRequests).2 == nontrapMemoryEffects
#guard normalizeRvfiTrace? 0 nontrapObservations == some nontrapExpected
#guard normalizeRvfiTrace? 2 nontrapSecondObservations == some nontrapSecondExpected
#guard (retireInputs pinnedCycleMachine.toCycleMachine
  pinnedCycleMachine.toCycleMachine.init cycleInputs).length == 4
#guard robTrace pinnedCycleMachine.toRobMachine
  pinnedCycleMachine.toRobMachine.init cycleInputs == nontrapExpected
#guard (robInputs pinnedCycleMachine.toRobMachine
  pinnedCycleMachine.toRobMachine.init cycleInputs).length == 4
#guard normalizeRvfiTrace? 0 nontrapObservations ==
  some (trace rvMachine rvMachine.init nontrapInputs)

#print axioms pinned_nontrap_rows_normalize
#print axioms pinned_nontrap_trace_certificate
#print axioms pinned_nontrap_trace_chunks
#print axioms pinned_nontrap_trace_append
#print axioms pinned_nontrap_trace_refines_isa
#print axioms pinned_nontrap_memory_effects
#print axioms pinned_cycle_retire_inputs
#print axioms pinned_cycle_observations_normalize
#print axioms pinned_cycle_trace
#print axioms pinned_rob_trace
#print axioms pinned_rob_inputs
#print axioms pinned_packet_observations_normalize
#print axioms pinned_packet_trace
#print axioms pinned_packet_inputs
#print axioms pinned_packet_rob_trace
#print axioms pinned_packet_rob_inputs
#print axioms pinned_cycle_trace_refines_isa
#print axioms pinned_stateful_memory_trace
#print axioms pinned_nontrap_observed_trace_refines_isa

end Examples.«system-verilog».cores.picorv32.trace_proof
