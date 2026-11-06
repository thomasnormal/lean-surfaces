import Examples.«system-verilog».cores.picorv32.rvfi_proof
import LeanModels.Refine.Bus
import LeanModels.Refine.Memory
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

def nontrapMemoryPacket : TaggedMemoryPacket :=
  [ { order := 1, request := .write 0x100 .word 5,
      effect := .write 0x100 .word 5 }
  , { order := 2, request := .read 0x100 .word false,
      effect := .read 0x100 .word 5 } ]

def bubbleObservation : RvfiObservation :=
  { valid := false, insn := 0, pcRdata := 0, pcWdata := 0 }

def bubbleInput : Input := { fetched := .word 0, memory := memZero }

/-- The four non-trapping instruction parcels emitted by the pinned witness. -/
def nontrapInputs : List Input :=
  [ { fetched := .word 0x00500093, memory := memZero }
  , { fetched := .word 0x10102023, memory := memZero }
  , { fetched := .word 0x10002103, memory := memFive }
  , { fetched := .word 0x00110193, memory := memFive } ]

def nontrapFirstInputs : List Input :=
  [ { fetched := .word 0x00500093, memory := memZero }
  , { fetched := .word 0x10102023, memory := memZero } ]

def nontrapSecondInputs : List Input :=
  [ { fetched := .word 0x10002103, memory := memFive }
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

def cycleFirstInputs : List Input :=
  [ bubbleInput, { fetched := .word 0x00500093, memory := memZero }
  , bubbleInput, { fetched := .word 0x10102023, memory := memZero } ]

def cycleSecondInputs : List Input :=
  [ bubbleInput, { fetched := .word 0x10002103, memory := memFive }
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

def packetFirstCycles : List Input := [ bubbleInput, bubbleInput ]

def packetSecondCycles : List Input := [ bubbleInput, bubbleInput ]

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

theorem pinned_nontrap_memory_packet :
    TaggedMemoryPacketRefines 1 memZero nontrapMemoryPacket
      (directRun memZero nontrapMemoryRequests).1 := by
  constructor
  · rfl
  · refine MemoryPacketRefines.cons (by decide) ?_
    refine MemoryPacketRefines.cons (by decide) ?_
    exact MemoryPacketRefines.nil _

theorem pinned_nontrap_memory_packet_effects :
    nontrapMemoryPacket.map TaggedMemoryCommit.effect =
      nontrapMemoryEffects := by
  decide

theorem pinned_nontrap_memory_packet_requests :
    nontrapMemoryPacket.map TaggedMemoryCommit.request =
      nontrapMemoryRequests := by
  decide

theorem pinned_nontrap_memory_packet_bus_effects (latency : LatencyOracle) :
    completed
        (runBus memZero (scheduleWith latency
          (nontrapMemoryPacket.map TaggedMemoryCommit.request))).2 =
      nontrapMemoryEffects := by
  have hbus := taggedMemoryPacket_refines_bus
    pinned_nontrap_memory_packet latency
  rw [pinned_nontrap_memory_packet_requests] at hbus
  exact hbus.2.symm.trans pinned_nontrap_memory_packet_effects

theorem pinned_nontrap_bus_effects (latency : LatencyOracle) :
    completed
        (runBus memZero (scheduleWith latency nontrapMemoryRequests)).2 =
      nontrapMemoryEffects := by
  have hdirect :
      (directRun memZero nontrapMemoryRequests).2 = nontrapMemoryEffects := by
    exact pinned_nontrap_memory_effects
  exact (runBus_oracle_projection memZero latency nontrapMemoryRequests).2.trans
    hdirect

theorem pinned_cycle_retire_inputs :
    retireInputs pinnedCycleMachine.toCycleMachine
        pinnedCycleMachine.toCycleMachine.init cycleInputs = nontrapInputs := by
  rfl

theorem pinned_cycle_observations_normalize :
    normalizeRvfiTrace? 0
        (rvfiObservations pinnedCycleMachine pinnedCycleMachine.init cycleInputs) =
      some nontrapExpected := by
  decide

theorem pinned_cycle_first_window_normalize :
    normalizeRvfiTrace? 0
        (rvfiObservations pinnedCycleMachine pinnedCycleMachine.init
          cycleFirstInputs) = some nontrapFirstExpected := by
  decide

theorem pinned_cycle_second_window_normalize :
    normalizeRvfiTrace? 2
        (rvfiObservations pinnedCycleMachine
          (rvfiStateAfter pinnedCycleMachine pinnedCycleMachine.init
            cycleFirstInputs) cycleSecondInputs) =
      some nontrapSecondExpected := by
  decide

theorem pinned_cycle_windows_append :
    normalizeRvfiTrace? 0
        (rvfiObservations pinnedCycleMachine pinnedCycleMachine.init
          (cycleFirstInputs ++ cycleSecondInputs)) =
      some (nontrapFirstExpected ++ nontrapSecondExpected) := by
  exact normalizeRvfiCycleTrace_append pinnedCycleMachine
    pinnedCycleMachine.init cycleFirstInputs cycleSecondInputs
    pinned_cycle_first_window_normalize pinned_cycle_second_window_normalize

theorem pinned_cycle_state_after_bridge :
    rvfiStateAfter pinnedCycleMachine pinnedCycleMachine.init cycleInputs =
      cycleStateAfter pinnedCycleMachine.toCycleMachine
        pinnedCycleMachine.toCycleMachine.init cycleInputs := by
  exact (RvfiCycleMachine.toCycleMachine_stateAfter pinnedCycleMachine
    pinnedCycleMachine.init cycleInputs).symm

theorem pinned_rob_state_after_bridge :
    robStateAfter pinnedCycleMachine.toRobMachine
        pinnedCycleMachine.toRobMachine.init cycleInputs =
      rvfiStateAfter pinnedCycleMachine pinnedCycleMachine.init cycleInputs := by
  exact RvfiCycleMachine.toRobMachine_stateAfter pinnedCycleMachine
    pinnedCycleMachine.init cycleInputs

theorem pinned_cycle_windows_rob_append :
    robTrace pinnedCycleMachine.toRobMachine pinnedCycleMachine.init
        (cycleFirstInputs ++ cycleSecondInputs) =
      nontrapFirstExpected ++ nontrapSecondExpected := by
  exact normalizeRvfiRobTrace_append pinnedCycleMachine pinnedCycleMachine.init
    cycleFirstInputs cycleSecondInputs
    pinned_cycle_first_window_normalize pinned_cycle_second_window_normalize

theorem pinned_cycle_windows_rob_refines_isa_of
    {rel : List RvfiObservation → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedCycleMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedCycleMachine.init rvMachine.init 0) :
    nontrapFirstExpected ++ nontrapSecondExpected =
      trace rvMachine rvMachine.init
        (robInputs pinnedCycleMachine.toRobMachine pinnedCycleMachine.init
          (cycleFirstInputs ++ cycleSecondInputs)) := by
  exact normalizeRvfiRobTrace_refines_append pinnedCycleMachine rvMachine
    rel admit
    pinnedCycleMachine.init rvMachine.init 0
    cycleFirstInputs cycleSecondInputs
    hrob hrel
    pinned_cycle_first_window_normalize pinned_cycle_second_window_normalize

theorem pinned_packet_observations_normalize :
    normalizeRvfiTrace? 0
        (rvfiPacketObservations pinnedPacketMachine pinnedPacketMachine.init
          packetCycleInputs) = some nontrapExpected := by
  decide

theorem pinned_packet_first_window_normalize :
    normalizeRvfiTrace? 0
        (rvfiPacketObservations pinnedPacketMachine pinnedPacketMachine.init
          packetFirstCycles) = some nontrapFirstExpected := by
  decide

theorem pinned_packet_second_window_normalize :
    normalizeRvfiTrace? 2
        (rvfiPacketObservations pinnedPacketMachine
          (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
            packetFirstCycles) packetSecondCycles) =
      some nontrapSecondExpected := by
  decide

theorem pinned_packet_windows_append :
    normalizeRvfiTrace? 0
        (rvfiPacketObservations pinnedPacketMachine pinnedPacketMachine.init
          (packetFirstCycles ++ packetSecondCycles)) =
      some (nontrapFirstExpected ++ nontrapSecondExpected) := by
  exact normalizeRvfiPacketTrace_append pinnedPacketMachine
    pinnedPacketMachine.init packetFirstCycles packetSecondCycles
    pinned_packet_first_window_normalize pinned_packet_second_window_normalize

theorem pinned_packet_windows_rob_append :
    robTrace pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        (packetFirstCycles ++ packetSecondCycles) =
      nontrapFirstExpected ++ nontrapSecondExpected := by
  exact normalizeRvfiPacketRobTrace_append pinnedPacketMachine
    pinnedPacketMachine.init packetFirstCycles packetSecondCycles
    pinned_packet_first_window_normalize pinned_packet_second_window_normalize

theorem pinned_packet_windows_rob_refines_isa_of
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    nontrapFirstExpected ++ nontrapSecondExpected =
      trace rvMachine rvMachine.init
        (robInputs pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          (packetFirstCycles ++ packetSecondCycles)) := by
  exact normalizeRvfiPacketRobTrace_refines_append pinnedPacketMachine rvMachine
    rel admit
    pinnedPacketMachine.init rvMachine.init 0
    packetFirstCycles packetSecondCycles
    hrob hrel
    pinned_packet_first_window_normalize pinned_packet_second_window_normalize

theorem pinned_packet_tags_windows_in_order :
    InOrderPacketStream 0
      (rvfiPacketTags pinnedPacketMachine pinnedPacketMachine.init
        (packetFirstCycles ++ packetSecondCycles)) := by
  exact normalizeRvfiPacketTags_stream_append pinnedPacketMachine
    pinnedPacketMachine.init packetFirstCycles packetSecondCycles
    pinned_packet_first_window_normalize pinned_packet_second_window_normalize

theorem pinned_packet_tags_flat_in_order :
    InOrderTags 0
      (rvfiPacketTags pinnedPacketMachine pinnedPacketMachine.init
        packetCycleInputs).flatten := by
  exact normalizeRvfiPacketTags_flat pinnedPacketMachine
    pinnedPacketMachine.init packetCycleInputs
    pinned_packet_observations_normalize

theorem pinned_packet_rob_tags :
    InOrderTags 0
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        packetCycleInputs) := by
  exact normalizeRvfiPacketRobTags pinnedPacketMachine
    pinnedPacketMachine.init packetCycleInputs
    pinned_packet_observations_normalize

theorem pinned_packet_rob_tags_windows_in_order :
    InOrderTags 0
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        (packetFirstCycles ++ packetSecondCycles)) := by
  exact normalizeRvfiPacketRobTags_append pinnedPacketMachine
    pinnedPacketMachine.init packetFirstCycles packetSecondCycles
    pinned_packet_first_window_normalize pinned_packet_second_window_normalize

theorem pinned_packet_rob_tags_of_refinement
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    InOrderTags 0
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        packetCycleInputs) := by
  exact robTags_in_order_of_refines hrob
    pinnedPacketMachine.init rvMachine.init 0 packetCycleInputs hrel

theorem pinned_packet_rob_tags_refines_isa_of
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    InOrderTags 0
        (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          packetCycleInputs) ∧
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        packetCycleInputs).map TaggedCommit.retirement =
      trace rvMachine rvMachine.init
        (robInputs pinnedPacketMachine.toRobMachine
          pinnedPacketMachine.init packetCycleInputs) := by
  exact normalizeRvfiPacketRobTags_refines pinnedPacketMachine rvMachine
    rel admit pinnedPacketMachine.init rvMachine.init 0 packetCycleInputs
    nontrapExpected hrob hrel pinned_packet_observations_normalize

theorem pinned_packet_rob_tags_refines_state
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    (InOrderTags 0
        (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          packetCycleInputs) ∧
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        packetCycleInputs).map TaggedCommit.retirement =
      trace rvMachine rvMachine.init
        (robInputs pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          packetCycleInputs)) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
        packetCycleInputs)
        (machineStateAfter rvMachine rvMachine.init
          (packetInputs pinnedPacketMachine.toPacketMachine
            pinnedPacketMachine.init packetCycleInputs)) finalOrder ∧
      finalOrder = 0 + nontrapExpected.length) := by
  exact normalizeRvfiPacketRobTags_refines_state pinnedPacketMachine rvMachine
    rel admit pinnedPacketMachine.init rvMachine.init 0 packetCycleInputs
    nontrapExpected hrob hrel pinned_packet_observations_normalize

theorem pinned_packet_windows_certificate :
    normalizeRvfiPacketWindows pinnedPacketMachine pinnedPacketMachine.init 0
      [packetFirstCycles, packetSecondCycles]
      [nontrapFirstExpected, nontrapSecondExpected] := by
  refine ⟨pinned_packet_first_window_normalize, ?_⟩
  refine ⟨?_, trivial⟩
  rw [show nontrapFirstExpected.length = 2 by decide]
  simpa using pinned_packet_second_window_normalize

theorem pinned_packet_windows_certificate_append :
    normalizeRvfiPacketWindows pinnedPacketMachine pinnedPacketMachine.init 0
      ([packetFirstCycles] ++ [packetSecondCycles])
      ([nontrapFirstExpected] ++ [nontrapSecondExpected]) := by
  apply normalizeRvfiPacketWindows_append pinnedPacketMachine
    pinnedPacketMachine.init 0 [packetFirstCycles] [packetSecondCycles]
    [nontrapFirstExpected] [nontrapSecondExpected]
  · exact ⟨pinned_packet_first_window_normalize, trivial⟩
  · rw [show ([nontrapFirstExpected] : List (List Retirement)).flatten.length = 2 by decide]
    simpa [normalizeRvfiPacketWindows, rvfiPacketStateAfter] using
      (show normalizeRvfiPacketWindows pinnedPacketMachine
        (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
          packetFirstCycles) 2 [packetSecondCycles]
        [nontrapSecondExpected] from
        ⟨pinned_packet_second_window_normalize, trivial⟩)

theorem pinned_packet_windows_chain_refines_state
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    (InOrderTags 0
        (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          [packetFirstCycles, packetSecondCycles].flatten) ∧
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten).map
          TaggedCommit.retirement =
        trace rvMachine rvMachine.init
          (robInputs pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
            [packetFirstCycles, packetSecondCycles].flatten)) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten)
        (machineStateAfter rvMachine rvMachine.init
          (packetInputs pinnedPacketMachine.toPacketMachine
            pinnedPacketMachine.init
            [packetFirstCycles, packetSecondCycles].flatten)) finalOrder ∧
      finalOrder = 0 +
        [nontrapFirstExpected, nontrapSecondExpected].flatten.length) := by
  exact normalizeRvfiPacketRobTags_refines_windows pinnedPacketMachine rvMachine
    rel admit pinnedPacketMachine.init rvMachine.init 0
    [packetFirstCycles, packetSecondCycles]
    [nontrapFirstExpected, nontrapSecondExpected] hrob hrel
    pinned_packet_windows_certificate

theorem pinned_packet_windows_chain_refines_state_append
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    (InOrderTags 0
        (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          ([packetFirstCycles] ++ [packetSecondCycles]).flatten) ∧
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        ([packetFirstCycles] ++ [packetSecondCycles]).flatten).map
          TaggedCommit.retirement =
        trace rvMachine rvMachine.init
          (robInputs pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
            ([packetFirstCycles] ++ [packetSecondCycles]).flatten)) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
        ([packetFirstCycles] ++ [packetSecondCycles]).flatten)
        (machineStateAfter rvMachine rvMachine.init
          (packetInputs pinnedPacketMachine.toPacketMachine
            pinnedPacketMachine.init
            ([packetFirstCycles] ++ [packetSecondCycles]).flatten)) finalOrder ∧
      finalOrder = 0 +
        ([nontrapFirstExpected] ++ [nontrapSecondExpected]).flatten.length) := by
  apply normalizeRvfiPacketRobTags_refines_windows_append pinnedPacketMachine
    rvMachine rel admit pinnedPacketMachine.init rvMachine.init 0
    [packetFirstCycles] [packetSecondCycles]
    [nontrapFirstExpected] [nontrapSecondExpected] hrob hrel
  · exact ⟨pinned_packet_first_window_normalize, trivial⟩
  · rw [show ([nontrapFirstExpected] : List (List Retirement)).flatten.length = 2 by decide]
    simpa [normalizeRvfiPacketWindows, rvfiPacketStateAfter] using
      (show normalizeRvfiPacketWindows pinnedPacketMachine
        (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
          packetFirstCycles) 2 [packetSecondCycles]
        [nontrapSecondExpected] from
        ⟨pinned_packet_second_window_normalize, trivial⟩)

theorem pinned_packet_windows_tags_stream :
    InOrderPacketStream 0
      (rvfiPacketTags pinnedPacketMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten) := by
  exact normalizeRvfiPacketWindows_tags_stream pinnedPacketMachine
    pinnedPacketMachine.init 0
    [packetFirstCycles, packetSecondCycles]
    [nontrapFirstExpected, nontrapSecondExpected]
    pinned_packet_windows_certificate

theorem pinned_packet_windows_tags_stream_append :
    InOrderPacketStream 0
      (rvfiPacketTags pinnedPacketMachine pinnedPacketMachine.init
        ([packetFirstCycles] ++ [packetSecondCycles]).flatten) := by
  apply normalizeRvfiPacketWindows_tags_stream_append pinnedPacketMachine
    pinnedPacketMachine.init 0 [packetFirstCycles] [packetSecondCycles]
    [nontrapFirstExpected] [nontrapSecondExpected]
  · exact ⟨pinned_packet_first_window_normalize, trivial⟩
  · rw [show ([nontrapFirstExpected] : List (List Retirement)).flatten.length = 2 by decide]
    simpa [normalizeRvfiPacketWindows, rvfiPacketStateAfter] using
      (show normalizeRvfiPacketWindows pinnedPacketMachine
        (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
          packetFirstCycles) 2 [packetSecondCycles]
        [nontrapSecondExpected] from
        ⟨pinned_packet_second_window_normalize, trivial⟩)

theorem pinned_packet_windows_tags_flat :
    InOrderTags 0
      (rvfiPacketTags pinnedPacketMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten).flatten := by
  exact normalizeRvfiPacketWindows_tags_flat pinnedPacketMachine
    pinnedPacketMachine.init 0
    [packetFirstCycles, packetSecondCycles]
    [nontrapFirstExpected, nontrapSecondExpected]
    pinned_packet_windows_certificate

theorem pinned_packet_windows_tags_flat_append :
    InOrderTags 0
      (rvfiPacketTags pinnedPacketMachine pinnedPacketMachine.init
        ([packetFirstCycles] ++ [packetSecondCycles]).flatten).flatten := by
  apply normalizeRvfiPacketWindows_tags_flat_append pinnedPacketMachine
    pinnedPacketMachine.init 0 [packetFirstCycles] [packetSecondCycles]
    [nontrapFirstExpected] [nontrapSecondExpected]
  · exact ⟨pinned_packet_first_window_normalize, trivial⟩
  · rw [show ([nontrapFirstExpected] : List (List Retirement)).flatten.length = 2 by decide]
    simpa [normalizeRvfiPacketWindows, rvfiPacketStateAfter] using
      (show normalizeRvfiPacketWindows pinnedPacketMachine
        (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
          packetFirstCycles) 2 [packetSecondCycles]
        [nontrapSecondExpected] from
        ⟨pinned_packet_second_window_normalize, trivial⟩)

theorem pinned_packet_windows_rob_trace_chain :
    robTrace pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten =
      [nontrapFirstExpected, nontrapSecondExpected].flatten := by
  exact normalizeRvfiPacketWindows_rob_trace pinnedPacketMachine
    pinnedPacketMachine.init 0
    [packetFirstCycles, packetSecondCycles]
    [nontrapFirstExpected, nontrapSecondExpected]
    pinned_packet_windows_certificate

theorem pinned_packet_windows_rob_trace_append :
    robTrace pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        ([packetFirstCycles] ++ [packetSecondCycles]).flatten =
      ([nontrapFirstExpected] ++ [nontrapSecondExpected]).flatten := by
  apply normalizeRvfiPacketWindows_rob_trace_append pinnedPacketMachine
    pinnedPacketMachine.init 0 [packetFirstCycles] [packetSecondCycles]
    [nontrapFirstExpected] [nontrapSecondExpected]
  · exact ⟨pinned_packet_first_window_normalize, trivial⟩
  · rw [show ([nontrapFirstExpected] : List (List Retirement)).flatten.length = 2 by decide]
    simpa [normalizeRvfiPacketWindows, rvfiPacketStateAfter] using
      (show normalizeRvfiPacketWindows pinnedPacketMachine
        (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
          packetFirstCycles) 2 [packetSecondCycles]
        [nontrapSecondExpected] from
        ⟨pinned_packet_second_window_normalize, trivial⟩)

theorem pinned_packet_windows_rob_tags_chain :
    InOrderTags 0
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten) := by
  exact normalizeRvfiPacketWindows_rob_tags pinnedPacketMachine
    pinnedPacketMachine.init 0
    [packetFirstCycles, packetSecondCycles]
    [nontrapFirstExpected, nontrapSecondExpected]
    pinned_packet_windows_certificate

theorem pinned_packet_windows_rob_tags_append :
    InOrderTags 0
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        ([packetFirstCycles] ++ [packetSecondCycles]).flatten) := by
  apply normalizeRvfiPacketWindows_rob_tags_append pinnedPacketMachine
    pinnedPacketMachine.init 0 [packetFirstCycles] [packetSecondCycles]
    [nontrapFirstExpected] [nontrapSecondExpected]
  · exact ⟨pinned_packet_first_window_normalize, trivial⟩
  · rw [show ([nontrapFirstExpected] : List (List Retirement)).flatten.length = 2 by decide]
    simpa [normalizeRvfiPacketWindows, rvfiPacketStateAfter] using
      (show normalizeRvfiPacketWindows pinnedPacketMachine
        (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
          packetFirstCycles) 2 [packetSecondCycles]
        [nontrapSecondExpected] from
        ⟨pinned_packet_second_window_normalize, trivial⟩)

theorem pinned_packet_windows_rob_tags_retirements_chain :
    (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten).map
        TaggedCommit.retirement =
      [nontrapFirstExpected, nontrapSecondExpected].flatten := by
  exact normalizeRvfiPacketWindows_rob_tags_retirements pinnedPacketMachine
    pinnedPacketMachine.init 0
    [packetFirstCycles, packetSecondCycles]
    [nontrapFirstExpected, nontrapSecondExpected]
    pinned_packet_windows_certificate

theorem pinned_packet_windows_rob_tags_retirements_append :
    (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        ([packetFirstCycles] ++ [packetSecondCycles]).flatten).map
        TaggedCommit.retirement =
      ([nontrapFirstExpected] ++ [nontrapSecondExpected]).flatten := by
  apply normalizeRvfiPacketWindows_rob_tags_retirements_append
    pinnedPacketMachine pinnedPacketMachine.init 0
    [packetFirstCycles] [packetSecondCycles]
    [nontrapFirstExpected] [nontrapSecondExpected]
  · exact ⟨pinned_packet_first_window_normalize, trivial⟩
  · rw [show ([nontrapFirstExpected] : List (List Retirement)).flatten.length = 2 by decide]
    simpa [normalizeRvfiPacketWindows, rvfiPacketStateAfter] using
      (show normalizeRvfiPacketWindows pinnedPacketMachine
        (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
          packetFirstCycles) 2 [packetSecondCycles]
        [nontrapSecondExpected] from
        ⟨pinned_packet_second_window_normalize, trivial⟩)

theorem pinned_packet_windows_rob_tags_inputs_chain :
    (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten).map
        TaggedCommit.input =
      packetInputs pinnedPacketMachine.toPacketMachine
        pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten := by
  exact RvfiPacketMachine.toRobMachine_tags_inputs pinnedPacketMachine
    pinnedPacketMachine.init [packetFirstCycles, packetSecondCycles].flatten

theorem pinned_packet_windows_rob_tags_length_chain :
    (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten).length =
      [nontrapFirstExpected, nontrapSecondExpected].flatten.length := by
  exact normalizeRvfiPacketWindows_rob_tags_length pinnedPacketMachine
    pinnedPacketMachine.init 0
    [packetFirstCycles, packetSecondCycles]
    [nontrapFirstExpected, nontrapSecondExpected]
    pinned_packet_windows_certificate

theorem pinned_packet_windows_rob_tags_inputs_length_chain :
    ((robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        [packetFirstCycles, packetSecondCycles].flatten).map
        TaggedCommit.input).length =
      [nontrapFirstExpected, nontrapSecondExpected].flatten.length := by
  exact normalizeRvfiPacketWindows_rob_tags_inputs_length pinnedPacketMachine
    pinnedPacketMachine.init 0
    [packetFirstCycles, packetSecondCycles]
    [nontrapFirstExpected, nontrapSecondExpected]
    pinned_packet_windows_certificate

theorem pinned_packet_windows_rob_trace_refines_isa
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    [nontrapFirstExpected, nontrapSecondExpected].flatten =
      trace rvMachine rvMachine.init
        (robInputs pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          [packetFirstCycles, packetSecondCycles].flatten) := by
  exact normalizeRvfiPacketWindows_rob_trace_refines pinnedPacketMachine rvMachine
    rel admit pinnedPacketMachine.init rvMachine.init 0
    [packetFirstCycles, packetSecondCycles]
    [nontrapFirstExpected, nontrapSecondExpected] hrob hrel
    pinned_packet_windows_certificate

theorem pinned_packet_windows_rob_trace_refines_isa_append
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    ([nontrapFirstExpected] ++ [nontrapSecondExpected]).flatten =
      trace rvMachine rvMachine.init
        (robInputs pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          ([packetFirstCycles] ++ [packetSecondCycles]).flatten) := by
  apply normalizeRvfiPacketWindows_rob_trace_refines_append
    pinnedPacketMachine rvMachine rel admit pinnedPacketMachine.init
    rvMachine.init 0 [packetFirstCycles] [packetSecondCycles]
    [nontrapFirstExpected] [nontrapSecondExpected] hrob hrel
  · exact ⟨pinned_packet_first_window_normalize, trivial⟩
  · rw [show ([nontrapFirstExpected] : List (List Retirement)).flatten.length = 2 by decide]
    simpa [normalizeRvfiPacketWindows, rvfiPacketStateAfter] using
      (show normalizeRvfiPacketWindows pinnedPacketMachine
        (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
          packetFirstCycles) 2 [packetSecondCycles]
        [nontrapSecondExpected] from
        ⟨pinned_packet_second_window_normalize, trivial⟩)

theorem pinned_packet_state_after_refines_normalized
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    ∃ finalOrder,
      rel (rvfiPacketStateAfter pinnedPacketMachine
        pinnedPacketMachine.init packetCycleInputs)
        (machineStateAfter rvMachine rvMachine.init
          (packetInputs pinnedPacketMachine.toPacketMachine
            pinnedPacketMachine.init packetCycleInputs)) finalOrder ∧
      finalOrder = 0 + nontrapExpected.length := by
  exact rvfiPacketStateAfter_refines_normalized pinnedPacketMachine rvMachine
    rel admit 0 hrob pinnedPacketMachine.init rvMachine.init hrel
    packetCycleInputs nontrapExpected pinned_packet_observations_normalize

theorem pinned_packet_state_after_refines_normalized_windows
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    ∃ finalOrder,
      rel (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
        (packetFirstCycles ++ packetSecondCycles))
        (machineStateAfter rvMachine rvMachine.init
          (packetInputs pinnedPacketMachine.toPacketMachine
            pinnedPacketMachine.init (packetFirstCycles ++ packetSecondCycles)))
          finalOrder ∧
      finalOrder = 0 +
        (nontrapFirstExpected ++ nontrapSecondExpected).length := by
  exact rvfiPacketStateAfter_refines_normalized_append pinnedPacketMachine
    rvMachine rel admit 0 hrob pinnedPacketMachine.init rvMachine.init hrel
    packetFirstCycles packetSecondCycles
    pinned_packet_first_window_normalize pinned_packet_second_window_normalize

theorem pinned_packet_rob_tags_refines_isa_windows_of
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    InOrderTags 0
        (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          (packetFirstCycles ++ packetSecondCycles)) ∧
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        (packetFirstCycles ++ packetSecondCycles)).map
          TaggedCommit.retirement =
        trace rvMachine rvMachine.init
          (robInputs pinnedPacketMachine.toRobMachine
            pinnedPacketMachine.init (packetFirstCycles ++ packetSecondCycles)) := by
  exact normalizeRvfiPacketRobTags_refines_append pinnedPacketMachine rvMachine
    rel admit pinnedPacketMachine.init rvMachine.init 0 packetFirstCycles
    packetSecondCycles hrob hrel pinned_packet_first_window_normalize
    pinned_packet_second_window_normalize

theorem pinned_packet_rob_tags_refines_state_windows
    {rel : List (List RvfiPacketEntry) → ArchState → Nat → Prop}
    {admit : Input → Prop}
    (hrob : RobStepRefines pinnedPacketMachine.toRobMachine rvMachine
      rel 0 admit)
    (hrel : rel pinnedPacketMachine.init rvMachine.init 0) :
    (InOrderTags 0
        (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
          (packetFirstCycles ++ packetSecondCycles)) ∧
      (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        (packetFirstCycles ++ packetSecondCycles)).map
          TaggedCommit.retirement =
        trace rvMachine rvMachine.init
          (robInputs pinnedPacketMachine.toRobMachine
            pinnedPacketMachine.init (packetFirstCycles ++ packetSecondCycles))) ∧
    (∃ finalOrder,
      rel (rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
        (packetFirstCycles ++ packetSecondCycles))
        (machineStateAfter rvMachine rvMachine.init
          (packetInputs pinnedPacketMachine.toPacketMachine
            pinnedPacketMachine.init (packetFirstCycles ++ packetSecondCycles)))
          finalOrder ∧
      finalOrder = 0 +
        (nontrapFirstExpected ++ nontrapSecondExpected).length) := by
  exact normalizeRvfiPacketRobTags_refines_state_append pinnedPacketMachine
    rvMachine rel admit pinnedPacketMachine.init rvMachine.init 0
    packetFirstCycles packetSecondCycles hrob hrel
    pinned_packet_first_window_normalize pinned_packet_second_window_normalize

theorem pinned_packet_state_after_bridge :
    rvfiPacketStateAfter pinnedPacketMachine pinnedPacketMachine.init
        (packetFirstCycles ++ packetSecondCycles) =
      robStateAfter pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
        (packetFirstCycles ++ packetSecondCycles) := by
  symm
  exact RvfiPacketMachine.toRobMachine_stateAfter pinnedPacketMachine
    pinnedPacketMachine.init (packetFirstCycles ++ packetSecondCycles)

theorem pinned_packet_first_tags :
    InOrderTags 0
        ((packetRows[0]!).filterMap RvfiPacketEntry.toTaggedCommit?) := by
  apply normalizeRvfiPacketTags (retirements := expected.take 1)
  decide

theorem pinned_packet_tags_stream :
    InOrderPacketStream 0
        (rvfiPacketTags pinnedPacketMachine pinnedPacketMachine.init
          packetCycleInputs) := by
  exact normalizeRvfiPacketTags_stream pinnedPacketMachine pinnedPacketMachine.init
    packetCycleInputs pinned_packet_observations_normalize

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

theorem pinned_rob_trace_refines_isa :
    robTrace pinnedCycleMachine.toRobMachine
        pinnedCycleMachine.toRobMachine.init cycleInputs =
      trace rvMachine rvMachine.init
        (robInputs pinnedCycleMachine.toRobMachine
          pinnedCycleMachine.toRobMachine.init cycleInputs) := by
  calc
    robTrace pinnedCycleMachine.toRobMachine
        pinnedCycleMachine.toRobMachine.init cycleInputs = nontrapExpected :=
      pinned_rob_trace
    _ = trace rvMachine rvMachine.init nontrapInputs :=
      pinned_nontrap_trace_refines_isa
    _ = trace rvMachine rvMachine.init
        (robInputs pinnedCycleMachine.toRobMachine
          pinnedCycleMachine.toRobMachine.init cycleInputs) := by
      rw [RvfiCycleMachine.toRobMachine_init]
      rw [RvfiCycleMachine.toRobMachine_inputs]
      exact congrArg (trace rvMachine rvMachine.init)
        pinned_cycle_retire_inputs

theorem pinned_rob_retirement_count :
    (robInputs pinnedCycleMachine.toRobMachine pinnedCycleMachine.init
      cycleInputs).length = nontrapExpected.length := by
  exact normalizeRvfiRobTrace_input_length pinnedCycleMachine
    pinnedCycleMachine.init cycleInputs pinned_cycle_observations_normalize

theorem pinned_rob_order_offset :
    0 + (robInputs pinnedCycleMachine.toRobMachine pinnedCycleMachine.init
      cycleInputs).length = nontrapExpected.length := by
  simpa using pinned_rob_retirement_count

theorem pinned_cycle_tags :
    InOrderTags 0
      (rvfiRobTags pinnedCycleMachine pinnedCycleMachine.init cycleInputs) := by
  exact normalizeRvfiRobTags pinnedCycleMachine pinnedCycleMachine.init
    cycleInputs pinned_cycle_observations_normalize

theorem pinned_cycle_tags_windows_append :
    rvfiRobTags pinnedCycleMachine pinnedCycleMachine.init
        (cycleFirstInputs ++ cycleSecondInputs) =
      rvfiRobTags pinnedCycleMachine pinnedCycleMachine.init cycleFirstInputs ++
        rvfiRobTags pinnedCycleMachine
          (rvfiStateAfter pinnedCycleMachine pinnedCycleMachine.init
            cycleFirstInputs) cycleSecondInputs := by
  exact rvfiRobTags_append pinnedCycleMachine pinnedCycleMachine.init
    cycleFirstInputs cycleSecondInputs

theorem pinned_cycle_tags_windows_in_order :
    InOrderTags 0
      (rvfiRobTags pinnedCycleMachine pinnedCycleMachine.init
        (cycleFirstInputs ++ cycleSecondInputs)) := by
  exact normalizeRvfiRobTags_append pinnedCycleMachine pinnedCycleMachine.init
    cycleFirstInputs cycleSecondInputs
    pinned_cycle_first_window_normalize pinned_cycle_second_window_normalize

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

theorem pinned_packet_rob_tags_retirements :
    (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
      packetCycleInputs).map TaggedCommit.retirement = nontrapExpected := by
  rw [robTags_retirements]
  exact pinned_packet_rob_trace

theorem pinned_packet_rob_tags_inputs :
    (robTags pinnedPacketMachine.toRobMachine pinnedPacketMachine.init
      packetCycleInputs).map TaggedCommit.input = nontrapInputs := by
  rw [robTags_inputs]
  exact pinned_packet_rob_inputs

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

theorem pinned_stateful_memory_arch :
    (rvMemoryStateAfter cv32e40pProfile
      { arch := rvMachine.init, memory := memZero } nontrapInputs).arch =
      machineStateAfter (rvMachineWith cv32e40pProfile) rvMachine.init
        (threadRvInputs cv32e40pProfile rvMachine.init memZero nontrapInputs) := by
  exact rvMemoryStateAfter_arch cv32e40pProfile rvMachine.init memZero
    nontrapInputs

theorem pinned_stateful_memory_windows :
    trace (rvMemoryMachineWith cv32e40pProfile)
        { arch := rvMachine.init, memory := memZero }
        (nontrapFirstInputs ++ nontrapSecondInputs) =
      trace (rvMemoryMachineWith cv32e40pProfile)
        { arch := rvMachine.init, memory := memZero } nontrapFirstInputs ++
        trace (rvMemoryMachineWith cv32e40pProfile)
          (rvMemoryStateAfter cv32e40pProfile
            { arch := rvMachine.init, memory := memZero } nontrapFirstInputs)
          nontrapSecondInputs := by
  exact rvMemoryMachine_trace_append cv32e40pProfile
    { arch := rvMachine.init, memory := memZero }
    nontrapFirstInputs nontrapSecondInputs

/-- The measured packed stream and the ISA stream are connected by one
trace-level equality, rather than by separate row and architectural checks. -/
theorem pinned_nontrap_observed_trace_refines_isa :
    normalizeRvfiTrace? 0 nontrapObservations =
      some (trace rvMachine rvMachine.init nontrapInputs) := by
  rw [pinned_nontrap_trace_certificate, pinned_nontrap_trace_refines_isa]

#guard trace rvMachine rvMachine.init nontrapInputs == nontrapExpected
#guard (directRun memZero nontrapMemoryRequests).2 == nontrapMemoryEffects
#guard normalizeRvfiTrace? 0 nontrapObservations == some nontrapExpected
#guard normalizeRvfiTrace? 0
  (rvfiObservations pinnedCycleMachine pinnedCycleMachine.init
    (cycleFirstInputs ++ cycleSecondInputs)) ==
  some (nontrapFirstExpected ++ nontrapSecondExpected)
#guard (trace (rvMemoryMachineWith cv32e40pProfile)
  { arch := rvMachine.init, memory := memZero }
  (nontrapFirstInputs ++ nontrapSecondInputs)).length == 4
#guard normalizeRvfiTrace? 2 nontrapSecondObservations == some nontrapSecondExpected
#guard normalizeRvfiTrace? 0
  (rvfiPacketObservations pinnedPacketMachine pinnedPacketMachine.init
    (packetFirstCycles ++ packetSecondCycles)) ==
  some (nontrapFirstExpected ++ nontrapSecondExpected)
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
#print axioms pinned_nontrap_memory_packet
#print axioms pinned_nontrap_memory_packet_effects
#print axioms pinned_nontrap_memory_packet_requests
#print axioms pinned_nontrap_memory_packet_bus_effects
#print axioms pinned_nontrap_bus_effects
#print axioms pinned_cycle_retire_inputs
#print axioms pinned_cycle_observations_normalize
#print axioms pinned_cycle_first_window_normalize
#print axioms pinned_cycle_second_window_normalize
#print axioms pinned_cycle_windows_append
#print axioms pinned_cycle_state_after_bridge
#print axioms pinned_rob_state_after_bridge
#print axioms pinned_cycle_windows_rob_append
#print axioms pinned_cycle_windows_rob_refines_isa_of
#print axioms pinned_cycle_trace
#print axioms pinned_rob_trace
#print axioms pinned_rob_trace_refines_isa
#print axioms pinned_rob_inputs
#print axioms pinned_rob_retirement_count
#print axioms pinned_rob_order_offset
#print axioms pinned_cycle_tags
#print axioms pinned_cycle_tags_windows_append
#print axioms pinned_cycle_tags_windows_in_order
#print axioms pinned_packet_observations_normalize
#print axioms pinned_packet_first_window_normalize
#print axioms pinned_packet_second_window_normalize
#print axioms pinned_packet_windows_append
#print axioms pinned_packet_windows_rob_append
#print axioms pinned_packet_windows_rob_refines_isa_of
#print axioms pinned_packet_tags_windows_in_order
#print axioms pinned_packet_tags_flat_in_order
#print axioms pinned_packet_rob_tags
#print axioms pinned_packet_rob_tags_windows_in_order
#print axioms pinned_packet_rob_tags_of_refinement
#print axioms pinned_packet_rob_tags_refines_isa_of
#print axioms pinned_packet_rob_tags_refines_state
#print axioms pinned_packet_state_after_refines_normalized
#print axioms pinned_packet_state_after_refines_normalized_windows
#print axioms pinned_packet_rob_tags_refines_isa_windows_of
#print axioms pinned_packet_rob_tags_refines_state_windows
#print axioms pinned_packet_windows_certificate
#print axioms pinned_packet_windows_certificate_append
#print axioms pinned_packet_windows_chain_refines_state
#print axioms pinned_packet_windows_chain_refines_state_append
#print axioms pinned_packet_windows_tags_stream
#print axioms pinned_packet_windows_tags_stream_append
#print axioms pinned_packet_windows_tags_flat
#print axioms pinned_packet_windows_tags_flat_append
#print axioms pinned_packet_windows_rob_trace_chain
#print axioms pinned_packet_windows_rob_trace_append
#print axioms pinned_packet_windows_rob_tags_chain
#print axioms pinned_packet_windows_rob_tags_append
#print axioms pinned_packet_windows_rob_tags_retirements_chain
#print axioms pinned_packet_windows_rob_tags_retirements_append
#print axioms pinned_packet_windows_rob_tags_inputs_chain
#print axioms pinned_packet_windows_rob_tags_length_chain
#print axioms pinned_packet_windows_rob_tags_inputs_length_chain
#print axioms pinned_packet_windows_rob_trace_refines_isa
#print axioms pinned_packet_windows_rob_trace_refines_isa_append
#print axioms pinned_packet_state_after_bridge
#print axioms pinned_packet_first_tags
#print axioms pinned_packet_tags_stream
#print axioms pinned_packet_trace
#print axioms pinned_packet_inputs
#print axioms pinned_packet_rob_trace
#print axioms pinned_packet_rob_inputs
#print axioms pinned_packet_rob_tags_retirements
#print axioms pinned_packet_rob_tags_inputs
#print axioms pinned_cycle_trace_refines_isa
#print axioms pinned_stateful_memory_trace
#print axioms pinned_stateful_memory_arch
#print axioms pinned_stateful_memory_windows
#print axioms pinned_nontrap_observed_trace_refines_isa

end Examples.«system-verilog».cores.picorv32.trace_proof
