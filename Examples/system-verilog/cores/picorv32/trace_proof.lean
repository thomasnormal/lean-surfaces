import Examples.«system-verilog».cores.picorv32.rvfi_proof

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

/-- The four non-trapping instruction parcels emitted by the pinned witness. -/
def nontrapInputs : List Input :=
  [ { fetched := .word 0x00500093, memory := memZero }
  , { fetched := .word 0x10102023, memory := memZero }
  , { fetched := .word 0x10002103, memory := memFive }
  , { fetched := .word 0x00110193, memory := memFive } ]

def nontrapObservations : List RvfiObservation := observations.take 4

def nontrapExpected : List Retirement := expected.take 4

theorem pinned_nontrap_rows_normalize :
    nontrapObservations.map RvfiObservation.toRetirement? =
      nontrapExpected.map some := by
  decide

theorem pinned_nontrap_trace_certificate :
    normalizeRvfiTrace? 0 nontrapObservations = some nontrapExpected := by
  decide

/-- The measured non-trapping PicoRV32 stream has exactly the ISA effects. -/
theorem pinned_nontrap_trace_refines_isa :
    trace rvMachine rvMachine.init nontrapInputs = nontrapExpected := by
  decide

/-- The measured packed stream and the ISA stream are connected by one
trace-level equality, rather than by separate row and architectural checks. -/
theorem pinned_nontrap_observed_trace_refines_isa :
    normalizeRvfiTrace? 0 nontrapObservations =
      some (trace rvMachine rvMachine.init nontrapInputs) := by
  rw [pinned_nontrap_trace_certificate, pinned_nontrap_trace_refines_isa]

#guard trace rvMachine rvMachine.init nontrapInputs == nontrapExpected
#guard normalizeRvfiTrace? 0 nontrapObservations == some nontrapExpected
#guard normalizeRvfiTrace? 0 nontrapObservations ==
  some (trace rvMachine rvMachine.init nontrapInputs)

#print axioms pinned_nontrap_rows_normalize
#print axioms pinned_nontrap_trace_certificate
#print axioms pinned_nontrap_trace_refines_isa
#print axioms pinned_nontrap_observed_trace_refines_isa

end Examples.«system-verilog».cores.picorv32.trace_proof
