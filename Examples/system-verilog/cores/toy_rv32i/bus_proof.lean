import LeanModels.Refine.Bus

/-!
# Timed memory contract example

This is a contract-level example, not a claim about the hand-written toy RTL.
The request sequence exercises a word store followed by reads of different
widths and signedness.  The theorem consumes the generic bridge for an
arbitrary latency oracle, so the concrete schedule below is only a reduction
check for the byte-level `loadVal`/`storeVal` behavior.
-/

namespace Examples.«system-verilog».cores.toy_rv32i.bus_proof

open LeanModels.Rv
open LeanModels.Refine

def zeroMemory : Memory := fun _ => 0

def requests : List BusRequest :=
  [ .write 0x100 .word 0xDEADBEEF
  , .read 0x100 .word false
  , .read 0x101 .half false
  , .read 0x103 .byte true ]

def latency : LatencyOracle
  | 0 => 4
  | 1 => 0
  | 2 => 7
  | _ => 1

theorem timed_bus_refines_direct :
    (runBus zeroMemory (scheduleWith latency requests)).1 =
        (directRun zeroMemory requests).1 ∧
      completed (runBus zeroMemory (scheduleWith latency requests)).2 =
        (directRun zeroMemory requests).2 := by
  exact runBus_oracle_projection zeroMemory latency requests

#guard (directRun zeroMemory requests).2 ==
  [ .write 0x100 .word 0xDEADBEEF
  , .read 0x100 .word 0xDEADBEEF
  , .read 0x101 .half 0x0000ADBE
  , .read 0x103 .byte 0xFFFFFFDE ]

#guard (completed (runBus zeroMemory (scheduleWith latency requests)).2).length ==
  requests.length

#print axioms timed_bus_refines_direct

end Examples.«system-verilog».cores.toy_rv32i.bus_proof
