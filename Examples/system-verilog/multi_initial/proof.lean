import LeanModels.Sv.Load

namespace Examples.systemVerilog.multiInitial.proof

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

set_option autoImplicit false

def worldOf {α : Type} (m : SvM α) (w : SvWorld) : Option SvWorld :=
  match SvM.exec m w with
  | .ok (.ok _, w') => some w'
  | _ => none

def signalValue (w : SvWorld) (name : String) : Option Nat :=
  (SvState.lookup w.signals name).bind LVec.toNat?

def multiInitialReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/multi_initial/multi_initial.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "multi-initial fixture failed to load")
  let .ok world := elabTimedDesign 4096 design
    | throw (IO.userError "multi-initial fixture failed to elaborate")
  unless world.procs.size == 2 && world.regionQ .active == [0, 1] do
    throw (IO.userError "timed loader did not schedule all initial processes")
  let some afterStart := worldOf (stepRegion ρ_src 64 .active) world
    | throw (IO.userError "multi-initial processes did not start")
  unless afterStart.procs.size == 2 && signalValue afterStart "value" == some 1 do
    throw (IO.userError "first initial effect was lost")
  let some afterWake := worldOf (do advanceTime 1; wakeTimers) afterStart
    | throw (IO.userError "multi-initial timers did not wake")
  unless afterWake.regionQ .active == [0, 1] do
    throw (IO.userError "all due initial continuations were not enqueued")
  let some afterRun := worldOf (stepRegion ρ_src 64 .active) afterWake
    | throw (IO.userError "multi-initial continuations did not run")
  unless signalValue afterRun "value" == some 2 && afterRun.out.flush == ["PASS"] do
    throw (IO.userError "multi-initial observable result was wrong")
  unless match runSelfCheck design 4096 with
    | .unsupported _ => true
    | _ => false do
    throw (IO.userError "time-zero self-check unexpectedly consumed timed initials")

#eval multiInitialReceipt

end Examples.systemVerilog.multiInitial.proof
