import LeanModels.Sv.Load

namespace Examples.systemVerilog.eventWait.proof

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

set_option autoImplicit false

def worldOf {α : Type} (m : SvM α) (w : SvWorld) : Option SvWorld :=
  match SvM.exec m w with
  | .ok (.ok _, w') => some w'
  | _ => none

def signalValue (w : SvWorld) (name : String) : Option Nat :=
  (SvState.lookup w.signals name).bind LVec.toNat?

def edgeWaiting : Option WaitTarget → Bool
  | some (.edge "clk" .pos) => true
  | _ => false

def eventReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/event/event.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "event fixture failed to load")
  let .ok world := elabTimedDesign 4096 design
    | throw (IO.userError "event fixture failed to elaborate")
  let some waiting := worldOf (stepRegion ρ_src 64 .active) world
    | throw (IO.userError "event process did not suspend")
  let some first := waiting.procs[0]?
    | throw (IO.userError "event process disappeared after suspension")
  unless first.residual.length == 3 &&
      edgeWaiting first.registration &&
      signalValue waiting "value" == some 1 do
    throw (IO.userError "event suspension did not retain the continuation and prior effect")
  let some afterWake := worldOf
      (wakeEdges [("clk", .ofNat 1 0)] [("clk", .ofNat 1 1)]) waiting
    | throw (IO.userError "event edge did not wake")
  unless afterWake.regionQ .active == [0] do
    throw (IO.userError "event wake did not enqueue Active")
  let some afterRun := worldOf (stepRegion ρ_src 64 .active) afterWake
    | throw (IO.userError "event continuation did not run")
  unless signalValue afterRun "value" == some 2 && afterRun.out.flush == ["PASS"] do
    throw (IO.userError "event continuation produced the wrong observable result")
  unless match runSelfCheck design 4096 with
    | .unsupported _ => true
    | _ => false do
    throw (IO.userError "time-zero self-check unexpectedly consumed an event wait")

#eval eventReceipt

end Examples.systemVerilog.eventWait.proof
