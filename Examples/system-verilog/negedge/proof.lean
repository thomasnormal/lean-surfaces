import LeanModels.Sv.Load

namespace Examples.systemVerilog.negedgeWait.proof

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

set_option autoImplicit false

def worldOf {α : Type} (m : SvM α) (w : SvWorld) : Option SvWorld :=
  match SvM.exec m w with
  | .ok (.ok _, w') => some w'
  | _ => none

def signalValue (w : SvWorld) (name : String) : Option Nat :=
  (SvState.lookup w.signals name).bind LVec.toNat?

def negedgeWaiting : Option WaitTarget → Bool
  | some (.edge "clk" .neg) => true
  | _ => false

def negedgeReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/negedge/negedge.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "negedge fixture failed to load")
  let .ok world := elabTimedDesign 4096 design
    | throw (IO.userError "negedge fixture failed to elaborate")
  let some waiting := worldOf (stepRegion ρ_src 64 .active) world
    | throw (IO.userError "negedge process did not suspend")
  let some first := waiting.procs[0]?
    | throw (IO.userError "negedge process disappeared after suspension")
  unless first.residual.length == 3 &&
      negedgeWaiting first.registration &&
      signalValue waiting "value" == some 1 do
    throw (IO.userError "negedge suspension did not retain the continuation")
  let some afterWake := worldOf
      (wakeEdges [("clk", .ofNat 1 1)] [("clk", .ofNat 1 0)]) waiting
    | throw (IO.userError "negedge did not wake")
  unless afterWake.regionQ .active == [0] do
    throw (IO.userError "negedge wake did not enqueue Active")
  let some afterRun := worldOf (stepRegion ρ_src 64 .active) afterWake
    | throw (IO.userError "negedge continuation did not run")
  unless signalValue afterRun "value" == some 2 && afterRun.out.flush == ["PASS"] do
    throw (IO.userError "negedge continuation produced the wrong result")
  unless match runSelfCheck design 4096 with
    | .unsupported _ => true
    | _ => false do
    throw (IO.userError "time-zero self-check unexpectedly consumed an event wait")

#eval negedgeReceipt

end Examples.systemVerilog.negedgeWait.proof
