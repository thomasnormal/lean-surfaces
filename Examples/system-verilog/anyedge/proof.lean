import LeanModels.Sv.Load

namespace Examples.systemVerilog.anyedgeWait.proof

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

set_option autoImplicit false

def worldOf {α : Type} (m : SvM α) (w : SvWorld) : Option SvWorld :=
  match SvM.exec m w with
  | .ok (.ok _, w') => some w'
  | _ => none

def signalValue (w : SvWorld) (name : String) : Option Nat :=
  (SvState.lookup w.signals name).bind LVec.toNat?

def anyWaiting : Option WaitTarget → Bool
  | some (.edge "clk" .any) => true
  | _ => false

def anyedgeReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/anyedge/anyedge.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "any-edge fixture failed to load")
  let .ok world := elabTimedDesign 4096 design
    | throw (IO.userError "any-edge fixture failed to elaborate")
  let some waiting := worldOf (stepRegion ρ_src 64 .active) world
    | throw (IO.userError "any-edge process did not suspend")
  let some first := waiting.procs[0]?
    | throw (IO.userError "any-edge process disappeared after suspension")
  unless first.residual.length == 3 &&
      anyWaiting first.registration &&
      signalValue waiting "value" == some 1 do
    throw (IO.userError "any-edge suspension did not retain the continuation")
  let some afterWake := worldOf
      (wakeEdges [("clk", .replicate 1 .lx)] [("clk", .replicate 1 .lz)]) waiting
    | throw (IO.userError "any-edge x-to-z change did not wake")
  unless afterWake.regionQ .active == [0] do
    throw (IO.userError "any-edge wake did not enqueue Active")
  let some afterRun := worldOf (stepRegion ρ_src 64 .active) afterWake
    | throw (IO.userError "any-edge continuation did not run")
  unless signalValue afterRun "value" == some 2 && afterRun.out.flush == ["PASS"] do
    throw (IO.userError "any-edge continuation produced the wrong result")
  unless match runSelfCheck design 4096 with
    | .unsupported _ => true
    | _ => false do
    throw (IO.userError "time-zero self-check unexpectedly consumed an event wait")

#eval anyedgeReceipt

end Examples.systemVerilog.anyedgeWait.proof
