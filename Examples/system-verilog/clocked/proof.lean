import LeanModels.Sv.Load

namespace Examples.systemVerilog.clocked.proof

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

def clockedReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/clocked/clocked.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "clocked fixture failed to load")
  let .ok world := elabTimedDesign 4096 design
    | throw (IO.userError "clocked fixture failed to elaborate")
  let some initial := world.procs[0]?
    | throw (IO.userError "clocked process missing")
  unless initial.arm.isSome && initial.residual.length == 2 do
    throw (IO.userError "clocked process was not armed")
  let some waiting := worldOf (stepRegion ρ_src 64 .active) world
    | throw (IO.userError "clocked process did not reach its wait")
  let some parked := waiting.procs[0]?
    | throw (IO.userError "clocked process disappeared")
  unless edgeWaiting parked.registration && parked.arm.isSome do
    throw (IO.userError "clocked process did not retain its edge wait")
  let some firstReady := worldOf
      (do wakeEdges [("clk", .ofNat 1 0)] [("clk", .ofNat 1 1)]; stepRegion ρ_src 64 .active)
      waiting
    | throw (IO.userError "clocked process did not run on first edge")
  unless signalValue firstReady "value" == some 1 && firstReady.regionQ .active == [0] do
    throw (IO.userError "clocked process did not re-arm")
  let some parkedAgain := worldOf (stepRegion ρ_src 64 .active) firstReady
    | throw (IO.userError "clocked process did not re-enter its wait")
  let some second := parkedAgain.procs[0]?
    | throw (IO.userError "clocked process disappeared after re-arm")
  unless edgeWaiting second.registration && second.arm.isSome do
    throw (IO.userError "clocked process lost its re-armed wait")
  unless match runSelfCheck design 4096 with
    | .unsupported _ => true
    | _ => false do
    throw (IO.userError "time-zero self-check unexpectedly consumed AlwaysPosedge")

#eval clockedReceipt

end Examples.systemVerilog.clocked.proof
