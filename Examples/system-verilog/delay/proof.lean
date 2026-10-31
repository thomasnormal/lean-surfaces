import LeanModels.Sv.Load

namespace Examples.systemVerilog.delay.proof

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

set_option autoImplicit false

def worldOf {α : Type} (m : SvM α) (w : SvWorld) : Option SvWorld :=
  match SvM.exec m w with
  | .ok (.ok _, w') => some w'
  | _ => none

def signalValue (w : SvWorld) (name : String) : Option Nat :=
  (SvState.lookup w.signals name).bind LVec.toNat?

def timerThree : Option WaitTarget → Bool
  | some (.timer 3) => true
  | _ => false

def refused {α : Type} (m : SvM α) (w : SvWorld) : Bool :=
  match SvM.exec m w with
  | .error _ => true
  | _ => false

def timedDelayReceipt : IO Unit := do
  let text ← IO.FS.readFile "Examples/system-verilog/delay/delay.sv.json"
  let .ok design := loadEnvelopeDesign text
    | throw (IO.userError "delay fixture failed to load")
  let .ok world := elabTimedDesign 4096 design
    | throw (IO.userError "delay fixture failed to elaborate")
  let some afterFirst := worldOf (stepRegion ρ_src 64 .active) world
    | throw (IO.userError "delay process did not suspend")
  let some first := afterFirst.procs[0]?
    | throw (IO.userError "delay process disappeared after suspension")
  unless first.residual.length == 3 &&
      timerThree first.registration &&
      signalValue afterFirst "value" == some 1 do
    throw (IO.userError "delay suspension did not retain the continuation and prior effect")
  let some afterWake := worldOf (do advanceTime 3; wakeTimers) afterFirst
    | throw (IO.userError "delay timer did not wake")
  unless afterWake.regionQ .active == [0] do
    throw (IO.userError "delay wake did not enqueue Active")
  let some afterRun := worldOf (stepRegion ρ_src 64 .active) afterWake
    | throw (IO.userError "delay continuation did not run")
  unless signalValue afterRun "value" == some 2 && afterRun.out.flush == ["PASS"] do
    throw (IO.userError "delay continuation produced the wrong observable result")
  unless match runSelfCheck design 4096 with
    | .unsupported _ => true
    | _ => false do
    throw (IO.userError "time-zero self-check unexpectedly consumed a scheduler delay")
  let zeroText ← IO.FS.readFile "Examples/system-verilog/delay/zero.sv.json"
  let .ok zeroDesign := loadEnvelopeDesign zeroText
    | throw (IO.userError "zero-delay fixture failed to load")
  let .ok zeroWorld := elabTimedDesign 4096 zeroDesign
    | throw (IO.userError "zero-delay fixture failed to elaborate")
  let some afterZero := worldOf (stepRegion ρ_src 64 .active) zeroWorld
    | throw (IO.userError "zero-delay control did not enter Inactive")
  unless afterZero.regionQ .inactive == [0] do
    throw (IO.userError "zero-delay control did not enqueue Inactive")

#eval timedDelayReceipt

end Examples.systemVerilog.delay.proof
