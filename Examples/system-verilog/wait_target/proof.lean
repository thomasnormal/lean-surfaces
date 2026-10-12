import LeanModels.Sv.Slot

namespace Examples.systemVerilog.waitTarget.proof

open LeanModels.Sv
open LeanModels.Sv.SelfCheck

set_option autoImplicit false

def worldOf {α : Type} (m : SvM α) (w : SvWorld) : Option SvWorld :=
  match SvM.exec m w with
  | .ok (.ok _, w') => some w'
  | _ => none

def refused {α : Type} (m : SvM α) (w : SvWorld) : Bool :=
  match SvM.exec m w with
  | .error _ => true
  | _ => false

def edgeWaiting (p : ProcState) : Bool :=
  match p.status with
  | .suspended (.atEdge signal edge) => signal == "clk" && edge == .pos
  | _ => false

def timerWaiting (p : ProcState) : Bool :=
  match p.registration with
  | some (.timer deadline) => deadline == 7
  | _ => false

def edgeWorld : SvWorld :=
  { time := 4
  , procs := #[{ residual := [], status := .suspended (.atEdge "clk" .pos),
                 registration := some (.edge "clk" .pos) }]
  , nba := [("pending", .ofNat 1 1)]
  , regionQ := fun _ => [] }

def timerWorld : SvWorld :=
  { time := 4
  , procs := #[{ residual := [], status := .suspended (.atTime 3),
                 registration := some (.timer 7) }]
  , regionQ := fun _ => [] }

def delayWorld : SvWorld :=
  { time := 4
  , procs := #[{ residual := [.delay 3], status := .ready }]
  , regionQ := fun _ => [] }

def zeroDelayWorld : SvWorld :=
  { procs := #[{ residual := [.delay 0], status := .ready }]
  , regionQ := fun _ => [] }

def readyWorld : SvWorld :=
  { procs := #[{ residual := [], status := .ready }] }

def levelCondition : SExpr := .m0 (.lit (.ofLogic .l1))

def levelWorld : SvWorld :=
  { procs := #[{ residual := [], status := .suspended (.onCond levelCondition),
                 registration := some (.level levelCondition) }] }

def duplicateWorld : SvWorld :=
  { procs := #[{ residual := [], status := .suspended (.atEdge "clk" .pos),
                 registration := some (.edge "clk" .pos), explicitlySuspended := true }] }

#guard (worldOf (suspendProcess 0) edgeWorld).map
  (fun w => (w.procs[0]?).map (fun p => p.explicitlySuspended && w.nba.length == 1)) == some (some true)

#guard (worldOf (do suspendProcess 0; wakeEdges [("clk", .ofNat 1 0)] [("clk", .ofNat 1 1)]) edgeWorld).map
  (fun w => (w.procs[0]?).map (fun p => p.explicitlySuspended && edgeWaiting p)) == some (some true)

#guard (worldOf (do suspendProcess 0; resumeProcess 0) edgeWorld).map
  (fun w => (w.procs[0]?).map (fun p => !p.explicitlySuspended && edgeWaiting p)) == some (some true)

#guard (worldOf (do suspendProcess 0; resumeProcess 0; wakeEdges [("clk", .ofNat 1 0)] [("clk", .ofNat 1 1)]) edgeWorld).map
  (fun w => (w.procs[0]?).map (fun p => match p.status with | .ready => p.registration.isNone && w.regionQ .active == [0] | _ => false)) == some (some true)

#guard (worldOf (do suspendProcess 0; resumeProcess 0) timerWorld).map
  (fun w => (w.procs[0]?).map (fun p => !p.explicitlySuspended && timerWaiting p)) == some (some true)

#guard (worldOf (do suspendProcess 0; resumeProcess 0; advanceTime 3; wakeTimers) timerWorld).map
  (fun w => (w.procs[0]?).map (fun p => match p.status with | .ready => p.registration.isNone && w.regionQ .active == [0] | _ => false)) == some (some true)

#guard (worldOf (do suspendProcess 0; advanceTime 3; wakeTimers) timerWorld).map
  (fun w => (w.procs[0]?).map (fun p => p.explicitlySuspended && timerWaiting p)) == some (some true)

#guard (worldOf (suspendProcess 0) timerWorld).map
  (fun w => (w.procs[0]?).map timerWaiting) == some (some true)

#guard (worldOf (runProcOnce 32 0) delayWorld).map
  (fun w => (w.procs[0]?).map timerWaiting) == some (some true)

#guard refused (runProcOnce 32 0) zeroDelayWorld

#guard refused (suspendProcess 0) readyWorld
#guard refused (suspendProcess 0) levelWorld
#guard refused (suspendProcess 0) duplicateWorld

end Examples.systemVerilog.waitTarget.proof
