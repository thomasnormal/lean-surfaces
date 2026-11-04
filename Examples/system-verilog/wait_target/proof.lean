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

def edgeRegistered (p : ProcState) : Bool :=
  match p.registration with
  | some (.edge signal edge) => signal == "clk" && edge == .pos
  | _ => false

def continuationPreserved (before after : SvWorld) : Bool :=
  match before.procs[0]?, after.procs[0]? with
  | some p0, some p1 =>
      p0.residual == p1.residual && p0.arm == p1.arm
  | _, _ => false

def worldFramePreserved (before after : SvWorld) : Bool :=
  before.time == after.time && before.signals == after.signals &&
    before.nba == after.nba && before.reNba == after.reNba &&
    before.future == after.future && before.out == after.out &&
    before.curRegion == after.curRegion && before.k == after.k

def edgeWorld : SvWorld :=
  { time := 4
  , procs := #[{ residual := [.skip, .waitEvent "clk" .neg]
               , arm := some [.waitEvent "clk" .pos]
               , status := .suspended (.atEdge "clk" .pos),
                 registration := some (.edge "clk" .pos) }]
  , nba := [("pending", .ofNat 1 1)]
  , out := { lines := #["prior"], cur := "tail" }
  , regionQ := fun _ => [] }

def timerWorld : SvWorld :=
  { time := 4
  , procs := #[{ residual := [.skip], status := .suspended (.atTime 3),
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
  (fun w => (w.procs[0]?).map
    (fun p => p.explicitlySuspended &&
      p.residual == [.skip, .waitEvent "clk" .neg] &&
      edgeRegistered p && w.nba == [("pending", .ofNat 1 1)] &&
      w.out.lines == #["prior"] && w.out.cur == "tail" &&
      w.regionQ .active == []))
  == some (some true)

#guard (worldOf (suspendProcess 0) edgeWorld).map
  (worldFramePreserved edgeWorld) == some true

#guard (worldOf (suspendProcess 0) edgeWorld).map
  (continuationPreserved edgeWorld) == some true

#guard (worldOf (suspendProcess 0) timerWorld).map
  (worldFramePreserved timerWorld) == some true

#guard (worldOf (do suspendProcess 0; wakeEdges [("clk", .ofNat 1 0)] [("clk", .ofNat 1 1)]) edgeWorld).map
  (fun w => (w.procs[0]?).map
    (fun p => p.explicitlySuspended && p.residual == [.skip, .waitEvent "clk" .neg] &&
      edgeRegistered p && edgeWaiting p && w.regionQ .active == []))
  == some (some true)

#guard (worldOf (do suspendProcess 0; resumeProcess 0) edgeWorld).map
  (fun w => (w.procs[0]?).map
    (fun p => !p.explicitlySuspended && edgeWaiting p && edgeRegistered p &&
      p.residual == [.skip, .waitEvent "clk" .neg] && w.regionQ .active == []))
  == some (some true)

#guard (worldOf (do suspendProcess 0; resumeProcess 0; wakeEdges [("clk", .ofNat 1 0)] [("clk", .ofNat 1 1)]) edgeWorld).map
  (fun w => (w.procs[0]?).map (fun p => match p.status with | .ready => edgeRegistered p && w.regionQ .active == [0] | _ => false)) == some (some true)

#guard (worldOf (do suspendProcess 0; resumeProcess 0) timerWorld).map
  (fun w => (w.procs[0]?).map (fun p => !p.explicitlySuspended && timerWaiting p)) == some (some true)

#guard (worldOf (do suspendProcess 0; advanceTime 3; wakeTimers) timerWorld).map
  (continuationPreserved timerWorld) == some true

#guard (worldOf (do suspendProcess 0; resumeProcess 0; advanceTime 3; wakeTimers) timerWorld).map
  (fun w => (w.procs[0]?).map (fun p => match p.status with | .ready => p.registration.isNone && w.regionQ .active == [0] | _ => false)) == some (some true)

#guard (worldOf (do suspendProcess 0; advanceTime 3; resumeProcess 0) timerWorld).map
  (fun w => (w.procs[0]?).map (fun p =>
    match p.status with
    | .ready => p.registration.isNone && p.residual == [.skip] && w.regionQ .active == [0]
    | _ => false))
  == some (some true)

#guard (worldOf (do suspendProcess 0; advanceTime 4; resumeProcess 0) timerWorld).map
  (fun w => (w.procs[0]?).map (fun p =>
    match p.status with
    | .ready => p.registration.isNone && p.residual == [.skip] && w.regionQ .active == [0]
    | _ => false))
  == some (some true)

#guard (worldOf (do suspendProcess 0; advanceTime 3; wakeTimers) timerWorld).map
  (fun w => (w.procs[0]?).map (fun p => p.explicitlySuspended && timerWaiting p)) == some (some true)

#guard (worldOf (suspendProcess 0) timerWorld).map
  (fun w => (w.procs[0]?).map (fun p => timerWaiting p && p.residual == [.skip])) == some (some true)

#guard (worldOf (runProcOnce 32 0) delayWorld).map
  (fun w => (w.procs[0]?).map timerWaiting) == some (some true)

#guard (worldOf (runProcOnce 32 0) zeroDelayWorld).map
  (fun w => w.regionQ .inactive == [0]) == some true

#guard refused (suspendProcess 0) readyWorld
#guard refused (suspendProcess 0) levelWorld
#guard refused (suspendProcess 0) duplicateWorld
#guard refused (resumeProcess 0) readyWorld
#guard refused (resumeProcess 0) levelWorld
#guard refused (do suspendProcess 0; resumeProcess 0; resumeProcess 0) edgeWorld

end Examples.systemVerilog.waitTarget.proof
