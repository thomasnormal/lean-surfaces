import LeanModels.Sv.Prim
import LeanModels.Sv.Step

/-!
# R1 inch 4a — `slotStep`, the Active/Inactive/NBA region loop

One IEEE 1800 §4.4 time slot, written against the `SvM` primitives rather
than against hand-threaded state. This is the loop the primitive layer
existed to make cheap.

## The three regions this inch implements, and the loop between them

`Active` → `Inactive` → `NBA`, **iterating rather than falling through**:
work scheduled into Active by an NBA commit re-enters Active, and the slot
does not close until all three are empty. That iteration is the part a
naive "one pass per region" model gets wrong, and it is why `slotStep` is
a recursion and not a sequence.

The reactive family (`Observed`, `Reactive`, `Re-Inactive`, `Re-NBA`) and
`Preponed`/`Postponed` are NOT implemented here. They are named in
`Region` already, so adding them changes no type — which was the whole
point of carrying all fifteen constructors from day one.

## Fuel is SEMANTIC here, not an artifact

`Res.timeout` in this tier means **non-convergence**: a combinational loop
today, and at this inch also a zero-delay loop that never lets the slot
close. Both are real, reportable properties of the design under test, so
the loop is fuel-bounded and exhaustion surfaces as Core's `exhausted`
(`Loud.timeout`) rather than being excluded by a termination argument.

## `Res` is retained as a VIEW

`stepSStmts` is a pure `Res`-valued function and stays one; `liftRes`
carries its three outcomes into `SvM`. That is what lets the existing
fuel-monotonicity ladder keep working unchanged — the stepper is not
rewritten into the monad, it is *lifted at the boundary*.
-/

namespace LeanModels.Sv

open SelfCheck

set_option autoImplicit false

/-! ## The view bridge -/

/-- Carry a pure `Res` result into `SvM`.

The three outcomes map onto three different layers, and the mapping is the
tier's outcome covenant restated on the substrate: a value is a value; a
`timeout` is Core's `exhausted`, i.e. `Loud.timeout` at the BASE, which
discards the world because a non-converging run has no meaningful state to
report; an `unsupported` is a classified refusal carrying the clause it
refused under. -/
def liftRes {α : Type} (c : SvClause) : Res α → SvM α
  | .ok a => pure a
  | .timeout => exhausted
  | .unsupported m => refuseSv .outOfTier c m

/-! ## Stepping one process -/

/-- Edge triggers retain their complete target even in legacy process states.
A relative timer alone cannot recover its original registration time. -/
def targetOf (ps : ProcState) : Option WaitTarget :=
  match ps.registration with
  | some target => some target
  | none =>
      match ps.status with
      | .suspended (.atEdge signal edgeKind) => some (.edge signal edgeKind)
      | .suspended (.onCond condition) => some (.level condition)
      | _ => none

def withoutIndex (index : Nat) (xs : List Nat) : List Nat :=
  xs.filter (fun other => other != index)

def removeFromReady (w : SvWorld) (index : Nat) : SvWorld :=
  { w with regionQ := fun r => withoutIndex index (w.regionQ r) }

def signalChanged (old new : SvState) (name : String) : Bool :=
  SvState.lookup old name != SvState.lookup new name

/-! ## Continuous-driver resolution -/

/-- Strength-free ordinary-net resolution for one bit.  An un-driven or
all-high-impedance bit is `z`; equal known drivers preserve their value; an
`x` or a disagreement among known drivers yields `x`. -/
def resolveDriverBit (bits : List Logic) : Logic :=
  let active := bits.filter (fun bit => bit != .lz)
  if active.isEmpty then
    .lz
  else if active.any (fun bit => bit == .lx) then
    .lx
  else
    match active with
    | [] => .lz
    | bit :: rest => if rest.all (fun other => other == bit) then bit else .lx

/-- Resolve sampled driver vectors bit by bit.  Every value is already sized
by the frontend's declaration conversion, so this function only combines
corresponding positions. -/
def resolveDriverVec (width : Nat) (values : List LVec) : LVec :=
  ⟨Array.ofFn (n := width) fun index =>
    resolveDriverBit (values.filterMap fun value => value.bits[index.val]?)⟩

/-- Sampled values for all continuous drivers of one target. -/
def driverValues (w : SvWorld) (target : String) : List LVec :=
  (List.range w.procs.size).filterMap fun index =>
    match w.procs[index]? with
    | some ps =>
        if ps.driverTarget == some target then
          match w.drivers[index]? with
          | some (some value) => some value
          | _ => none
        else none
    | none => none

/-- Replace one driver's sample and publish the resolved target value. -/
def publishDriver (w : SvWorld) (index : Nat) (target : String)
    (value : LVec) : SvWorld :=
  let drivers := w.drivers.set! index (some value)
  let values := driverValues { w with drivers := drivers } target
  let width := Option.getD ((SvState.lookup w.signals target).map LVec.width) value.width
  { w with drivers := drivers
         , signals := SvState.set w.signals target (resolveDriverVec width values) }

/-- Apply a stepped process result, routing continuous assignments through the
driver table while leaving ordinary procedural writes untouched. -/
def publishStep (w : SvWorld) (index : Nat) (ps : ProcState)
    (signals : SvState) (nba : NbaQueue) (out : Out) : SvWorld :=
  let base := { w with signals := signals, nba := nba, out := out }
  match ps.driverTarget with
  | some target =>
      match SvState.lookup signals target with
      | some value => publishDriver base index target value
      | none => base
  | none => base

def appendActive (w : SvWorld) (indices : List Nat) : SvWorld :=
  { w with regionQ := fun r =>
      if r == Region.active then w.regionQ r ++ indices else w.regionQ r }

/-- Wake dormant `always_comb` processes whose inferred sensitivity contains a
signal that changed.  The process is queued in Active; changes made by one
comb process therefore trigger dependent comb processes in the same slot. -/
def wakeCombs (old new : SvState) : SvM Unit :=
  modify fun w =>
    let woken : List Nat :=
      (List.range w.procs.size).filter fun i =>
        match w.procs[i]? with
        | some ps => ps.comb && ps.status == .dormant &&
            ps.combReads.any (signalChanged old new)
        | none => false
    let procs' := woken.foldl (fun (ps : Array ProcState) i =>
      match ps[i]? with
      | some p => ps.set! i { p with status := .ready }
      | none => ps) w.procs
    { w with procs := procs'
           , regionQ := fun r =>
               if r == Region.active then w.regionQ r ++ woken else w.regionQ r }

/-- Wake level-sensitive `wait (condition)` continuations after a relevant
signal publication.  The condition itself is sampled by the retained
stepper, so a false re-check simply suspends the process again.  Filtering
by the condition's static read set avoids spurious scheduler work while
preserving the IEEE rule that a wait is re-evaluated after updates to a
signal it reads. -/
def wakeLevels (old new : SvState) : SvM Unit :=
  modify fun w =>
    let woken : List Nat :=
      (List.range w.procs.size).filter fun i =>
        match w.procs[i]? with
        | some ps =>
            match ps.status, targetOf ps with
            | .suspended (.onCond condition), some (.level _) =>
                !ps.explicitlySuspended &&
                  (SExpr.readNames condition).any (signalChanged old new)
            | _, _ => false
        | none => false
    let procs' := woken.foldl (fun (ps : Array ProcState) i =>
      match ps[i]? with
      | some p => ps.set! i { p with status := .ready, registration := none }
      | none => ps) w.procs
    appendActive { w with procs := procs' } woken

/-! ## Edge detection and waking -/

/-- §9.4.2 edge on a 1-bit value.  The shared `Basic` predicates include
the IEEE x/z transitions; this selector supplies the process-level `Edge`
case. -/
def edgeOn (e : Edge) (old new : Logic) : Bool :=
  match e with
  | .pos => isPosedge old new
  | .neg => isNegedge old new
  | .any => old != new

/-- Did `sig` see the given edge between `old` and `new`? -/
def sawEdge (old new : SvState) (sig : String) (e : Edge) : Bool :=
  edgeOn e (SvState.bit0 old sig) (SvState.bit0 new sig)

/-- Evaluate the retained `iff` guard at the state in which its event was
published.  The extractor admits only scalar identifier guards for this
slice; any other expression is deliberately false here and is rejected by
the envelope admission path rather than approximated. -/
def eventGuardPass (st : SvState) : Option SExpr → Bool
  | none => true
  | some (.m0 (.ident signal)) => SvState.bit0 st signal == .l1
  | some _ => false

/-- Whether one guarded event-list entry both changed and passed its filter. -/
def eventTriggered (old new : SvState)
    (events : List (String × Edge × Option SExpr)) : Bool :=
  events.any fun (signal, edge, guard) =>
    sawEdge old new signal edge && eventGuardPass new guard

def appendInactive (w : SvWorld) (indices : List Nat) : SvWorld :=
  { w with regionQ := fun r =>
      if r == Region.inactive then w.regionQ r ++ indices else w.regionQ r }

/-- Wake every process whose edge trigger fired between `old` and `new`,
marking it ready and enqueueing it in Active. -/
def wakeEdges (old new : SvState) : SvM Unit :=
  modify fun w =>
    let triggered : List Nat :=
      (List.range w.procs.size).filter fun i =>
        match w.procs[i]? with
        | some ps =>
            match targetOf ps with
            | some (.edge sig e) =>
                !ps.explicitlySuspended &&
                  (sawEdge old new sig e ||
                    ps.resetTarget.any (fun reset => sawEdge old new reset ps.resetEdge)) &&
                  (match ps.status with
                   | .suspended _ | .ready => true
                   | _ => false)
            | some (.edges events) =>
                !ps.explicitlySuspended &&
                  eventTriggered old new
                    (if ps.eventGuards.isEmpty
                     then events.map fun (sig, edge) => (sig, edge, none)
                     else ps.eventGuards) &&
                  (match ps.status with
                   | .suspended _ | .ready => true
                   | _ => false)
            | _ => false
        | none => false
    let woken := triggered.filter fun i =>
      match w.procs[i]? with
      | some ps => match ps.status with
          | .suspended _ => true
          | _ => false
      | none => false
    let procs' := triggered.foldl (fun (ps : Array ProcState) i =>
        match ps[i]? with
        | some p =>
            ps.set! i { p with status := .ready
                              , pendingEdges := p.pendingEdges + 1 }
        | none => ps) w.procs
    appendActive { w with procs := procs' } woken

/-- Run process `i`'s residual until it completes or suspends, and write
the result back into the world.

The residual IS the continuation (`Step.lean`): on suspension we store
what is left and the trigger that will wake it; on completion we store the
empty residual and mark it finished. -/
partial def runProcResidual (fuel : Nat) (i : Nat) (ps : ProcState)
    (residual : List SStmt) : SvM StepOutcome :=
  match fuel with
  | 0 => exhausted
  | fuel + 1 => do
      let w ← get
      match residual with
      | [] =>
          let (ps', reArmed) :=
            if ps.comb then
              ({ ps with residual := ps.combBody
                       , status := .dormant
                       , registration := none
                       , explicitlySuspended := false }, false)
            else match ps.arm with
              | some body =>
                  if !ps.eventEdges.isEmpty then
                    if ps.pendingEdges > 1 then
                      ({ ps with residual := body
                               , status := .ready
                               , registration := none
                               , explicitlySuspended := false
                               , pendingEdges := ps.pendingEdges - 1 }, true)
                    else
                      let trigger := match ps.eventEdges with
                        | (signal, edge) :: _ => Trigger.atEdge signal edge
                        | [] => Trigger.atEdge "" .any
                      ({ ps with residual := body
                               , status := .suspended trigger
                               , registration := some (.edges ps.eventEdges)
                               , explicitlySuspended := false
                               , pendingEdges := 0 }, false)
                  else if ps.pendingEdges > 1 then
                    ({ ps with residual := body.drop 1
                             , status := .ready
                             , registration := none
                             , explicitlySuspended := false
                             , pendingEdges := ps.pendingEdges - 1 }, true)
                  else
                    ({ ps with residual := body
                             , status := .ready
                             , registration := none
                             , explicitlySuspended := false
                             , pendingEdges := 0 }, true)
              | none =>
                  ({ ps with residual := []
                           , status := .finished
                           , registration := none
                           , explicitlySuspended := false
                           , pendingEdges := 0 }, false)
          set { w with procs := w.procs.set! i ps'
                       , regionQ := fun r =>
                           if reArmed && r == Region.active then w.regionQ r ++ [i]
                           else w.regionQ r }
          pure .done
      | .block body :: rest =>
          -- Preserve the scheduler's publication point between statements
          -- in a process block.  `stepSStmt` deliberately treats a block as
          -- one pure step for the legacy runner; the retained timed process
          -- instead exposes each statement to the same wake path so two
          -- blocking writes in one active process can produce two edges.
          runProcResidual fuel i ps (body.toList ++ rest)
      | stmt :: rest =>
          let (sigs, nba, out, oc) ←
            liftRes ⟨"4.4"⟩ (stepSStmt fuel w.signals w.nba w.out stmt)
          match oc with
          | .suspended (.atTime 0) tail =>
              let continuation := tail ++ rest
              let ps' := { ps with residual := continuation
                                  , status := .ready
                                  , registration := none
                                  , explicitlySuspended := false }
              let updated := publishStep w i ps sigs nba out
              let updated := { updated with procs := updated.procs.set! i ps' }
              set (appendInactive updated [i])
              if w.signals != updated.signals then
                wakeCombs w.signals updated.signals
                wakeLevels w.signals updated.signals
                wakeEdges w.signals updated.signals
              pure (.suspended (.atTime 0) continuation)
          | .suspended t continuation =>
              let ps' := { ps with residual := continuation ++ rest
                                  , status := .suspended t
                                  , registration := some (WaitTarget.ofTrigger w.time t) }
              let updated := publishStep w i ps sigs nba out
              set { updated with procs := updated.procs.set! i ps' }
              if w.signals != updated.signals then
                wakeCombs w.signals updated.signals
                wakeLevels w.signals updated.signals
                wakeEdges w.signals updated.signals
              pure (.suspended t (continuation ++ rest))
          | .done =>
              let ps' := { ps with residual := rest
                                  , status := .ready
                                  , registration := none
                                  , explicitlySuspended := false }
              let updated := publishStep w i ps sigs nba out
              set { updated with procs := updated.procs.set! i ps' }
              if w.signals != updated.signals then
                wakeCombs w.signals updated.signals
                wakeLevels w.signals updated.signals
                wakeEdges w.signals updated.signals
              runProcResidual fuel i ps' rest

def runProcOnce (fuel : Nat) (i : Nat) : SvM StepOutcome := do
  let w ← get
  match w.procs[i]? with
  | none => refuseSv .outOfTier ⟨"4.4"⟩ s!"no process at index {i}"
  | some ps =>
      if ps.explicitlySuspended then
        refuseSv .outOfTier ⟨"9.7"⟩ "explicitly suspended process is not runnable"
      else
        runProcResidual fuel i ps ps.residual

/-! ## One region's pass -/

/-- Run every process ready in region `r`, **in the order the oracle
chooses**, and clear the region's ready set. Returns whether anything ran.

`σ.choose` is consulted once per pass and the invocation counter advances,
so two schedules that differ only in this region produce different orders
— which is exactly the freedom IEEE 1800 §4.7 grants and the tier's `∀ σ`
quantifies over. The region ORDER is not the oracle's to choose; only the
order within one region is. -/
def stepRegion (σ : RegionOracle) (fuel : Nat) (r : Region) : SvM Bool := do
  let w ← get
  let ready := σ.choose w.k r (w.regionQ r)
  -- DRAIN BEFORE RUNNING, not after. Clearing the queue at the END of the
  -- pass discards everything scheduled INTO this region *during* it — which
  -- is exactly what a re-arming `always` process does when its body
  -- completes. Draining first makes the region's queue mean "work still
  -- owed", so the pass's own additions survive into `slotStep`'s next
  -- iteration, which is the §4.4 rule this module's docstring already
  -- claims ("work scheduled into Active by an NBA commit re-enters Active").
  set { w with k := w.k + 1, curRegion := r
             , regionQ := fun r' => if r' == r then [] else w.regionQ r' }
  match ready with
  | [] => pure false
  | _ =>
      for i in ready do
        let _ ← runProcOnce fuel i
      pure true

/-- Deliver delay registrations whose absolute deadline has arrived.

An explicitly suspended timer remains registered but is not delivered.  This
is the waiting-target rule: advancing time does not erase the deadline, and
resumption can deliver an already-due timer in the current Active step. -/
def wakeTimers : SvM Unit :=
  modify fun w =>
    let woken : List Nat :=
      (List.range w.procs.size).filter fun i =>
        match w.procs[i]? with
        | some ps =>
            match ps.status, targetOf ps with
            | .suspended (.atTime (_ + 1)), some (.timer deadline) =>
                !ps.explicitlySuspended && deadline ≤ w.time
            | _, _ => false
        | none => false
    let procs' := woken.foldl (fun (ps : Array ProcState) i =>
        match ps[i]? with
        | some p => ps.set! i { p with status := .ready, registration := none }
        | none => ps) w.procs
    appendActive { w with procs := procs' } woken

/-- Suspend a process only while it is parked on a fixed edge or timer.

The ready-process, level-wait, terminal, and duplicate-suspension cases are
deliberately loud until their IEEE 9.7 rules are independently modelled. -/
def suspendProcess (index : Nat) : SvM Unit := do
  let w ← get
  match w.procs[index]? with
  | none => refuseSv .outOfTier ⟨"9.7"⟩ s!"no process at index {index}"
  | some ps =>
      if ps.explicitlySuspended then
        refuseSv .outOfTier ⟨"9.7"⟩ "process is already explicitly suspended"
      else
        match ps.status, targetOf ps with
        | .suspended _, some target@(.edge _ _)
        | .suspended (.atTime (_ + 1)), some target@(.timer _) =>
            let ps' := { ps with registration := some target, explicitlySuspended := true }
            set (removeFromReady { w with procs := w.procs.set! index ps' } index)
        | .suspended _, some (.level _) =>
            refuseSv .outOfTier ⟨"9.7"⟩ "level-wait re-entry is not admitted"
        | .ready, _ =>
            refuseSv .outOfTier ⟨"9.7"⟩ "ready-process suspension is not admitted"
        | .finished, _ =>
            refuseSv .outOfTier ⟨"9.7"⟩ "terminal-process suspension is not admitted"
        | _, _ =>
            refuseSv .outOfTier ⟨"9.7"⟩ "process has no admitted waiting target"

/-- Resume an explicitly suspended edge/timer waiter.

Edge waits are re-sensitized without latching an event that occurred while
suspended. A timer whose original deadline is due enters Active immediately;
otherwise its absolute deadline remains unchanged. -/
def resumeProcess (index : Nat) : SvM Unit := do
  let w ← get
  match w.procs[index]? with
  | none => refuseSv .outOfTier ⟨"9.7"⟩ s!"no process at index {index}"
  | some ps =>
      if !ps.explicitlySuspended then
        refuseSv .outOfTier ⟨"9.7"⟩ "process is not explicitly suspended"
      else
        match ps.status, ps.registration with
        | .suspended _, some (.edge _ _) =>
            set { w with procs := w.procs.set! index ({ ps with explicitlySuspended := false }) }
        | .suspended (.atTime (_ + 1)), some (.timer deadline) =>
            if deadline ≤ w.time then
              let ps' := { ps with status := .ready, registration := none, explicitlySuspended := false }
              set (appendActive { w with procs := w.procs.set! index ps' } [index])
            else
              set { w with procs := w.procs.set! index ({ ps with explicitlySuspended := false }) }
        | .suspended _, some (.level _) =>
            refuseSv .outOfTier ⟨"9.7"⟩ "level-wait re-entry is not admitted"
        | _, _ =>
            refuseSv .outOfTier ⟨"9.7"⟩ "resume target is not an admitted waiter"

/-! ## Postponed output -/

/-- Flush monitor samples before the output work queued by `$strobe` after the
Active/Inactive/NBA loop has closed.  Both operations evaluate against the
final signal state and preserve `$finish`'s state-preserving halt.  This is
the one postponed-region implementation for the legacy self-check runner and
the timed scheduler. -/
def flushPostponed (fuel : Nat) : SvM Unit := do
  let w ← get
  let (signals, out) ← liftRes ⟨"21.2"⟩ (flushMonitor fuel w.signals w.out)
  let (signals, out) ← liftRes ⟨"21.2"⟩ (flushStrobes fuel signals out)
  set { w with signals := signals, out := out, curRegion := Region.postponed }

/-! ## The slot -/

/-- One time slot: Active, then Inactive, then the NBA commit, **looping**
until all three are exhausted.

Reading the recursion is reading §4.4's iteration rule: any region that
did work sends us back to Active, because Active is where that work lands.
Only when Active is empty, Inactive is empty, and the NBA buffer is empty
does the slot close. -/
def slotStep (σ : RegionOracle) : Nat → SvM Unit
  | 0 => exhausted
  | fuel + 1 => do
      if (← stepRegion σ fuel .active) then
        slotStep σ fuel
      else if (← stepRegion σ fuel .inactive) then
        slotStep σ fuel
      else do
        let w ← get
        if w.nba.isEmpty then
          flushPostponed fuel
        else do
          let before ← get
          applyNba
          let after ← get
          if before.signals != after.signals then
            wakeCombs before.signals after.signals
            wakeLevels before.signals after.signals
            wakeEdges before.signals after.signals
          slotStep σ fuel

end LeanModels.Sv
