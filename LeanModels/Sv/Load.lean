import LeanModels.Sv.Drive

/-!
# R1 inch 4a — waking suspended processes, and loading a `Design`

Gaps that a process-free fixture concealed, closed together because none
is testable without the others.

**`regionQ` was only ever DRAINED** — `stepRegion` reads and clears it and
nothing ever put an index in. `sawEdge`/`wakeEdges` are the missing half
and live in `Slot.lean`, because `runSlots` has to call them and `Drive`
imports `Slot`.

**And `SvWorld` never mentioned `Design`.** `run` is `Design`-indexed;
`runSlots` operated on a world someone hand-built. Until `elabDesign`
exists the adequacy lemma cannot be *stated*, because there is no way to
say "the same design" on both sides.

**Waking was not enough: nothing was ever STARTED.** `stepRegion` reads
`regionQ`; `ProcStatus.ready` is a different notion of readiness and no
rule connected them. A design whose processes were all born `.ready` with
an empty `regionQ` ran nothing at all — so no process ever reached its
`@(posedge clk)`, and a process that is not suspended cannot be woken.
`elabDesign` therefore schedules every process in Active at time 0, and
`runProcOnce` re-enqueues a re-armed one; `stepRegion` drains its queue
*before* the pass rather than clearing it after, so those re-entries are
not thrown away by the pass that caused them. Three edits, one gap: an
`always` block that runs exactly zero times instead of forever.

**And the edge rule was half of §9.4.2.** It woke on `x→1` but not on
`0→x`, while its own docstring claimed unknowns were never edges — three
different rules in one definition. `edgeOn` states the clause: an `x`/`z`
end IS an edge whenever the other end is a level. That is also the rule
`Sem2.isNegedge` already had — and the two are now ONE definition,
`isPosedge`/`isNegedge` in `Basic`, so the tier agrees with itself by
construction rather than by inspection.

## What is deliberately still LOUD

The timed loader admits `always_comb`, `always_latch`, `always_ff`, and single-driver continuous `assign`
through explicit implicit-sensitivity metadata on `ProcState`: each body runs
once in Active at time zero, becomes dormant, and is queued again when a read
signal changes. The legacy `elabDesign`/`runSelfCheck` path remains
initial-only. Multiple continuous drivers stay loud until the scheduler has a
net-driver table and IEEE four-state resolution; a last-writer approximation
would be wrong. Delayed assignments and selected/concatenated targets remain
outside this slice. A comb process that writes one of its own read signals is
not silently treated as an edge wait; the write-name exclusion makes that
self-trigger boundary explicit until the language-level guard is added.

The timed region model still refuses level waits, internally published edge
events, and other scheduler forms outside this slice. The M0 cycle model's
fixpoint semantics remain separate; the timed runner uses the retained
process table and the one Active/Inactive/NBA loop.
-/

namespace LeanModels.Sv

open SelfCheck

set_option autoImplicit false

/-! ## Loading a design -/

/-- One `Design` process as a schedulable `ProcState`.

`always_ff @(posedge clk) body` becomes the residual
`[waitEvent clk .pos, body]` **re-armed to itself** — which is the
defunctionalized reading of `forever { @(posedge clk); body }`: run to the
wait, suspend, and on completion reinstate the whole thing. -/
def procOf : Process → Except String ProcState
  | .alwaysFF clk body =>
      let b : List SStmt := [.waitEvent clk .pos, .m0 body]
      .ok { residual := b, status := .ready, arm := some b }
  | .alwaysPlain clk body =>
      let b : List SStmt := [.waitEvent clk .pos, .m0 body]
      .ok { residual := b, status := .ready, arm := some b }
  | .alwaysComb _ =>
      .error "always_comb: comb sensitivity ('any read signal changed') has no Trigger; the region model needs a settle rule, and approximating it would be wrong"
  | .assign _ _ =>
      .error "continuous assign: timed scheduler required"
  | .unsupported k t =>
      .error s!"out-of-tier process '{k}': {t}"

/-- Build the initial world for a `Design`: declaration-initialised signals
and one `ProcState` per process. Loud on any process the region model
cannot yet schedule.

**Every process is SCHEDULED in Active at time 0**, not merely marked
`.ready`. `stepRegion` reads `regionQ`, never `ProcStatus`, so those are
two different notions of readiness and only one of them runs anything: a
world whose processes are all `.ready` with an empty `regionQ` executes
nothing at all, forever. Scheduling them is also §4.4's own rule — an
`always_ff` starts at time 0, immediately reaches its `@(posedge clk)` and
suspends there, and *that suspension is the only state from which
`wakeEdges` can ever wake it*. -/
def elabDesign (d : Design) : Except String SvWorld := do
  let procs ← d.processes.mapM procOf
  return { signals := initState d
         , procs := procs
         , regionQ := fun r => if r == Region.active then List.range procs.size else [] }

private partial def m0Writes : Stmt → List (Bool × String)
  | .blockingAssign name _ | .nbaAssign name _ => [(false, name)]
  | .ifStmt _ t e => m0Writes t ++ (e.toList.flatMap m0Writes)
  | .block body => body.toList.flatMap m0Writes
  | .unsupported _ _ => []

private def targetWrite : PackedTarget → Bool × String
  | .whole name _ _ | .selected name _ _ _ _ _ => (false, name)

/-- Possible writes and edge sensitivities. This is conservative across
branches: the kernel does not yet publish individual procedural edges. -/
private partial def timedAccesses : SStmt → List (Bool × String)
  | .m0 body => m0Writes body
  | .assign _ name _ | .selectedAssign name _ _ _ _ _ _
  | .selectedNbaAssign name _ _ _ _ _ _ | .localDecl name _ _ _ => [(false, name)]
  -- `$dist_uniform` is an inout call: both the target and the seed are written.
  | .distUniformAssign target seed _ _ _ => [(false, target), (false, seed)]
  | .packedAssign targets _ | .packedNbaAssign targets _ => targets.map targetWrite
  | .scanf _ _ outputs result => (outputs.flatten ++ result).map targetWrite
  | .waitEvent signal _ => [(true, signal)]
  | .ifStmt _ t e => timedAccesses t ++ (e.toList.flatMap timedAccesses)
  | .block body => body.toList.flatMap timedAccesses
  | .forLoop initializers _ steps body =>
      initializers.toList.flatMap timedAccesses ++ steps.toList.flatMap timedAccesses ++
        timedAccesses body
  | .forAfterInit _ steps body | .forHeader _ steps body
  | .forAfterBody _ steps body | .forAfterStep _ steps body =>
      steps.toList.flatMap timedAccesses ++ timedAccesses body
  | .repeatLoop _ _ body | .repeatBody _ body | .repeatAfterBody _ body
  | .doWhileLoop _ body => timedAccesses body
  | .breakLoop | .continueLoop | .sysCall _ _ _ | .strobe _ _ | .severity _ | .fatal _
  | .finish | .skip
  | .delay _ | .waitCond _ => []

/-- Timing controls are illegal inside `always_comb`.  Keep that boundary at
the timed loader rather than letting a suspended comb process become an
unwakeable dormant process. -/
private partial def hasTimingControl : SStmt → Bool
  | .delay _ | .waitEvent _ _ | .waitCond _ => true
  | .m0 _ | .assign _ _ _ | .selectedAssign _ _ _ _ _ _ _
  | .selectedNbaAssign _ _ _ _ _ _ _ | .distUniformAssign _ _ _ _ _
  | .packedAssign _ _ | .packedNbaAssign _ _ | .scanf _ _ _ _
  | .breakLoop | .continueLoop | .localDecl _ _ _ _ | .sysCall _ _ _
  | .strobe _ _ | .severity _ | .fatal _ | .finish | .skip => false
  | .ifStmt _ thenBranch elseBranch =>
      hasTimingControl thenBranch || (elseBranch.map hasTimingControl).getD false
  | .block body => body.toList.any hasTimingControl
  | .forLoop initializers _ steps body =>
      initializers.toList.any hasTimingControl || steps.toList.any hasTimingControl ||
        hasTimingControl body
  | .forAfterInit _ steps body | .forHeader _ steps body
  | .forAfterBody _ steps body | .forAfterStep _ steps body =>
      steps.toList.any hasTimingControl || hasTimingControl body
  | .repeatLoop _ _ body | .repeatBody _ body | .repeatAfterBody _ body
  | .doWhileLoop _ body => hasTimingControl body

/-- An internally written edge source requires the kernel's per-publication
wake rule; external stimulus is currently the only integrated edge source. -/
def requiresInternalEdges (d : SelfCheck.Design) : Bool :=
  let accesses := d.procs.toList.flatMap fun proc =>
    match proc with
    | .initial body | .alwaysBody body | .alwaysImplicit body
    | .alwaysComb body | .alwaysLatch body => timedAccesses body
    | .alwaysPosedge clock body | .alwaysFF clock body => (true, clock) :: timedAccesses body
    | .assign _ _ => []
    | .other _ _ => []
  let writes := accesses.filterMap fun (watched, name) => if watched then none else some name
  accesses.any fun (watched, name) => watched && writes.contains name

/-- Compile one source process to the existing retained statement interface.
Plain `always` owns one loop residual, without an additional rearming carrier. -/
def timedProcOf : SProc → Except String ProcState
  | .initial body =>
      pure { residual := [body], status := .ready }
  | .alwaysBody body =>
      pure { residual := [.forLoop #[] (.m0 (.lit (.ofNat 1 1))) #[] body], status := .ready }
  | .alwaysImplicit body =>
      let writes := SStmt.writeNames body
      let reads := (SStmt.readNames body).eraseDups.filter (fun name => !writes.contains name)
      pure { residual := [body]
           , status := .ready
           , comb := true
           , combReads := reads
           , combBody := [body] }
  | .alwaysComb body =>
      if hasTimingControl body then
        .error "timed design rejects timing control inside always_comb"
      else
        let writes := SStmt.writeNames body
        let reads := (SStmt.readNames body).eraseDups.filter (fun name => !writes.contains name)
        pure { residual := [body]
             , status := .ready
             , comb := true
             , combReads := reads
             , combBody := [body] }
  | .alwaysLatch body =>
      if hasTimingControl body then
        .error "timed design rejects timing control inside always_latch"
      else
        let writes := SStmt.writeNames body
        let reads := (SStmt.readNames body).eraseDups.filter (fun name => !writes.contains name)
        pure { residual := [body]
             , status := .ready
             , comb := true
             , combReads := reads
             , combBody := [body] }
  | .assign target value =>
      let body := .assign false target value
      pure { residual := [body]
           , status := .ready
           , comb := true
           , combReads := value.readNames.eraseDups
           , combBody := [body] }
  | .alwaysPosedge clock body | .alwaysFF clock body =>
      let residual := [.waitEvent clock .pos, body]
      pure { residual, status := .ready, arm := some residual }
  | .other kind _ => .error s!"timed design rejects process kind '{kind}'"

/-- Build a scheduler world from the self-check envelope vocabulary.

This surface admits `initial`, plain `always`, `always_comb`, `always_latch`,
`always_ff`, single-driver continuous `assign`, and canonical positive-edge
processes. Their continuations run through the existing
scheduler with an explicit region oracle. Time is measured in that
module's time-unit ticks; physical unit conversion is not inferred.
`runSelfCheck` remains time-zero-only and continues to refuse timing nodes. -/
def elabTimedDesign (fuel : Nat) (d : SelfCheck.Design) : Except String SvWorld := do
  if d.requiresTimeZero then
    throw "timed design rejects time-zero-only $time lowering"
  let assignTargets := d.procs.toList.filterMap fun proc =>
    match proc with
    | .assign target _ => some target
    | _ => none
  if assignTargets.eraseDups.length != assignTargets.length then
    throw "continuous assign: multiple drivers require net resolution"
  for target in assignTargets do
    match d.decls.toList.find? (fun decl => decl.name == target) with
    | none => throw s!"continuous assign target '{target}' is undeclared"
    | some decl =>
        if !decl.isNet && !decl.isOutput then
          throw s!"continuous assign target '{target}' is not a net"
  let procs ← d.procs.toList.mapM timedProcOf
  if procs.isEmpty then
    .error "timed design requires at least one procedural process"
  let signals ← match SelfCheck.initDecls fuel d.decls.toList [] with
    | .ok signals => pure signals
    | .timeout => .error "timed design declaration initialization exhausted fuel"
    | .unsupported msg => .error s!"timed design declaration initialization: {msg}"
  let procs := procs.toArray
  return { signals := signals
         , procs := procs
         , regionQ := fun r => if r == Region.active then List.range procs.size else [] }

/-- A time-zero approximation cannot enter the timed executor at any fuel. -/
theorem elabTimedDesign_requiresTimeZero (fuel : Nat) (d : SelfCheck.Design)
    (restricted : d.requiresTimeZero = true) :
    elabTimedDesign fuel d = .error "timed design rejects time-zero-only $time lowering" := by
  simp [elabTimedDesign, restricted]
  rfl

/-! ## Guards -/

section Guards

/-- `always_ff @(posedge clk) n = 1;` — one process, one clock. -/
private def ffDesign : Design :=
  { name := "ff"
  , decls := #[{ name := "clk", width := 1, isInput := true },
               { name := "n", width := 4 }]
  , processes := #[.alwaysFF "clk" (.blockingAssign "n" (.lit (LVec.ofNat 4 1)))] }

-- an always_ff design LOADS, and its process is armed
#guard (elabDesign ffDesign).toOption.isSome
#guard ((elabDesign ffDesign).toOption.map (fun w => w.procs.size)) == some 1
#guard ((elabDesign ffDesign).toOption.bind (fun w => (w.procs[0]?).map (·.arm.isSome))) == some true

-- the legacy self-check loader still keeps always_comb loud
#guard (elabDesign { name := "c", decls := #[], processes := #[.alwaysComb (.blockingAssign "y" (.ident "a"))] }).toOption.isNone

/-! **THE RE-ARM GUARD.** Two posedges, and the process is still alive after
the second — it re-armed rather than finishing. Before `ProcState.arm` this
process was marked `.finished` after its first body completed and every
later slot silently did nothing: a SHORTER TRACE, not an error. -/
private def ffWorld : SvWorld := (elabDesign ffDesign).toOption.getD {}

private def clkStim : List SvState :=
  [[("clk", LVec.ofNat 1 0)], [("clk", LVec.ofNat 1 1)],
   [("clk", LVec.ofNat 1 0)], [("clk", LVec.ofNat 1 1)]]

/-- Run to completion and keep BOTH halves. `Drive`'s own `traceOf` is
`private` to that module, so it is not in scope here; and the re-arm guard
needs the final world, not just the trace. -/
private def runOn (m : SvM RegionTrace) (w : SvWorld) : Option (RegionTrace × SvWorld) :=
  match SvM.exec m w with
  | .ok (.ok tr, w') => some (tr, w')
  | _ => none

private def isFinished (p : ProcState) : Bool :=
  match p.status with
  | .finished => true
  | _ => false

private def isWaitingOnEdge (p : ProcState) : Bool :=
  match p.status with
  | .suspended (.atEdge _ _) => true
  | _ => false

private def ran : Option (RegionTrace × SvWorld) := runOn (runSlots ρ_src 256 clkStim) ffWorld

-- the driver produces one slot per stimulus entry over a REAL loaded design
#guard (ran.map (·.1.length)) == some 4

-- the body DID run: `n` was assigned by the always block. This is the guard
-- that fails if the process is loaded but never scheduled — `n` stays `x`
-- and `toNat?` is `none`, not `some 1`.
#guard (ran.bind (fun r => (SvState.lookup r.2.signals "n").bind LVec.toNat?)) == some 1

-- and the process is NOT finished after two posedges: it re-armed
#guard (ran.bind (fun r => (r.2.procs[0]?).map isFinished)) == some false

-- ... and it is back to WAITING on its clock edge, which is what re-arming
-- MEANS. Checked separately because a process that never ran at all would
-- also be "not finished" — that is a vacuous pass, and it is the exact
-- shape the process-free fixture kept producing.
#guard (ran.bind (fun r => (r.2.procs[0]?).map isWaitingOnEdge)) == some true

/-! **§9.4.2 edge detection.** An `x`/`z` end is an edge whenever the OTHER
end is a level — leaving a known 0 and arriving at a known 1 are both
posedges. Only `x→z`/`z→x` and a value against itself are edgeless. -/
#guard sawEdge [("c", LVec.ofNat 1 0)] [("c", LVec.ofNat 1 1)] "c" .pos == true
#guard sawEdge [("c", LVec.xVec 1)]    [("c", LVec.ofNat 1 1)] "c" .pos == true
#guard sawEdge [("c", LVec.ofNat 1 0)] [("c", LVec.xVec 1)]    "c" .pos == true
#guard sawEdge [("c", LVec.ofNat 1 1)] [("c", LVec.ofNat 1 1)] "c" .pos == false
#guard sawEdge [("c", LVec.xVec 1)]    [("c", LVec.xVec 1)]    "c" .pos == false
-- a falling clock is a negedge and NOT a posedge — the rule is directional
#guard sawEdge [("c", LVec.ofNat 1 1)] [("c", LVec.ofNat 1 0)] "c" .pos == false
#guard sawEdge [("c", LVec.ofNat 1 1)] [("c", LVec.ofNat 1 0)] "c" .neg == true
-- ... and the negedge half is the exact mirror (`Basic.isNegedge`, the
-- same definition the M1 reset phase reads)
#guard sawEdge [("c", LVec.ofNat 1 1)] [("c", LVec.xVec 1)]    "c" .neg == true
#guard sawEdge [("c", LVec.xVec 1)]    [("c", LVec.ofNat 1 0)] "c" .neg == true
-- x -> z is NOT an edge in either direction: neither end is a level
#guard sawEdge [("c", LVec.xVec 1)] [("c", LVec.replicate 1 .lz)] "c" .pos == false
#guard sawEdge [("c", LVec.xVec 1)] [("c", LVec.replicate 1 .lz)] "c" .neg == false
-- an undeclared signal reads x against x, so it can never wake anything
#guard sawEdge [] [("c", LVec.ofNat 1 1)] "nosuch" .pos == false

end Guards

end LeanModels.Sv
