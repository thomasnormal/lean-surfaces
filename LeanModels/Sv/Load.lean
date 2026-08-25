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
`Sem2.isNegedge` already had, so the tier now agrees with itself.

## What is deliberately still LOUD

`always_comb` and continuous `assign` are **refused**, not approximated.
Their sensitivity is *"any signal the body reads changed"*, and `Trigger`
offers `atTime`, `atEdge` and `onCond` — none of which expresses it. The
M0 cycle model handles them by running to a fixpoint (`combSettle`); the
region model would need the same, and inventing a wrong trigger to make
them load would be worse than refusing. Named here, priced, and NOT
modelled.

That means designs containing `always_comb` — including the `adder`
gallery example — do not load yet, while `always_ff` designs do. The
corpus census says which order is right: `initial` is 98.8% of the anchor
corpus and `always_*` about 1% each.
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
      .error "continuous assign: same comb-sensitivity gap as always_comb"
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

-- always_comb is LOUD rather than approximated
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
-- ... and the negedge half is the exact mirror (this is `Sem2.isNegedge`)
#guard sawEdge [("c", LVec.ofNat 1 1)] [("c", LVec.xVec 1)]    "c" .neg == true
#guard sawEdge [("c", LVec.xVec 1)]    [("c", LVec.ofNat 1 0)] "c" .neg == true
-- x -> z is NOT an edge in either direction: neither end is a level
#guard sawEdge [("c", LVec.xVec 1)] [("c", LVec.replicate 1 .lz)] "c" .pos == false
#guard sawEdge [("c", LVec.xVec 1)] [("c", LVec.replicate 1 .lz)] "c" .neg == false
-- an undeclared signal reads x against x, so it can never wake anything
#guard sawEdge [] [("c", LVec.ofNat 1 1)] "nosuch" .pos == false

end Guards

end LeanModels.Sv
