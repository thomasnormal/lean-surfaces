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

/-- Run process `i`'s residual until it completes or suspends, and write
the result back into the world.

The residual IS the continuation (`Step.lean`): on suspension we store
what is left and the trigger that will wake it; on completion we store the
empty residual and mark it finished. -/
def runProcOnce (fuel : Nat) (i : Nat) : SvM StepOutcome := do
  let w ← get
  match w.procs[i]? with
  | none => refuseSv .outOfTier ⟨"4.4"⟩ s!"no process at index {i}"
  | some ps =>
      let (sigs, nba, out, oc) ←
        liftRes ⟨"4.4"⟩ (stepSStmts fuel w.signals w.nba w.out ps.residual)
      -- RE-ARM or finish. An `always` body completing is the end of one
      -- iteration, not of the process; an `initial` body completing is the
      -- end of the process.
      --
      -- A re-armed process must also be RE-ENQUEUED. `ProcStatus.ready` is
      -- not what `stepRegion` reads — it reads `regionQ` — so marking the
      -- process ready without scheduling it leaves it permanently idle:
      -- it never reaches its `@(posedge clk)` again, and therefore can
      -- never be woken again either. The re-entry is what turns "re-armed"
      -- into "runs a second time".
      let (ps', reArmed) : ProcState × Bool :=
        match oc with
        | .done =>
            match ps.arm with
            | some body => ({ ps with residual := body, status := .ready }, true)
            | none => ({ ps with residual := [], status := .finished }, false)
        | .suspended t rest => ({ ps with residual := rest, status := .suspended t }, false)
      set { w with signals := sigs, nba := nba, out := out
                 , procs := w.procs.set! i ps'
                 , regionQ := fun r =>
                     if reArmed && r == Region.active then w.regionQ r ++ [i] else w.regionQ r }
      pure oc

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

/-! ## Edge detection and waking -/

/-- §9.4.2 edge on a 1-bit value.

    posedge : 0→1, 0→x, 0→z, x→1, z→1
    negedge : 1→0, 1→x, 1→z, x→0, z→0

So an `x`/`z` transition **is** an edge whenever the other end is a level:
leaving a known 0 is a posedge even if the destination is unknown, and
arriving at a known 1 is a posedge even if the origin was. Only `x→z`,
`z→x` and a value to itself are edgeless — neither end is a level.

**The rule itself lives in `Basic`**, as `isPosedge`/`isNegedge`, because
the M1 cycle model needs the same one for its async-reset phase and sits
ABOVE this module in the import graph. It was written twice — once here,
once there — and the two spellings disagreed on `x`/`z`. This function is
now only the `Edge`-indexed selector over that one rule, which is the part
`Basic` cannot express: `Edge` is a `SelfCheck` type. -/
def edgeOn (e : Edge) (old new : Logic) : Bool :=
  match e with
  | .pos => isPosedge old new
  | .neg => isNegedge old new
  | .any => isPosedge old new || isNegedge old new

/-- Did `sig` see the given edge between two states?

Reads the clock through `SvState.bit0` — the same accessor the M1 reset
phase uses, rather than the private copy this function used to carry. An
absent or width-0 signal reads `x`, and `x` against `x` is not an edge, so
an undeclared name can never wake anything. -/
def sawEdge (old new : SvState) (sig : String) (e : Edge) : Bool :=
  edgeOn e (SvState.bit0 old sig) (SvState.bit0 new sig)

/-- Wake every process whose edge trigger fired between `old` and `new`,
marking it ready and **enqueueing it in Active**.

This is the half `stepRegion` was missing: it drains `regionQ`, and this
is what fills it. -/
def wakeEdges (old new : SvState) : SvM Unit :=
  modify fun w =>
    let woken : List Nat :=
      (List.range w.procs.size).filter fun i =>
        match w.procs[i]? with
        | some ps =>
            match ps.status with
            | .suspended (.atEdge sig e) => sawEdge old new sig e
            | _ => false
        | none => false
    let procs' := woken.foldl (fun (ps : Array ProcState) i =>
        match ps[i]? with
        | some p => ps.set! i { p with status := .ready }
        | none => ps) w.procs
    { w with procs := procs'
           , regionQ := fun r =>
               if r == Region.active then w.regionQ r ++ woken else w.regionQ r }

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
          pure ()
        else do
          applyNba
          slotStep σ fuel

end LeanModels.Sv
