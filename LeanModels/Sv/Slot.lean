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
      let ps' : ProcState :=
        match oc with
        | .done => { residual := [], status := .finished }
        | .suspended t rest => { residual := rest, status := .suspended t }
      set { w with signals := sigs, nba := nba, out := out,
                   procs := w.procs.set! i ps' }
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
  set { w with k := w.k + 1, curRegion := r }
  match ready with
  | [] => pure false
  | _ =>
      for i in ready do
        let _ ← runProcOnce fuel i
      modify fun w' =>
        { w' with regionQ := fun r' => if r' == r then [] else w'.regionQ r' }
      pure true

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
