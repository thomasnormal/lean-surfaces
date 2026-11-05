import LeanModels.Sv.SeqProfile

/-!
# Exact multi-clock instants (`LeanModels.Sv` — F4)

`cycleStep2` is the one-clock profile: one stimulus entry denotes one rising
edge of its clock.  This module adds the source-shaped multi-clock view without
changing that API.  A `ClockInstant` names the clocks that rise together and
the input values settled for the instant.  The step applies inputs, settles
combinational logic, runs asynchronous reset events, runs only edge processes
whose clock is in `rises`, commits their NBAs together, and settles again.

Because every edge body is evaluated against the same pre-commit state, two
coincident edges sample old values exactly as IEEE 1800-2023 §4.4.2 and
§10.4.2 require.  The schedule oracle still quantifies active-process order;
the instant list quantifies clock ratios, stopped clocks, drift, and coincident
edges.  No metastability or resolution approximation is introduced here.
-/

namespace LeanModels.Sv

structure ClockInstant where
  rises : List String
  inputs : SvState
deriving Repr, Inhabited

def Design2.edgeIndicesAt (d : Design2) (rises : List String) : List Nat :=
  d.edgeIndices.filter fun i =>
    match d.processes[i]? with
    | some p => p.clock?.any (rises.contains ·)
    | none => false

def cycleStep2AtInstant (d : Design2) (σ : ScheduleOracle) (fuel : Nat)
    (instant : ClockInstant) (prev st : SvState) (k : Nat := 0) :
    Res (SvState × Nat) := do
  let st0 := applyInputs2 d instant.inputs st
  let (st1, k1) ← combSettle2 d σ fuel st0 k
  let rdy := d.resetIndices prev st1
  let (st2, k2) ←
    match rdy with
    | [] => pure (st1, k1)
    | _ => do
        let (str, nbar) ← resetPass2 d fuel st1 [] (σ.choose k1 rdy)
        combSettle2 d σ fuel (commitNba2 str nbar) (k1 + 1)
  let selected := d.edgeIndicesAt instant.rises
  let (st3, nba) ← edgePass2 d fuel st2 [] (σ.choose k2 selected)
  let st4 := commitNba2 st3 nba
  combSettle2 d σ fuel st4 (k2 + 1)

def runFromMulti (d : Design2) (σ : ScheduleOracle) (fuel : Nat)
    (prev : SvState) (k : Nat) : List ClockInstant → Res (List SvState)
  | [] => .ok []
  | instant :: rest => do
      let (st', k') ← cycleStep2AtInstant d σ fuel instant prev prev k
      let tr ← runFromMulti d σ fuel st' k' rest
      return st' :: tr

/-- Run the exact E multi-clock profile over a list of simultaneous-event
instants.  The first snapshot is the post-instant state, matching `run2`'s
trace convention. -/
def runMulti (d : Design2) (σ : ScheduleOracle) (fuel : Nat)
    (instants : List ClockInstant) : Res (List SvState) := do
  let tr ← runFromMulti d σ fuel (initState2 d) 0 instants
  return tr

/-! ## Clean-room two-clock guards -/

private def twoClock : Design2 where
  name := "two_clock"
  decls := #[
    { name := "wclk", width := 1, isInput := true },
    { name := "rclk", width := 1, isInput := true },
    { name := "d", width := 1, isInput := true },
    { name := "a", width := 1 },
    { name := "b", width := 1 }]
  processes := #[
    .alwaysFF "wclk" (.nbaAssign (.ident "a") (.ident "d")),
    .alwaysFF "rclk" (.nbaAssign (.ident "b") (.ident "a"))]

private def ci (rises : List String) (wclk rclk d : Logic) : ClockInstant :=
  { rises, inputs := [("wclk", LVec.ofLogic wclk), ("rclk", LVec.ofLogic rclk),
      ("d", LVec.ofLogic d)] }

-- Separate edges: `a` captures d, then `b` captures the settled a.
#guard (runMulti twoClock σ_src 64 [
    ci ["wclk"] .l0 .l0 .l1,
    ci ["rclk"] .l0 .l1 .l1]).toOption.map (·.map (SvState.showSignal · "a")) ==
  some ["1", "1"]

-- Coincident edges: b sees the old a, even though a's NBA commits together.
#guard (runMulti twoClock σ_src 64 [
    ci ["wclk", "rclk"] .l0 .l0 .l1]).toOption.map (·.map (SvState.showSignal · "b")) ==
  some ["x"]

end LeanModels.Sv
