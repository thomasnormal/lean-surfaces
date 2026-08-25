import LeanModels.Sv.Slot

/-!
# R1 inch 4a — `runSlots`, the trace-producing driver

`slotStep` runs ONE time slot and mutates the world; it produces no trace,
so there was nothing for `cycleOf` to project and the adequacy lemma had
nothing to be stated over. This file closes that gap: drive a stimulus
through `slotStep` and collect a `RegionTrace`.

## Why this is the adequacy lemma's prerequisite and not the lemma

The transfer of the existing estate (162 trace-shaped declarations, 23 of
them the fuel-monotonicity ladder) goes through

    cycleOf (runSlots …) = run …        on the cycle fragment

and **both sides of that equation have to exist before it can be stated.**
The right-hand side has existed since M0. The left-hand side is this file.
The oracle correspondence the statement also needs — `ScheduleOracle`
embedded in `RegionOracle` — landed at inch 2 as
`ScheduleOracle.toRegion` with `toRegion_choose := rfl`, for an unrelated
reason.

**The lemma is deliberately NOT attempted here.** It now carries two
obligations at once — a trace-type change AND a monad change, because the
estate is stated over `Res`-valued `run` while `runSlots` is in `SvM` —
and this lane's habit is to build the definitions, state the obligation,
and prove it against a real goal rather than an imagined one. That is what
worked for the stepper's subsumption.

## The Preponed sample is taken here, and it is not decoration

`Slot.sampled` is read **before the stimulus is applied**, which is what
IEEE 1800 §4.4 means by the Preponed region: clocking blocks and
concurrent assertions see the values as of before anything in the slot
changed them. Nothing in this inch consumes it yet, but taking it at the
wrong moment would be invisible until the reactive regions arrive and
then very hard to find.
-/

namespace LeanModels.Sv

open SelfCheck

set_option autoImplicit false

/-- Overwrite the named signals — the stimulus for one slot.

Names not present are added; names the stimulus omits keep their value.
This is the world-level counterpart of `Semantics.applyInputs`, which is
`Design`-shaped and pure. -/
def setInputs (inputs : SvState) : SvM Unit :=
  modify fun w =>
    { w with signals := inputs.foldl (fun st (n, v) => SvState.set st n v) w.signals }

/-- Drive a stimulus through `slotStep`, one time slot per entry, and
collect the trace.

Each slot records `sampled` (Preponed — before the stimulus lands) and
`final` (after the Active/Inactive/NBA loop closes), which is exactly the
pair `Slot` was given at inch 2 and the pair `cycleOf` projects from. -/
def runSlots (σ : RegionOracle) (fuel : Nat) : List SvState → SvM RegionTrace
  | [] => pure []
  | inputs :: rest => do
      let w0 ← get
      let sampled := w0.signals
      setInputs inputs
      -- WAKE before stepping: a process suspended on `@(posedge clk)` becomes
      -- ready exactly when the stimulus drives that edge. Without this the
      -- ready sets stay empty forever and every trace is silently short.
      let w1 ← get
      wakeEdges sampled w1.signals
      slotStep σ fuel
      let w2 ← get
      let s : Slot := { time := w2.time, sampled := sampled, final := w2.signals }
      let tr ← runSlots σ fuel rest
      pure (s :: tr)

/-! ## End-to-end guards

A world with no processes is the honest first fixture: `slotStep`'s ready
sets are empty, so the loop closes immediately and the driver's own shape
— one slot per stimulus entry, Preponed before, final after — is what is
being pinned, with no process semantics confounding it. -/

section Guards

private def dw : SvWorld := { signals := [("a", LVec.ofNat 4 1)] }

private def traceOf (m : SvM RegionTrace) (w : SvWorld) : Option RegionTrace :=
  match SvM.exec m w with
  | .ok (.ok tr, _) => some tr
  | _ => none

private def stim : List SvState :=
  [[("a", LVec.ofNat 4 2)], [("a", LVec.ofNat 4 3)]]

-- one slot per stimulus entry
#guard (traceOf (runSlots ρ_src 64 stim) dw).map (·.length) == some 2

-- empty stimulus is an empty trace, not a refusal
#guard (traceOf (runSlots ρ_src 64 []) dw).map (·.length) == some 0

-- `final` follows the stimulus ...
#guard ((traceOf (runSlots ρ_src 64 stim) dw).map
          (fun tr => tr.map (fun s => (SvState.lookup s.final "a").map LVec.toNat)))
  == some [some 2, some 3]

-- ... and `sampled` is the PREPONED value: what `a` was BEFORE that slot's
-- stimulus landed, so slot 0 sees the initial 1 and slot 1 sees slot 0's 2.
#guard ((traceOf (runSlots ρ_src 64 stim) dw).map
          (fun tr => tr.map (fun s => (SvState.lookup s.sampled "a").map LVec.toNat)))
  == some [some 1, some 2]

/-! **THE ADEQUACY PREREQUISITE, CHECKED.** `cycleOf` projects a
`RegionTrace` to the cycle view, and that view is the sequence of slot
`final` states — the shape the transfer lemma will equate with `run`. This
guard is not the lemma; it is the evidence that both sides of the lemma
now exist and compose. -/
#guard ((traceOf (runSlots ρ_src 64 stim) dw).map
          (fun tr => (cycleOf tr).map (fun st => (SvState.lookup st "a").map LVec.toNat)))
  == some [some 2, some 3]

-- fuel exhaustion is reachable and LOUD: zero fuel cannot close a slot
#guard (traceOf (runSlots ρ_src 0 stim) dw).isNone

end Guards

end LeanModels.Sv
