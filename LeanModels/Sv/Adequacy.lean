import LeanModels.Sv.Load

/-!
# R1 inch 4b — the adequacy lemma, STATED

Obligations 1 and 2 were solved at inch 4 (`cycleOf` exists; `SvM.exec`
projects) and obligation 3 at inch 4a (`elabDesign` turns a `Design` into
an `SvWorld`). With all three in hand the lemma should have been a matter
of writing it down. It was not, and the reason is the finding of this
inch.

## The obstruction: the two models do not take the same stimulus

**The M0 clock is IMPLICIT.** `Semantics.lean` says so in as many words:
*every `cycleStep` is one posedge of the (single) clock*. A cycle-model
stimulus therefore drives the DATA inputs and never mentions a clock —
`run d σ fuel stim` produces exactly `stim.length` states.

**The region model has no implicit anything.** A process suspended on
`@(posedge clk)` wakes when `wakeEdges` sees `clk` actually go 0 → 1, and
driving a real edge takes **two** stimulus entries: one holding it low,
one raising it. So `runSlots` over the same list produces `stim.length`
slots and **not one posedge among them**.

The lemma `run d σ fuel stim = cycleOf (runSlots …)` is therefore not
merely unproved, it is **ill-typed as an intention**: the left side counts
cycles and the right side counts time slots, and at inch 4a they were not
the same unit. Two definitions close the gap, and naming them is most of
this inch's work:

* `clockExpand` — the stimulus translation, 2 slots per cycle;
* `posedgeSlots` — the trace decimation, keeping the slot the edge ran in.

## And a second obstruction, found by computing rather than by reading

The expanded stimulus **introduces a signal the cycle model never has**.
`clk` is driven 0/1 on the region side and stays `x` on the cycle side,
forever, because nothing there ever assigns it. So the two runs disagree
on `clk` in every state, by construction, and **a whole-state equality is
false for a reason that has nothing to do with adequacy**.

The comparison has to be made through an OBSERVATION. `d.outputNames` is
the honest one — it is what a cycle-level observer of the design can see,
and it is already the shape `divResult`/`sampleAtFirst` observe through.

## What is proved here, and what is only stated

**Guarded**: the two translations, and — the load-bearing one — that the
two models AGREE on a real design through the expansion and the
decimation. That is executable evidence that the statement below is even
plausible, and it is what would catch a wrong expansion immediately.

**Stated, not proved**: `CycleAdequacy`. The proof is priced in
`docs/backlog/sv.md` and is NOT attempted here, for the reason this lane
has now applied three times — a proof written against an imagined goal is
worth less than a statement written against a real one.
-/

namespace LeanModels.Sv

open SelfCheck

set_option autoImplicit false

/-! ## The two translations -/

/-- One cycle becomes TWO time slots: `clk` low, then `clk` high. The
raise is the posedge the M0 model leaves implicit.

`SvState.set` rather than an append, so a stimulus that already mentions
the clock is overridden rather than shadowed — the expansion decides the
clock, not the caller. -/
def clockExpand (clk : String) (stim : List SvState) : List SvState :=
  stim.flatMap fun inp =>
    [SvState.set inp clk (LVec.ofNat 1 0), SvState.set inp clk (LVec.ofNat 1 1)]

/-- The inverse projection on the trace: of each low/high pair keep the
SECOND, which is the slot the posedge ran in and therefore the slot whose
final state answers to one `cycleStep`.

A trailing unpaired element is DROPPED: it is a cycle whose clock never
rose, so there is no cycle-model state to compare it with. -/
def posedgeSlots {α : Type} : List α → List α
  | _ :: b :: rest => b :: posedgeSlots rest
  | _ => []

/-! ## The obligation -/

/-- **The adequacy statement.** Through `clockExpand` on the way in and
`posedgeSlots` on the way out, the region semantics and the cycle
semantics agree on everything the design's outputs can show.

Quantified over `σ` — the same `∀ σ` the tier's other theorems use —
with `σ.toRegion` on the region side, which is the conservative embedding
`toRegion_choose` already discharges.

`elabDesign d = .ok w` is the loadability hypothesis and is deliberately
NOT weakened to `d.isCycleFragment`: that predicate admits `always_comb`
and `assign`, which `elabDesign` refuses (their comb sensitivity has no
`Trigger`). Stating it over the fragment would make the lemma false for a
reason already known and named. -/
def CycleAdequacy (d : Design) (clk : String) (σ : ScheduleOracle)
    (fuel : Nat) (stim : List SvState) : Prop :=
  ∀ (w : SvWorld) (tr : RegionTrace) (w' : SvWorld) (cyc : List SvState),
    elabDesign d = .ok w →
    SvM.exec (runSlots σ.toRegion fuel (clockExpand clk stim)) w = .ok (.ok tr, w') →
    run d σ fuel stim = .ok cyc →
    ∀ s : String, s ∈ d.outputNames.toList →
      (posedgeSlots (cycleOf tr)).map (fun st => SvState.lookup st s)
        = cyc.map (fun st => SvState.lookup st s)

/-! ## Guards -/

section Guards

-- the expansion: two slots per cycle, low then high
#guard clockExpand "c" [] == ([] : List SvState)
#guard (clockExpand "c" [[], []]).length == 4
#guard ((clockExpand "c" [[]]).map (fun st => (SvState.lookup st "c").bind LVec.toNat?))
  == [some 0, some 1]
-- and it OVERRIDES a clock the caller tried to set, rather than shadowing it
#guard ((clockExpand "c" [[("c", LVec.ofNat 1 1)]]).map
          (fun st => (SvState.lookup st "c").bind LVec.toNat?)) == [some 0, some 1]

-- the decimation: keep the second of each pair, drop a trailing singleton
#guard posedgeSlots [1, 2, 3, 4] == [2, 4]
#guard posedgeSlots ([] : List Nat) == []
#guard posedgeSlots [1] == []
#guard posedgeSlots [1, 2, 3] == [2]

/-! **THE AGREEMENT GUARD.** `always_ff @(posedge clk) n = 1;` run on both
sides of the lemma. `n` is an OUTPUT here, which is what makes it
observable in the sense `CycleAdequacy` compares through. -/
private def ffD : Design :=
  { name := "ff"
  , decls := #[{ name := "clk", width := 1, isInput := true },
               { name := "n", width := 4, isOutput := true }]
  , processes := #[.alwaysFF "clk" (.blockingAssign "n" (.lit (LVec.ofNat 4 1)))] }

private def cycStim : List SvState := [[], []]

/-- The cycle model's view of one signal: the M0 stimulus, undecimated. -/
private def cycleObs (s : String) : Option (List (Option Nat)) :=
  match run ffD σ_src 256 cycStim with
  | .ok sts => some (sts.map (fun st => (SvState.lookup st s).bind LVec.toNat?))
  | _ => none

/-- The region model's view of the same signal: expanded in, decimated out. -/
private def regionObs (s : String) : Option (List (Option Nat)) :=
  match elabDesign ffD with
  | .ok w =>
      match SvM.exec (runSlots ρ_src 256 (clockExpand "clk" cycStim)) w with
      | .ok (.ok tr, _) =>
          some ((posedgeSlots (cycleOf tr)).map
                  (fun st => (SvState.lookup st s).bind LVec.toNat?))
      | _ => none
  | _ => none

-- each side, pinned separately, so a failure says WHICH model moved
#guard cycleObs "n" == some [some 1, some 1]
#guard regionObs "n" == some [some 1, some 1]

-- ... and the agreement itself, which is `CycleAdequacy` at this instance
#guard cycleObs "n" == regionObs "n"

/-! And the second obstruction, PINNED rather than described: on `clk` the
two models disagree in every state, because the cycle model never assigns
the clock it is implicitly stepping. This is why `CycleAdequacy` compares
through `outputNames` and not through whole states. -/
#guard cycleObs "clk" == some [none, none]
#guard regionObs "clk" == some [some 1, some 1]
#guard !(cycleObs "clk" == regionObs "clk")

end Guards

end LeanModels.Sv
