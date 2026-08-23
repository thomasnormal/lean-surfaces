/-
**R3c ON THE MONADIC INTERPRETER** — the campaign's re-founding, first inch.

`docs/python-monadic-rebuild.md` is the interpreter; `docs/backlog/sunfish-rtrack.md`
entry -3 is this lane's transport classification, and this file is that
classification put to work. Two things land here and they are deliberately the
two CHEAPEST things that are also load-bearing:

1. **The 176/177 allocation ledger, RE-RUN on the new interpreter.** This lane
   proposed it as the first thing to re-run precisely because it closed to the
   object on the trunk: if it still closes, that is a free independent check on
   the rebuild's allocation behaviour, and if it does not, the difference IS what
   the re-founding changed. It costs one identifier — `callIn` becomes
   `Monadic.callInMono`, which has `callIn`'s type BY CONSTRUCTION (Eval.lean §4).
2. **`FoldInv` over `RoundOK`** — the vocabulary settled with the base-case lane
   (backlog entries -2, -4), stated for the first time.

**Why this file may import the rebuild at all.** `LeanModels/Python/Monadic.lean`
is imported by `Main.lean` and by nothing else, deliberately: 65 files under
`Examples/` take the `LeanModels` umbrella and an import there would invalidate
every one of them. A file that names the rebuild must therefore import it
DIRECTLY, which is what this one does, and the cost is charged to this file
alone.

**What is NOT here, and why.** No interpreter-facing gate. The survey of the
rebuild says the generator ENGINE is complete (`stepIterAt`, `execGenAt`,
`forGenAt`, `drainIterAt`, `anyAllIterAt`, all `Kont` fields) but the PROOF LAYER
is not: there are zero occurrences of `IterSteps`, `GenEmits`, `GenSilent` or
`GenYields` under `Monadic/`. Those judgments are this lane's to re-state, and
they are the next inch, not this one.
-/
import Examples.python.sunfish.bound_depth
import LeanModels.Python.Monadic

namespace Examples.python.sunfish.monadic_fold

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.bound_depth (Round Exit Sound Report foldFrom
  fold_report QSRoundOK qsRoundOK_sound)

set_option maxRecDepth 100000

/-! ## §1 THE ALLOCATION LEDGER, RE-RUN

The trunk's numbers (backlog §L55, and §L32 before it): a depth-1 node on the
opening board answers **46 in 1 node** at `gamma ≥ 47` leaving the heap at
`70 → 246`, and **0 in 2 nodes** at `gamma ≤ 0` leaving it at `70 → 247`. The
ledger that closed those to the object was

    settle: 3 (cell, closure, generator) + 1 (calm genexp) + 84 (ordering line)
            + 88 (the correction's PARTIAL drain)                        = 176
    cut:    3 + 1 + 84 + 1 (`pos.move`) + 88 (the child's subtree)        = 177

**The fixture is trunk-built and the MEASUREMENT is monadic**, which is the same
boundary the acceptance gate itself uses: `searcherW` is a pinned `World`
(pins_common, `#guard`ed in `bound_depth.lean`), `World`/`Heap`/`RVal` are shared
substrate that the rebuild does not touch, and `callInMono` has `callIn`'s type
by construction. So the only thing that changes between the trunk row and the row
below is which interpreter runs `Searcher.bound`. -/

/-- The measurement, parameterised by WHICH interpreter runs `Searcher.bound`.
`callIn` and `Monadic.callInMono` have the same type by construction
(Eval.lean §4), so the interpreter is an argument and the two rows below differ
in nothing else. -/
private def probeWith
    (run : Module → Nat → World → String → Array RVal → Run World RVal)
    (gamma depth : Int) (F : Nat) : Option (Int × Int × Nat × Nat) :=
  match searcherW with
  | some (w, a) =>
    (match run sunfish F w "Searcher.bound" #[.ref a, posH 0, .int gamma, .int depth] with
     | .ok w' (RVal.int r) =>
       (match Heap.get? w'.heap a with
        | some (Obj.instance _ attrs) =>
          (match Env.lookup attrs.toList "nodes" with
           | some (RVal.int n) => some (r, n, w.heap.size, w'.heap.size)
           | _ => Option.none)
        | _ => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

private def probeTrunk := probeWith callIn
private def probeMono := probeWith Monadic.callInMono

/-! **THE ROWS, PRINTED BEFORE THEY ARE ASSERTED.** A `#guard` that fails says
only "false"; the queue for a build tenure is measured in hours, so an assertion
about behaviour this lane has not yet observed must not cost a whole tenure to
return one bit. These four `#eval`s put the measured rows in the build log
FIRST, so that even a RED build below hands back the numbers that made it red
and the next tenure is an edit rather than another blind shot. -/
#eval probeMono 47 1 300
#eval probeMono 0 1 300
#eval probeTrunk 47 1 300
#eval probeTrunk 0 1 300

/-! **THE LEDGER, on the rebuild.** Answer, node count, heap in, heap out — the
trunk's four numbers, unchanged. -/
#guard probeMono 47 1 300 == some (46, 1, 70, 246)
#guard probeMono 0 1 300 == some (0, 2, 70, 247)

/-! …and the decomposition still closes to the object. -/
#guard 3 + 1 + 84 + 88 == 176 && 246 - 70 == 176
#guard 3 + 1 + 84 + 1 + 88 == 177 && 247 - 70 == 177

/-! **THE DIFFERENTIAL ROW.** The rows above pin the rebuild against numbers
this lane measured on the trunk MONTHS ago and has been carrying in prose; the
rows below pin it against the trunk *as it stands in this same build*, at
identical fuel, with the interpreter as the only difference. That is the check
that cannot go stale, and it is the one that would survive a re-pin of the
fixture.

The fuel THRESHOLD is asserted separately below, and only because it has now
been measured. Fuel thresholds are the one measurement that does not transport:
the rebuild spends fuel only at the knot, so at fixed `F` it is at least as
decisive as the trunk (Eval.lean §0.2), and the DIRECTION of that inequality at
this boundary had to be read off the machine before any number could be written
down. -/
#guard probeMono 47 1 300 == probeTrunk 47 1 300
#guard probeMono 0 1 300 == probeTrunk 0 1 300

/-! **THE THRESHOLD, MEASURED FIRST AND GUARDED SECOND.** `fold_depth1.lean:114`
guards the trunk's threshold: at `F = 200` both trunk rows are `none`. The
tenure of 2026-08-23 03:13 printed the rebuild's answer at the same fuel and got
`(true, true)` — and the trunk's, `(true, true)` — so the two interpreters
EXHAUST TOGETHER at this boundary and the rebuild is not more decisive here.
Those rows were `#eval`s in the commit that measured them and are `#guard`s in
this one, which is the only order in which a guard may acquire a number: the
machine answers, then the file asserts. Had either row come back `false`, §0.2
permits it and the assertion below would have been written the other way. -/
#guard (probeMono 47 1 200).isNone && (probeMono 0 1 200).isNone
#guard (probeTrunk 47 1 200).isNone && (probeTrunk 0 1 200).isNone

/-! ## §2 `FoldInv` over `RoundOK` — the settled vocabulary, first statement

Agreed with the base-case lane (backlog entries -2 and -4): the per-ROUND
classification is the PRIMITIVE, `Sound` is DERIVED from it, and the
schedule-level invariant is ONE structure stated over the primitive.

**This is a strengthening, not a rename.** `fold_depth1.lean`'s `RanInv` carries
`∀ r ∈ rs, Sound gamma value r.score` — the DERIVED fact, per round. `FoldInv`
carries `RoundOK` per round, the classification itself, and recovers `Sound`
where it is needed by `qsRoundOK_sound`. So `FoldInv → RanInv` holds and not the
converse, which is the whole content of "the classification is the primitive".

**`RoundOK` is the settled NAME and this is an alias, not a copy.** The lane that
owns `QSRoundOK` agreed to spend the name — *"the QS prefix was accurate about
where the thing was first needed and wrong about what it is"* — but renaming it
in `bound_depth.lean` is pure churn on a file the re-founding retires, so the
rename is owed at the next legitimate tenure there and the alias carries the
meaning until then. Aliasing rather than copying is the whole point: there is
exactly one definition of the four-way classification in the repository. -/

/-- The settled name for the per-round classification. One definition, aliased —
the rename in `bound_depth.lean` §3 is owed and mechanical. -/
abbrev RoundOK := QSRoundOK

/-- **THE FOLD INVARIANT.** Three fields over the primitive, and the base-case
lane's constraint is honoured by what is ABSENT: it carries the ROUND obligation
only. Neither stand-pat direction is baked in — the fail-low arm needs
`value ≤ sc` and the fail-high arm its exact converse, and a caller supplying
both asserts `V pos 0 = pos.score`, which DEGENERATES the cut arm to
`gamma ≤ sc`: 3.5% of that lane's measured cuts, never the 84% that cut on a
searched move. Each exit's corollary takes the direction it needs. -/
structure FoldInv (gamma value best : Int) (rs : List Round) : Prop where
  sound : Sound gamma value best
  rounds : ∀ r ∈ rs, RoundOK gamma value r
  attain : value ≤ best ∨ ∃ r ∈ rs, value ≤ r.score

/-- **THE STEP.** One non-cutting `report` round consumed, the accumulator
advanced by `max`. The round's own `Sound` comes from the primitive rather than
from a separate premise, which is the whole economy of stating it this way. -/
theorem FoldInv.step {gamma value best sc : Int} {lv : Bool} {rs : List Round}
    (h : FoldInv gamma value best (.report sc lv :: rs)) :
    FoldInv gamma value (max best sc) rs := by
  have h1 : Sound gamma value sc := by
    have := qsRoundOK_sound (h.rounds (.report sc lv) (by simp))
    simpa [Round.score] using this
  refine ⟨h.sound.max h1, fun r hr => h.rounds r (by simp [hr]), ?_⟩
  rcases h.attain with hb | ⟨r, hr, hv⟩
  · exact Or.inl (by omega)
  · rcases List.mem_cons.mp hr with rfl | hr'
    · have hs : value ≤ sc := by simpa [Round.score] using hv
      exact Or.inl (by omega)
    · exact Or.inr ⟨r, hr', hv⟩

/-- **`Inv []` IS DISCHARGED**, not refuted — the difference from depth 0, where
the corresponding invariant at the empty remainder is `False`. -/
theorem FoldInv.nil {gamma value best : Int} (h : FoldInv gamma value best []) :
    Report gamma best value := by
  have hv : value ≤ best := by
    rcases h.attain with hb | ⟨r, hr, -⟩
    · exact hb
    · exact absurd hr (by simp)
  by_cases hlt : best < gamma
  · exact Or.inl ⟨hlt, hv⟩
  · have hbv : best ≤ value := by
      rcases h.sound with h1 | h2
      · omega
      · exact h2
    exact Or.inr ⟨by omega, hbv⟩

/-- **THE WHOLE SCHEDULE.** The futility premise is the caller's, supplied by the
EXIT — on the exhausting arm by "a schedule that ran out contains no `settle`",
which is this lane's `foldFrom_ran_no_settle`. `FoldInv` does not carry it. -/
theorem FoldInv.run {gamma value best : Int} {live : Bool} {rs : List Round}
    (h : FoldInv gamma value best rs) (hns : ∀ cap, Round.settle cap ∉ rs) :
    Report gamma (foldFrom gamma best live rs).1 value :=
  fold_report h.sound (fun r hr => qsRoundOK_sound (h.rounds r hr)) h.attain
    (fun cap hm => absurd hm (hns cap))

#print axioms FoldInv.step
#print axioms FoldInv.nil
#print axioms FoldInv.run

end Examples.python.sunfish.monadic_fold
