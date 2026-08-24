/-
**THE FLAGSHIP OF THE SUNFISH R-TRACK, TYPED.**

`bound_refines_fuelModel` is the campaign's goal theorem: the shipped
`Searcher.bound` keeps the promise its own docstring makes, at every
non-negative depth. Until this file it existed only as PROSE — in
`docs/backlog-archive.md` and in three successive "and then it assembles"
ladders — and nowhere in the tree.

**That absence had a cost, and it is why this file is small and early.** A goal
theorem nobody has typed is a goal nobody can typecheck against: every WAITING
trigger aimed at it is unexecutable, every lane's claim to be "serving the
flagship" is unfalsifiable, and the distance to it can only be asserted. Typing
it converts all three into things a machine can check. `docs/sunfish-flagship-chain.md`
is the ledger of the remaining distance; this is its rung 1.

**What is proved here, and what is NOT.** The strong induction is discharged —
once, here — so that the flagship reduces to exactly TWO named obligations and
no proof shape. Neither obligation is discharged in this file:

* `BoundRefinesW V 0` — the depth-0 base case, the calmness/base-case lane's;
* `RecursionStepW V` — the recursion step, this lane's.

So `bound_refines_fuelModel` below is a genuine theorem with genuine hypotheses,
not a definition dressed as one. When those two land it is closed by
application, and nothing about its shape is then in question.

**Why the induction is STRONG** (and why the weak form would not do): `bound()`
recurses at `depth - 1`, at `depth - 3` under the intrinsic reduction, and at
`depth - 7` for the deep-null probe, so a predecessor-step induction cannot
reach its own hypotheses. `RecursionStepW`'s statement records that decision;
this file consumes it.

**The proposition is `BoundRefinesW`, not `BoundRefines`** — the repaired one.
Plain `BoundRefines` is FALSE (`not_boundRefines` refutes it at `pos := .int 5`,
where the shipped `bound()` reaches `pos.score` and refuses), which made the
original `RecursionStep` vacuously true. Using the repaired proposition is what
makes the theorem below have content.
-/
import Examples.python.sunfish.recursion_step

namespace Examples.python.sunfish.flagship

open LeanModels LeanModels.Python
open Examples.python.sunfish.basecase_depth0 (BoundRefinesW)
open Examples.python.sunfish.recursion_step (RecursionStepW)

/-- **THE FLAGSHIP.** The shipped `Searcher.bound` refines the fuel model at
every non-negative depth. -/
def BoundRefinesFuelModel (V : RVal → Int → Int) : Prop :=
  ∀ d : Int, 0 ≤ d → BoundRefinesW V d

/-- **AND IT ASSEMBLES**, from the base case and the step and nothing else. The
induction over `0 ≤ d : Int` is routed through `d.toNat` so that the recursion is
on a `Nat` and the arithmetic side conditions are `omega`'s — the shape is
ordinary, which is the point: no part of the flagship's difficulty lives here. -/
theorem bound_refines_fuelModel {V : RVal → Int → Int}
    (h0 : BoundRefinesW V 0) (hstep : RecursionStepW V) :
    BoundRefinesFuelModel V := by
  have key : ∀ n : Nat, ∀ d : Int, 0 ≤ d → d.toNat ≤ n → BoundRefinesW V d := by
    intro n
    induction n with
    | zero =>
      intro d hd hn
      have hz : d = 0 := by omega
      subst hz; exact h0
    | succ n ih =>
      intro d hd hn
      rcases (show d = 0 ∨ 1 ≤ d by omega) with hz | hz
      · subst hz; exact h0
      · exact hstep d hz (fun e he0 he1 => ih e he0 (by omega))
  intro d hd
  exact key d.toNat d hd (Nat.le_refl _)

#print axioms bound_refines_fuelModel

end Examples.python.sunfish.flagship
