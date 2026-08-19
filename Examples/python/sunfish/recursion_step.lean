/-
**`RecursionStep`, RE-EXPRESSED over the repaired rule** — the coordinated edit
the refutation made necessary (docs/backlog.md §L25's R4, §L26's repair).

Two facts forced this file's existence and neither is a design choice:

1. **`BoundRefines` is FALSE** (`not_boundRefines`, basecase_depth0.lean,
   commit `a8e3393`): it quantifies over an arbitrary `pos : RVal`, and at
   `pos := .int 5` the shipped `bound()` refuses on `pos.score`. So
   `RecursionStep` as it stands in bound_depth.lean is **vacuously true** — its
   hypothesis `∀ e < d, BoundRefines V e` includes `e = 0` and is unsatisfiable.
   The strong-induction SHAPE was right; the proposition it ranged over was not.
2. **`BoundRefinesW` is the repair** (commit `d13d2ae`): `BoundWF` folds the
   receiver, the table, its entry SPELLING and the killer dict into one
   nine-projection structure, and `IsPosition pos` replaces the free `RVal` with
   the predicate the code can actually read. `RefinesAt` — the conclusion — is
   character-for-character what it was, so a leaf proved against the old rule is
   consumed by the new one unchanged (`boundRefines_eq` is that receipt).

**Why the step lives HERE and not beside the old one.** `basecase_depth0.lean`
imports `bound_depth.lean`, so `bound_depth` cannot name `BoundRefinesW` without
inverting the import. The old `RecursionStep` stays where it is, marked
superseded, because a recorded statement is never edited into something else —
§L23's law. This file is the successor, and it is the only place R3 should read.

**The strong induction is unchanged from the form landed at `b29da46`**, and its
reason is unchanged with it: the shipped body recurses at `depth - 7` (the
deep-null probe, sunfish.py:453, live from depth 6) and at `depth - 3`
(intrinsic LMR), not only at `depth - 1`. A weak hypothesis cannot discharge
either. The floor `0 ≤ e` is statement 3's own `depth = max(depth, 0)` refloor,
which is what makes the descent well-founded.
-/
import Examples.python.sunfish.basecase_depth0

namespace Examples.python.sunfish.recursion_step

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.bound_depth
open Examples.python.sunfish.basecase_depth0

/-- **THE STEP THE RULE OWES, over the repaired proposition.** Strong induction,
for the reason the header gives. -/
def RecursionStepW (V : RVal → Int → Int) : Prop :=
  ∀ d : Int, 1 ≤ d → (∀ e : Int, 0 ≤ e → e < d → BoundRefinesW V e) → BoundRefinesW V d

/-! ### The cheap non-vacuity check

The point of the rename is that the step's HYPOTHESIS is now satisfiable, where
over `BoundRefines` it was not. This composition is the confirmation: the base
case discharges the strong hypothesis at `d = 1`, so `RecursionStepW` is a
statement with content rather than an implication out of falsehood. It is a
sanity check and not a proof of anything about the engine — exactly the
`#guard`-level assurance §L24's law asks for before a statement is built on. -/

/-- **The step composes with the base case.** At `d = 1` the strong hypothesis is
the base case alone, so this is where "no longer trivially true" is visible. -/
theorem stepW_composes_at_one {V : RVal → Int → Int}
    (hstep : RecursionStepW V) (h0 : BoundRefinesW V 0) : BoundRefinesW V 1 :=
  hstep 1 (by omega) (fun e he0 he1 => by
    have hz : e = 0 := by omega
    subst hz; exact h0)

/-- And at `d = 2`, where the hypothesis is genuinely PLURAL — the shape the
null-move probe's `depth - 7` needs and the weak form could never provide. -/
theorem stepW_composes_at_two {V : RVal → Int → Int}
    (hstep : RecursionStepW V) (h0 : BoundRefinesW V 0) (h1 : BoundRefinesW V 1) :
    BoundRefinesW V 2 :=
  hstep 2 (by omega) (fun e he0 he1 => by
    have hz : e = 0 ∨ e = 1 := by omega
    rcases hz with h | h
    · subst h; exact h0
    · subst h; exact h1)

/-! ### What R3 now reads

`RecursionStepW` is the obligation, and §L25's R1–R5 are its parts. Nothing in
this file says the step is provable; what it says is that proving it would MEAN
something, which is the property the refuted version lacked. -/

#print axioms RecursionStepW
#print axioms stepW_composes_at_one
#print axioms stepW_composes_at_two

end Examples.python.sunfish.recursion_step
