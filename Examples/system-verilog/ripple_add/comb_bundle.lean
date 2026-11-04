import Examples.«system-verilog».ripple_add.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on the bundle `CombDesign ∧ Acyclic` (WP-P, P1)

The older Examples (`comb_view.lean`, `comb_proof.lean`) prove `CombDesign` and `Acyclic` as two
theorems; both keep working (this file does not replace them: they are the backward-compatibility
check of the single-goal forms). The bundle proves both in ONE theorem from ONE application of the
soundness theorem (`CombView.comb_acyclic_view` / `comb_lex_view`) and one round of obligation
normalizations, instead of repeating the in-range and one-driver normalizations in each:

```
theorem ripple_struct (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) ∧ Acyclic (ripple_add.sem N) := by
  sv_structure (rank := rippleRank …)
  all_goals (intros; omega)
```

The goals it leaves are those of `Acyclic` alone (here seven: `inRange_1-2`, `driverDisjoint_1-3`,
`rankDecreases_1-2`), which contain those of `CombDesign` (five).

Build: `lake build Examples.«system-verilog».ripple_add.comb_bundle`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».ripple_add.gen

namespace Examples.«system-verilog».ripple_add.comb_bundle

/-! ## Positive: the bundle, every `N ≥ 1`, with a `Nat` rank and with a lexicographic key -/

theorem ripple_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (ripple_add.sem N) ∧ Acyclic (ripple_add.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; omega)

/-- A lexicographic key `(stage, bit, phase)` of the same schedule. -/
def rippleKey (N : Nat) : SiteId → Key
  | .plain 0 => (0, 0, 0)
  | .plain _ => (N + 1, 0, 0)
  | .fam _ _ [i] => (1, i.toNat, 0)
  | .fam _ _ _ => (N + 1, 0, 0)

theorem ripple_struct_lex (N : Nat) (hN : 1 ≤ N) :
    CombDesign (ripple_add.sem N) ∧ Acyclic (ripple_add.sem N) := by
  sv_structure (lexRank := rippleKey N)
  all_goals (intros; omega)

-- The two halves are what the single-goal forms prove.
example (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) := (ripple_struct N hN).1
example (N : Nat) (hN : 1 ≤ N) : Acyclic (ripple_add.sem N) := (ripple_struct N hN).2

/-! ## Negative: the sampled checks speak for the bundle too -/

/--
error: sv_structure: the rank does not decrease along a read: `plain#1` (rank 0) reads a window of `c` driven by `g_bit#1[0]` (rank 0, window c[1]); a driver must have a SMALLER rank than its reader (sampled at [N] = [1]; a genuine violation, not a missing proof, unless your hypotheses exclude this point)
  the read that forms the edge: `c[1]` of `plain#1`, written by `g_bit#1[0]` (window c[1])
-/
#guard_msgs (whitespace := lax) in
theorem bad_rank (N : Nat) (hN : 1 ≤ N) :
    CombDesign (ripple_add.sem N) ∧ Acyclic (ripple_add.sem N) := by
  sv_structure (rank := fun _ => 0)
  all_goals (intros; omega)

-- A bundle needs a rank, like `Acyclic` alone.
/--
error: sv_structure: an `Acyclic` goal needs a rank over site identities, e.g. `sv_structure (rank := rippleRank … …)` or a lexicographic key `sv_structure (lexRank := fun | .plain 0 => (0, 0, 0) | …)`; run `sv_structure?` to see the sites and the rank relation they must satisfy
-/
#guard_msgs (whitespace := lax) in
theorem no_rank (N : Nat) (hN : 1 ≤ N) :
    CombDesign (ripple_add.sem N) ∧ Acyclic (ripple_add.sem N) := by
  sv_structure
  all_goals (intros; omega)

-- `using hc` is for an `Acyclic` goal alone.
/--
error: sv_structure: `using hc` is for an `Acyclic` goal alone; the conjunction `CombDesign ∧ Acyclic` derives the one-driver obligation itself
-/
#guard_msgs (whitespace := lax) in
theorem bundle_using (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (ripple_add.sem N)) :
    CombDesign (ripple_add.sem N) ∧ Acyclic (ripple_add.sem N) := by
  sv_structure (rank := fun _ => 0) using hc
  all_goals (intros; omega)

/-- info: 'Examples.«system-verilog».ripple_add.comb_bundle.ripple_struct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ripple_struct

/-- info: 'Examples.«system-verilog».ripple_add.comb_bundle.ripple_struct_lex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ripple_struct_lex

end Examples.«system-verilog».ripple_add.comb_bundle
