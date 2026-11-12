import Examples.«system-verilog».comb_karatsuba.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic

/-!
# The coverage goals of a 19-site design with generate loops, closed by `sv_cover` (WP-COV)

`sv_equations` states one coverage goal per read of the design: every bit a read observes has a source. For this
design (26 reads of the padded operand vectors, each bit written by SEVERAL writer families: `ap[i]` by `g_pin` below
`N` and by `g_pz` above, a localparam `H` inside every window) the normalization of the WHOLE obligation ran out of `simp`
steps (`maximum number of steps exceeded`, 100000), and the goals were left in the SITE-WITNESS form
`∃ b, (b = site₀ ∨ … ∨ b = site₁₈) ∧ …`, which `sv_cover`'s 2-D rule does not read and whose site route cannot close a bit
with several writers. `sv_equations` now renormalizes such a goal on its own (`sv_cover_renorm`): the goals come out as the
explicit disjunction of writers and the same standard closer closes all 17 of them, with no hand-written case split.

The theorem states a trivial specification: the point is the obligations `sv_equations` hands back, not the arithmetic
(the multiplier's proof, `svgolf/design/tasks-week2/clmul/karatsuba/G3h.lean`, goes through the same `sv_cover` calls).

The range premise is `N < 2147483647`: `H = (N + 1) / 2` adds before it divides, and the instantiation wraps that sum to
32 bits (IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), so at `N = 2147483647` the quotient is negative.

Build: `lake build Examples.«system-verilog».comb_karatsuba.cover`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_karatsuba.gen

namespace Examples.«system-verilog».comb_karatsuba.cover

set_option maxHeartbeats 0 in
/-- Every obligation of `sv_equations` that is left (the coverage of every read, 17 goals) is closed by the standard
closer; the two input premises by `inKnown_ofBitVec`. -/
theorem k1u_covers (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647)
    (hc : CombDesign (clmul_n.sem N)) (ha : Acyclic (clmul_n.sem N)) :
    clmul_n.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) → True := by
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y hA hB
  sv_equations
  · trivial
  all_goals first
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (intros; omega)
    | sv_cover

/-- info: 'Examples.«system-verilog».comb_karatsuba.cover.k1u_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms k1u_covers

end Examples.«system-verilog».comb_karatsuba.cover
