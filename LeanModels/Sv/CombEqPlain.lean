import LeanModels.Sv.CombEqThm
import LeanModels.Sv.CombViewPlain

/-!
# Flat netlists: the obligations of `sv_equations` as closed statements (WP-P3b)

`sv_equations` returns the obligations `width` (every operand as wide as its target), `bitRead` (a bit read
inside its vector) and `cover` (every bit a read observes has a source), besides the two it shares with
`sv_structure` (`auto`, `inRange`: `CombViewPlain.lean`). For a design whose sites are ALL plain (no
generate loop) and that has no free parameter, each is a closed, decidable statement about the site list:
the tactic decides it (`closeByDecide`) instead of normalizing it with `simp`, which spends about 30 s of
a 60 s `sv_equations` on the coverage obligation of the 113-gate `aes_sbox` netlist and leaves one
`∃ b, (b = site₀ ∨ … ∨ b = site₁₁₂) ∧ …` goal per read for the player.

The three lemmas are the reduction (`Loops.all [] σ P` is `P σ`); the coverage one goes through
`SrcPlain`, `SrcS` with the loops gone, because `LoopsE` over an arbitrary header list is not decidable.
A design with a generate loop or a parameter is untouched.
-/

namespace LeanModels.Sv
namespace CombEq

/-- `accBitUpper` is decidable (a bit read: `idx + 1 ≤ width`; every other access: `True`). -/
instance (dwv : String → Nat) (σ' : String → Int) (a : CombView.Acc) : Decidable (accBitUpper dwv σ' a) := by
  unfold accBitUpper
  split <;> infer_instance

/-- `Sk.WidthOk` is decidable (structural recursion on the skeleton). -/
def Sk.decWidthOk (σ : String → Int) (dw : String → Nat) (tw : Nat) : (sk : Sk) → Decidable (sk.WidthOk σ dw tw)
  | .lit v => inferInstanceAs (Decidable (v.width = tw))
  | .rd a => inferInstanceAs (Decidable ((a.win σ dw).2.2 = tw))
  | .gate _ l r =>
      haveI := Sk.decWidthOk σ dw tw l
      haveI := Sk.decWidthOk σ dw tw r
      inferInstanceAs (Decidable (l.WidthOk σ dw tw ∧ r.WidthOk σ dw tw))
  | .cat ps => inferInstanceAs (Decidable ((ps.map (Part.wid σ dw)).sum = tw))
  | .fill _ => inferInstanceAs (Decidable True)

instance (σ : String → Int) (dw : String → Nat) (tw : Nat) (sk : Sk) : Decidable (sk.WidthOk σ dw tw) :=
  Sk.decWidthOk σ dw tw sk

end CombEq

namespace CombView
namespace Summary
open LeanModels.Sv.CombEq

/-- **Bit `p` of signal `n` has a source, for a flat netlist**: `SrcS` with the loop quantifier gone (every
site is plain, so `LoopsE [] σ P` is `P σ`). Decidable. -/
def SrcPlain (s : Summary) (σ : String → Int) (n : String) (p : Nat) : Prop :=
  (n ∈ s.inputNames ∧ p < s.dw σ n) ∨
  ∃ b ∈ s.lsites, b.site.tgt.name = n ∧
    (b.site.tgt.win σ (s.dw σ)).2.1 ≤ p ∧
      p < (b.site.tgt.win σ (s.dw σ)).2.1 + (b.site.tgt.win σ (s.dw σ)).2.2

instance (s : Summary) (σ : String → Int) (n : String) (p : Nat) : Decidable (s.SrcPlain σ n p) := by
  unfold SrcPlain
  infer_instance

theorem SrcPlain.srcS {s : Summary} {σ : String → Int} {n : String} {p : Nat}
    (hp : ∀ a ∈ s.lsites, a.hdrs = []) (h : s.SrcPlain σ n p) : s.SrcS σ n p := by
  rcases h with h | ⟨b, hb, hn, hw⟩
  · exact Or.inl h
  · refine Or.inr ⟨b, hb, hn, ?_⟩
    rw [hp b hb]
    exact hw

/-- `WidthObl` for a flat netlist (every site plain): the closed form. -/
theorem widthObl_of_plain (s : Summary) (σ : String → Int)
    (hp : ∀ a ∈ s.lsites, a.hdrs = [])
    (h : ∀ ls ∈ s.lsites,
      (skRhs (rhsOf ls.site.proc) ls.site.rds).WidthOk σ (s.dw σ) (ls.site.tgt.win σ (s.dw σ)).2.2) :
    s.WidthObl σ := by
  intro ls hls
  simp only [hp _ hls, Loops.all]
  exact h ls hls

/-- `BitReadObl` for a flat netlist (every site plain): the closed form. -/
theorem bitReadObl_of_plain (s : Summary) (σ : String → Int)
    (hp : ∀ a ∈ s.lsites, a.hdrs = [])
    (h : ∀ ls ∈ s.lsites, ∀ r ∈ ls.site.rds, accBitUpper (s.dw σ) σ r) :
    s.BitReadObl σ := by
  intro ls hls
  simp only [hp _ hls, Loops.all]
  exact h ls hls

/-- `CoverObl` for a flat netlist (every site plain): the closed form. -/
theorem coverObl_of_plain (s : Summary) (σ : String → Int)
    (hp : ∀ a ∈ s.lsites, a.hdrs = [])
    (h : ∀ ls ∈ s.lsites, ∀ r ∈ ls.site.rds, ∀ k, k < (r.win σ (s.dw σ)).2.2 →
      s.SrcPlain σ r.name ((r.win σ (s.dw σ)).2.1 + k)) :
    s.CoverObl σ := by
  intro ls hls
  simp only [hp _ hls, Loops.all]
  exact fun r hr k hk => SrcPlain.srcS hp (h ls hls r hr k hk)

end Summary
end CombView
end LeanModels.Sv

/-- info: 'LeanModels.Sv.CombView.Summary.SrcPlain.srcS' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombView.Summary.SrcPlain.srcS

/-- info: 'LeanModels.Sv.CombView.Summary.widthObl_of_plain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombView.Summary.widthObl_of_plain

/-- info: 'LeanModels.Sv.CombView.Summary.bitReadObl_of_plain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombView.Summary.bitReadObl_of_plain

/-- info: 'LeanModels.Sv.CombView.Summary.coverObl_of_plain' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombView.Summary.coverObl_of_plain
