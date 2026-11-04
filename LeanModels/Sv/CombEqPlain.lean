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

/-- `Sk.SelfOk` is decidable (structural recursion on the skeleton). -/
def Sk.decSelfOk (σ : String → Int) (dw : String → Nat) : (sk : Sk) → Decidable (sk.SelfOk σ dw)
  | .lit _ => inferInstanceAs (Decidable True)
  | .rd _ => inferInstanceAs (Decidable True)
  | .gate _ l r =>
      haveI := Sk.decSelfOk σ dw l
      haveI := Sk.decSelfOk σ dw r
      inferInstanceAs (Decidable (l.SelfOk σ dw ∧ r.SelfOk σ dw ∧ l.width σ dw = r.width σ dw))
  | .cat _ => inferInstanceAs (Decidable True)
  | .rep _ => inferInstanceAs (Decidable True)
  | .fill _ => inferInstanceAs (Decidable False)
  | .bnot a => Sk.decSelfOk σ dw a
  | .lnot a => Sk.decSelfOk σ dw a
  | .red _ a => Sk.decSelfOk σ dw a
  | .land l r =>
      haveI := Sk.decSelfOk σ dw l
      haveI := Sk.decSelfOk σ dw r
      inferInstanceAs (Decidable (l.SelfOk σ dw ∧ r.SelfOk σ dw))
  | .lor l r =>
      haveI := Sk.decSelfOk σ dw l
      haveI := Sk.decSelfOk σ dw r
      inferInstanceAs (Decidable (l.SelfOk σ dw ∧ r.SelfOk σ dw))
  | .tern c a b =>
      haveI := Sk.decSelfOk σ dw c
      haveI := Sk.decSelfOk σ dw a
      haveI := Sk.decSelfOk σ dw b
      inferInstanceAs (Decidable (c.SelfOk σ dw ∧ c.width σ dw = 1 ∧ a.SelfOk σ dw ∧ b.SelfOk σ dw ∧
        a.width σ dw = b.width σ dw))
  | .cmp _ l r =>
      haveI := Sk.decSelfOk σ dw l
      haveI := Sk.decSelfOk σ dw r
      inferInstanceAs (Decidable (l.SelfOk σ dw ∧ r.SelfOk σ dw ∧ l.width σ dw = r.width σ dw))
  | .ext _ => inferInstanceAs (Decidable False)
  | .add _ _ => inferInstanceAs (Decidable False)
  | .sub _ _ => inferInstanceAs (Decidable False)
  | .mul _ _ => inferInstanceAs (Decidable False)
  | .const _ => inferInstanceAs (Decidable False)
  | .cref _ => inferInstanceAs (Decidable False)
  | .rsz _ _ => inferInstanceAs (Decidable False)
  | .sh _ _ _ _ => inferInstanceAs (Decidable False)

instance (σ : String → Int) (dw : String → Nat) (sk : Sk) : Decidable (sk.SelfOk σ dw) :=
  Sk.decSelfOk σ dw sk

/-- `Sk.WidthOk` is decidable (structural recursion on the skeleton). -/
def Sk.decWidthOk (σ : String → Int) (dw : String → Nat) (tw : Nat) : (sk : Sk) → Decidable (sk.WidthOk σ dw tw)
  | .lit v => inferInstanceAs (Decidable (v.width = tw))
  | .rd a => inferInstanceAs (Decidable ((a.win σ dw).2.2 = tw))
  | .gate _ l r =>
      haveI := Sk.decWidthOk σ dw tw l
      haveI := Sk.decWidthOk σ dw tw r
      inferInstanceAs (Decidable (l.WidthOk σ dw tw ∧ r.WidthOk σ dw tw))
  | .cat ps => inferInstanceAs (Decidable ((ps.map (Part.wid σ dw)).sum = tw))
  | .rep p => inferInstanceAs (Decidable (p.wid σ dw = tw))
  | .fill _ => inferInstanceAs (Decidable True)
  | .bnot a => Sk.decWidthOk σ dw tw a
  | .lnot a => inferInstanceAs (Decidable (tw = 1 ∧ a.SelfOk σ dw))
  | .red _ a => inferInstanceAs (Decidable (tw = 1 ∧ a.SelfOk σ dw))
  | .land l r => inferInstanceAs (Decidable (tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw))
  | .lor l r => inferInstanceAs (Decidable (tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw))
  | .tern c a b =>
      haveI := Sk.decWidthOk σ dw tw a
      haveI := Sk.decWidthOk σ dw tw b
      inferInstanceAs (Decidable (c.SelfOk σ dw ∧ c.width σ dw = 1 ∧ a.WidthOk σ dw tw ∧
        b.WidthOk σ dw tw))
  | .cmp _ l r =>
      inferInstanceAs (Decidable (tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw ∧ l.width σ dw = r.width σ dw))
  | .ext _ => inferInstanceAs (Decidable False)
  | .add _ _ => inferInstanceAs (Decidable False)
  | .sub _ _ => inferInstanceAs (Decidable False)
  | .mul _ _ => inferInstanceAs (Decidable False)
  | .const _ => inferInstanceAs (Decidable False)
  | .cref _ => inferInstanceAs (Decidable False)
  | .rsz _ _ => inferInstanceAs (Decidable False)
  | .sh _ _ _ _ => inferInstanceAs (Decidable False)

instance (σ : String → Int) (dw : String → Nat) (tw : Nat) (sk : Sk) : Decidable (sk.WidthOk σ dw tw) :=
  Sk.decWidthOk σ dw tw sk

/-- The truncation-marker part of the contract is decidable. -/
def Sk.decRok (σ : String → Int) (dw : String → Nat) (tw : Nat) : (sk : Sk) → Decidable (sk.rok σ dw tw)
  | .lit _ => inferInstanceAs (Decidable True)
  | .rd _ => inferInstanceAs (Decidable True)
  | .gate _ l r =>
      haveI := Sk.decRok σ dw tw l
      haveI := Sk.decRok σ dw tw r
      inferInstanceAs (Decidable (l.rok σ dw tw ∧ r.rok σ dw tw))
  | .cat _ => inferInstanceAs (Decidable True)
  | .rep _ => inferInstanceAs (Decidable True)
  | .fill _ => inferInstanceAs (Decidable True)
  | .bnot a => Sk.decRok σ dw tw a
  | .lnot _ => inferInstanceAs (Decidable True)
  | .red _ _ => inferInstanceAs (Decidable True)
  | .land _ _ => inferInstanceAs (Decidable True)
  | .lor _ _ => inferInstanceAs (Decidable True)
  | .tern _ a b =>
      haveI := Sk.decRok σ dw tw a
      haveI := Sk.decRok σ dw tw b
      inferInstanceAs (Decidable (a.rok σ dw tw ∧ b.rok σ dw tw))
  | .cmp _ _ _ => inferInstanceAs (Decidable True)
  | .ext _ => inferInstanceAs (Decidable True)
  | .add l r =>
      haveI := Sk.decRok σ dw tw l
      haveI := Sk.decRok σ dw tw r
      inferInstanceAs (Decidable (l.rok σ dw tw ∧ r.rok σ dw tw))
  | .sub l r =>
      haveI := Sk.decRok σ dw tw l
      haveI := Sk.decRok σ dw tw r
      inferInstanceAs (Decidable (l.rok σ dw tw ∧ r.rok σ dw tw))
  | .mul l r =>
      haveI := Sk.decRok σ dw tw l
      haveI := Sk.decRok σ dw tw r
      inferInstanceAs (Decidable (l.rok σ dw tw ∧ r.rok σ dw tw))
  | .const _ => inferInstanceAs (Decidable True)
  | .cref _ => inferInstanceAs (Decidable True)
  | .rsz _ p => inferInstanceAs (Decidable ((p.rmax σ dw).getD 0 ≤ tw))
  | .sh _ _ l _ => inferInstanceAs (Decidable (l.width σ dw ≤ tw))

instance (σ : String → Int) (dw : String → Nat) (tw : Nat) (sk : Sk) : Decidable (sk.rok σ dw tw) :=
  Sk.decRok σ dw tw sk

/-- `Sk.WidthOkC` (the word-level width contract) is decidable (structural recursion on the skeleton; the context
width changes under a comparison and a marker, so it is an argument of the recursion). -/
def Sk.decWidthOkC (σ : String → Int) (dw : String → Nat) :
    (sk : Sk) → (tw : Nat) → Decidable (sk.WidthOkC σ dw tw)
  | .lit v, tw => inferInstanceAs (Decidable (v.width = tw))
  | .rd a, tw => inferInstanceAs (Decidable ((a.win σ dw).2.2 = tw))
  | .gate _ l r, tw =>
      haveI := Sk.decWidthOkC σ dw l tw
      haveI := Sk.decWidthOkC σ dw r tw
      inferInstanceAs (Decidable (l.WidthOkC σ dw tw ∧ r.WidthOkC σ dw tw))
  | .cat ps, tw => inferInstanceAs (Decidable ((ps.map (Part.wid σ dw)).sum = tw))
  | .rep p, tw => inferInstanceAs (Decidable (p.wid σ dw = tw))
  | .fill _, _ => inferInstanceAs (Decidable True)
  | .bnot a, tw =>
      haveI := Sk.decWidthOkC σ dw a tw
      inferInstanceAs (Decidable (a.WidthOkC σ dw tw ∧ a.rok σ dw tw))
  | .lnot a, tw => inferInstanceAs (Decidable (tw = 1 ∧ a.SelfOk σ dw))
  | .red _ a, tw => inferInstanceAs (Decidable (tw = 1 ∧ a.SelfOk σ dw))
  | .land l r, tw => inferInstanceAs (Decidable (tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw))
  | .lor l r, tw => inferInstanceAs (Decidable (tw = 1 ∧ l.SelfOk σ dw ∧ r.SelfOk σ dw))
  | .tern c a b, tw =>
      haveI := Sk.decWidthOkC σ dw a tw
      haveI := Sk.decWidthOkC σ dw b tw
      inferInstanceAs (Decidable (c.SelfOk σ dw ∧ c.width σ dw = 1 ∧ a.WidthOkC σ dw tw ∧
        b.WidthOkC σ dw tw))
  | .cmp _ l r, tw =>
      haveI := Sk.decWidthOkC σ dw l (max (l.width σ dw) (r.width σ dw))
      haveI := Sk.decWidthOkC σ dw r (max (l.width σ dw) (r.width σ dw))
      inferInstanceAs (Decidable (tw = 1 ∧ l.WidthOkC σ dw (max (l.width σ dw) (r.width σ dw)) ∧
        r.WidthOkC σ dw (max (l.width σ dw) (r.width σ dw))))
  | .ext q, tw => inferInstanceAs (Decidable (q.wid σ dw ≤ tw))
  | .add l r, tw =>
      haveI := Sk.decWidthOkC σ dw l tw
      haveI := Sk.decWidthOkC σ dw r tw
      inferInstanceAs (Decidable (l.WidthOkC σ dw tw ∧ r.WidthOkC σ dw tw ∧ l.rok σ dw tw ∧ r.rok σ dw tw))
  | .sub l r, tw =>
      haveI := Sk.decWidthOkC σ dw l tw
      haveI := Sk.decWidthOkC σ dw r tw
      inferInstanceAs (Decidable (l.WidthOkC σ dw tw ∧ r.WidthOkC σ dw tw ∧ l.rok σ dw tw ∧ r.rok σ dw tw))
  | .mul l r, tw =>
      haveI := Sk.decWidthOkC σ dw l tw
      haveI := Sk.decWidthOkC σ dw r tw
      inferInstanceAs (Decidable (l.WidthOkC σ dw tw ∧ r.WidthOkC σ dw tw ∧ l.rok σ dw tw ∧ r.rok σ dw tw))
  | .const _, _ => inferInstanceAs (Decidable True)
  | .cref _, _ => inferInstanceAs (Decidable True)
  | .rsz true p, tw =>
      haveI := Sk.decWidthOkC σ dw p tw
      haveI := Sk.decWidthOkC σ dw p (p.width σ dw)
      inferInstanceAs (Decidable (if p.width σ dw < tw then p.WidthOkC σ dw tw
        else p.WidthOkC σ dw (p.width σ dw)))
  | .rsz false p, _ =>
      haveI := Sk.decWidthOkC σ dw p (p.width σ dw)
      inferInstanceAs (Decidable (p.WidthOkC σ dw (p.width σ dw)))
  | .sh _ _ l r, _ =>
      haveI := Sk.decWidthOkC σ dw l (l.width σ dw)
      haveI := Sk.decWidthOkC σ dw r (r.width σ dw)
      inferInstanceAs (Decidable (l.WidthOkC σ dw (l.width σ dw) ∧ r.WidthOkC σ dw (r.width σ dw)))

instance (σ : String → Int) (dw : String → Nat) (tw : Nat) (sk : Sk) : Decidable (sk.WidthOkC σ dw tw) :=
  Sk.decWidthOkC σ dw sk tw

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
    (hp : ∀ a ∈ s.lsites, a.hdrs.isEmpty = true)
    (h : ∀ ls ∈ s.lsites,
      (skRhs (rhsOf ls.site.proc) ls.site.rds).WidthOkC σ (s.dw σ) (ls.site.tgt.win σ (s.dw σ)).2.2) :
    s.WidthObl σ := by
  intro ls hls
  simp only [List.isEmpty_iff.mp (hp _ hls), Loops.all]
  exact h ls hls

/-- `BitReadObl` for a flat netlist (every site plain): the closed form. -/
theorem bitReadObl_of_plain (s : Summary) (σ : String → Int)
    (hp : ∀ a ∈ s.lsites, a.hdrs.isEmpty = true)
    (h : ∀ ls ∈ s.lsites, ∀ r ∈ ls.site.rds, accBitUpper (s.dw σ) σ r) :
    s.BitReadObl σ := by
  intro ls hls
  simp only [List.isEmpty_iff.mp (hp _ hls), Loops.all]
  exact h ls hls

/-- `CoverObl` for a flat netlist (every site plain): the closed form. -/
theorem coverObl_of_plain (s : Summary) (σ : String → Int)
    (hp : ∀ a ∈ s.lsites, a.hdrs.isEmpty = true)
    (h : ∀ ls ∈ s.lsites, ∀ r ∈ ls.site.rds, ∀ k, k < (r.win σ (s.dw σ)).2.2 →
      s.SrcPlain σ r.name ((r.win σ (s.dw σ)).2.1 + k)) :
    s.CoverObl σ := by
  intro ls hls
  simp only [List.isEmpty_iff.mp (hp _ hls), Loops.all]
  exact fun r hr k hk => SrcPlain.srcS (fun a ha => List.isEmpty_iff.mp (hp a ha)) (h ls hls r hr k hk)

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

/-- info: 'LeanModels.Sv.CombView.Summary.coverObl_of_plain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombView.Summary.coverObl_of_plain
