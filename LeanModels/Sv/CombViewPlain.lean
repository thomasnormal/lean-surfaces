import LeanModels.Sv.CombViewThm

/-!
# Flat netlists: the two quadratic structure obligations as closed statements (WP-P3b)

`Summary.DisjObl` (one driver per bit) and `Summary.RankObl'` (the rank decreases along every read) are
stated over the generate loops of each site (`Loops.all hdrs σ …`). The tactic `sv_structure` normalizes
them with `simp`, which unfolds `List.pairwise_cons` into one goal per PAIR of sites and `writersOf` (a
`List.filter` over all sites) once per read: quadratic in the number of sites, and for a flat netlist of
113 gates (`aes_sbox`, Boyar-Peralta) it runs out of time before it produces a goal
(`svgolf/PROVING.md`, section 12).

When EVERY site is plain (`hdrs = []`, no generate loop) the loops vanish, and both obligations are
closed, decidable statements about the site list with no loop index: for a design without a free
parameter the kernel decides them (the tactic assigns `of_decide_eq_true _ _ (Eq.refl true)` after
evaluating the decision natively, `closeByDecide`). These two lemmas are that reduction. They are the
ones `svgolf/tasks/aes_sbox/reference/sbox_bp.lean` carried as `disjObl_plain` / `rankObl_plain`;
`rankObl'_of_plain` is stated for an arbitrary relation `R`, so one lemma serves the `Nat` rank
(`RankObl`) and the lexicographic key (`LexObl`).

A design WITH a generate loop is untouched: `sv_structure` keeps normalizing its obligations as before.
-/

namespace LeanModels.Sv
namespace CombView
namespace Summary

/-- **One driver per bit, for a flat netlist** (every site plain): the pairwise window check as one
closed fact about the site list, instead of one simp-normalised obligation per pair. -/
theorem disjObl_of_plain (s : Summary) (σ : String → Int)
    (hp : ∀ a ∈ s.lsites, a.hdrs = [])
    (h : s.lsites.Pairwise (fun a b => a.id σ ≠ b.id σ →
        Win.overlaps (a.site.tgt.win σ (s.dw σ)) (b.site.tgt.win σ (s.dw σ)) = false)) :
    s.DisjObl σ := by
  refine ⟨List.Pairwise.imp_of_mem (fun ha hb hab => ?_) h, fun a ha => ?_⟩
  · simp only [Summary.DisjOne, hp _ ha, hp _ hb, Loops.all]
    exact hab
  · simp only [Summary.DisjOne, hp _ ha, Loops.all]
    exact fun hne => absurd rfl hne

/-- **The rank decreases along every read, for a flat netlist** (every site plain): for every read of
every site, every site writing that signal whose window the read overlaps is related by `R` to the
reader. A closed statement about the list of sites; `R` is `fun w r => ρ w < ρ r` for `RankObl` and
`fun w r => KLt (κ w) (κ r)` for `LexObl`. -/
theorem rankObl'_of_plain (s : Summary) (R : SiteId → SiteId → Prop) (σ : String → Int)
    (hp : ∀ a ∈ s.lsites, a.hdrs = [])
    (h : ∀ a ∈ s.lsites, ∀ r ∈ a.site.rds, ∀ b ∈ s.writersOf r.name,
      ReadWin.overlaps (r.rd σ) (b.site.tgt.win σ (s.dw σ)) = true → R (b.id σ) (a.id σ)) :
    s.RankObl' R σ := by
  intro a ha r hr b hb
  have hb' := (List.mem_filter.1 hb).1
  simp only [hp _ ha, hp _ hb', Loops.all]
  exact h a ha r hr b hb

/-! ### The two linear obligations, for the same designs

`AutoObl` (reads in range, dimensions non-negative, loop bounds within the generate fuel) and
`InRangeObl` (every write window inside its declared signal) are linear in the number of sites, but the
`simp` normalization costs about 2 M heartbeats per site (152 M and 95 M of a 283 M proof at 113 sites),
which is most of a default `maxHeartbeats`. For a flat netlist without a free parameter they too are
closed decidable statements. (These instances are what lets the kernel run them.) -/

instance (s : Summary) (σ : String → Int) (a : Acc) : Decidable (s.DimNum σ a) := by
  unfold Summary.DimNum
  split <;> infer_instance

instance (s : Summary) (σd σs : String → Int) (a : Acc) : Decidable (s.InR σd σs a) := by
  unfold Summary.InR
  split <;> infer_instance

instance (s : Summary) (σd σs : String → Int) (st : TSite) : Decidable (s.InWin σd σs st) := by
  unfold Summary.InWin
  have : Decidable (match st.tgt with
      | .bit n a => a.eval σs + 1 ≤ (s.dw σd n : Int)
      | _ => True) := by
    split <;> infer_instance
  infer_instance

/-- `AutoObl` for a flat netlist (every site plain): the closed form. -/
theorem autoObl_of_plain (s : Summary) (σ : String → Int) (args : List Int)
    (hp : ∀ a ∈ s.lsites, a.hdrs = [])
    (h : (∀ ls ∈ s.lsites, ∀ r ∈ ls.site.rds, s.InR σ σ r) ∧
      (∀ ls ∈ s.lsites, ∀ a ∈ ls.site.tgt :: ls.site.rds, s.DimNum σ a) ∧
      (∀ p ∈ s.hdrPaths, ∀ h ∈ p, (h.bound.eval σ - h.c0).toNat ≤ 4 * (args.map Int.natAbs).sum + 60)) :
    s.AutoObl σ args := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun ls hls => ?_, h2, h3⟩
  simp only [hp _ hls, Loops.all]
  exact h1 ls hls

/-- `InRangeObl` for a flat netlist (every site plain): the closed form. -/
theorem inRangeObl_of_plain (s : Summary) (σ : String → Int)
    (hp : ∀ a ∈ s.lsites, a.hdrs = [])
    (h : ∀ ls ∈ s.lsites, s.InWin σ σ ls.site) : s.InRangeObl σ := by
  intro ls hls
  simp only [hp _ hls, Loops.all]
  exact h ls hls

end Summary
end CombView
end LeanModels.Sv

/-- info: 'LeanModels.Sv.CombView.Summary.disjObl_of_plain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombView.Summary.disjObl_of_plain

/-- info: 'LeanModels.Sv.CombView.Summary.rankObl'_of_plain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombView.Summary.rankObl'_of_plain

/-- info: 'LeanModels.Sv.CombView.Summary.autoObl_of_plain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombView.Summary.autoObl_of_plain

/-- info: 'LeanModels.Sv.CombView.Summary.inRangeObl_of_plain' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombView.Summary.inRangeObl_of_plain
