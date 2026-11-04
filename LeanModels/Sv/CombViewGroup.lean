import LeanModels.Sv.CombViewThm
import LeanModels.Sv.PinAxioms

/-!
# Grouping the two quadratic structure obligations by signal name (WP-LIN)

`Summary.DisjObl` (one driver per bit) and `Summary.RankObl'` (the rank decreases along every read) are the two
obligations of `sv_structure` whose normalization by `simp` grows quadratically in the number of sites
(measured, thousands of heartbeats, a parametric chain of `n` plain sites: `driverDisjoint` 16 187 / 45 372 / 161 430 and
`rankDecreases` 35 726 / 112 829 / 403 666 at `n` = 11 / 21 / 41, while `autoObl` and `inRangeObl` are linear):
`DisjObl` states `DisjOne` for EVERY pair of sites (`List.Pairwise`), `RankObl'` visits, for every read, a filter of ALL
sites (`writersOf`). Both only matter between sites that write the SAME signal: two windows of different signals do not
overlap, whatever their loops and indices.

This file states the grouping and proves it once.

* `sameNamePairs l`: the pairs `(a, b)` of `List.Pairwise`'s enumeration (`a` before `b` in `l`) whose target signals agree,
  in the same order. `pairwise_of_sameNamePairs`: `Pairwise R l` follows from `R` on those pairs when `R` holds for every
  two sites that write different signals; `disjOne_of_ne_name` says `DisjOne` does.
* `rdWriters l`: every site with its reads, each read with the sites that write the signal it reads, in the nesting
  of `RankObl'`'s quantifiers (and of `CoverObl`'s, `CombEqGroup.lean`).

`Summary.disjObl_of_groups` and `Summary.rankObl'_of_groups` take the explicit list the tactic computed (the list is
equal to `sameNamePairs s.lsites` / `rdWriters s.lsites` by `rfl`: the kernel checks it once) and ask for the original
obligation restricted to that list. The tactic hands THAT to the normalization, so the work is linear in the number of
related pairs, which is the number of reads: the goals that come out are the ones the old route produced (a pair of sites
of different signals normalized to `True` and left no goal), in the same order. The rank obligation keeps its nesting (site,
read, writer) rather than a flat list of triples: a site that reads the same bit twice then still normalizes to the same
conjunct twice side by side, which `simp` merges, exactly as before (a flat list kept both copies: measured on
`Examples/system-verilog/ripple_add/neg`).
-/

namespace LeanModels.Sv
namespace CombView

/-- The pairs of sites, in the order `List.Pairwise` visits them, whose target signals agree. -/
def sameNamePairs : List LSite → List (LSite × LSite)
  | [] => []
  | a :: rest =>
      (rest.filter fun b => b.site.tgt.name == a.site.tgt.name).map (fun b => (a, b)) ++ sameNamePairs rest

theorem pairwise_of_sameNamePairs {R : LSite → LSite → Prop}
    (hne : ∀ a b : LSite, a.site.tgt.name ≠ b.site.tgt.name → R a b) :
    ∀ l : List LSite, (∀ p ∈ sameNamePairs l, R p.1 p.2) → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | a :: rest, h => by
      rw [List.pairwise_cons]
      refine ⟨fun b hb => ?_,
        pairwise_of_sameNamePairs hne rest fun p hp => h p (List.mem_append_right _ hp)⟩
      by_cases hn : b.site.tgt.name = a.site.tgt.name
      · refine h (a, b) ?_
        simp only [sameNamePairs, List.mem_append, List.mem_map, List.mem_filter]
        exact Or.inl ⟨b, ⟨hb, by simpa using hn⟩, rfl⟩
      · exact hne a b fun h' => hn h'.symm

/-- The signal of an accessor's window is its name (`Acc.win_name` of `CombViewMain`, restated here to stay below it). -/
theorem win_fst_eq_name (σ : String → Int) (dw : String → Nat) (a : Acc) : (a.win σ dw).1 = a.name := by
  cases a <;> rfl

/-- Two windows of different signals never overlap. -/
theorem overlaps_eq_false_of_ne {w w' : Win} (h : w.1 ≠ w'.1) : Win.overlaps w w' = false := by
  obtain ⟨n, lo, k⟩ := w
  obtain ⟨n', lo', k'⟩ := w'
  exact Win.overlaps_eq_false.mpr (Or.inl h)

namespace Summary

/-- Two sites that write different signals drive disjoint bits, at every pair of loop valuations. -/
theorem disjOne_of_ne_name (s : Summary) (σ : String → Int) {a b : LSite}
    (h : a.site.tgt.name ≠ b.site.tgt.name) : s.DisjOne σ a b := by
  unfold Summary.DisjOne
  rw [Loops.all_iff]
  intro σ1 _
  rw [Loops.all_iff]
  intro σ2 _ _
  apply overlaps_eq_false_of_ne
  rw [win_fst_eq_name, win_fst_eq_name]
  exact h

/-- **One driver per bit, grouped by signal.** `P` is `sameNamePairs s.lsites` (the tactic computes it and the kernel checks
`hP` by `rfl`); the obligation is `DisjOne` on the pairs of `P`, `DisjOne` of each site with itself, and the guarded
conjunct for bodies of several windows, exactly as `DisjObl` states them. -/
theorem disjObl_of_groups (s : Summary) (σ : String → Int) (P : List (LSite × LSite))
    (hP : sameNamePairs s.lsites = P)
    (h : (∀ p ∈ P, s.DisjOne σ p.1 p.2) ∧ (∀ a ∈ s.lsites, s.DisjOne σ a a) ∧
      (if (∀ b ∈ s.lsites, b.site.more = []) then True else
        (∀ a ∈ s.lsites, ∀ b ∈ s.lsites, ∀ y ∈ b.site.more, ∀ x ∈ a.site.tgt :: a.site.more,
          Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
            a.id σ1 ≠ b.id σ2 →
              Win.overlaps (x.win σ1 (s.dw σ)) (y.win σ2 (s.dw σ)) = false) ∧
        (∀ a ∈ s.lsites, Loops.all a.hdrs σ fun σ1 =>
          (a.site.tgt :: a.site.more).Pairwise fun x y =>
            Win.overlaps (x.win σ1 (s.dw σ)) (y.win σ1 (s.dw σ)) = false))) :
    s.DisjObl σ := by
  subst hP
  exact ⟨pairwise_of_sameNamePairs (fun a b hne => s.disjOne_of_ne_name σ hne) _ h.1, h.2.1, h.2.2⟩

end Summary

/-- The reads of each site, each with the sites that write the signal it reads (in site order). The nesting is the one of
`RankObl'` and `CoverObl`: a site, then its reads, then the writers of the signal a read observes. -/
def rdWriters (l : List LSite) : List (LSite × List (Acc × List LSite)) :=
  l.map fun a => (a, a.site.rds.map fun r => (r, l.filter fun b => b.site.tgt.name == r.name))

namespace Summary

/-- **The rank obligation, grouped by signal.** `RW` is `rdWriters s.lsites` (`hRW` by `rfl`); the first conjunct of `RankObl'`
is asked of the writers of each read only (the nesting of the original: site, read, writer), the guarded conjunct for bodies
of several windows is stated as `RankObl'` states it. -/
theorem rankObl'_of_groups (s : Summary) (R : SiteId → SiteId → Prop) (σ : String → Int)
    (RW : List (LSite × List (Acc × List LSite))) (hRW : rdWriters s.lsites = RW)
    (h : (∀ e ∈ RW, ∀ q ∈ e.2, ∀ b ∈ q.2,
          Loops.all e.1.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
            ReadWin.overlaps (q.1.rd σ1) (b.site.tgt.win σ2 (s.dw σ)) = true → R (b.id σ2) (e.1.id σ1)) ∧
      (if (∀ b ∈ s.lsites, b.site.more = []) then True else
        ∀ b ∈ s.lsites, ∀ y ∈ b.site.more, ∀ a ∈ s.lsites, ∀ r ∈ a.site.rds, y.name = r.name →
          Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
            ReadWin.overlaps (r.rd σ1) (y.win σ2 (s.dw σ)) = true → R (b.id σ2) (a.id σ1))) :
    s.RankObl' R σ := by
  subst hRW
  refine ⟨fun a ha r hr b hb => ?_, h.2⟩
  have hb' := hb
  unfold Summary.writersOf at hb'
  exact h.1 (a, a.site.rds.map fun r => (r, s.lsites.filter fun b => b.site.tgt.name == r.name))
    (List.mem_map.2 ⟨a, ha, rfl⟩) (r, s.lsites.filter fun b => b.site.tgt.name == r.name)
    (List.mem_map.2 ⟨r, hr, rfl⟩) b hb'

end Summary

end CombView
end LeanModels.Sv

#pin_axioms LeanModels.Sv.CombView.sameNamePairs LeanModels.Sv.CombView.pairwise_of_sameNamePairs
  LeanModels.Sv.CombView.win_fst_eq_name LeanModels.Sv.CombView.overlaps_eq_false_of_ne
  LeanModels.Sv.CombView.Summary.disjOne_of_ne_name LeanModels.Sv.CombView.Summary.disjObl_of_groups
  LeanModels.Sv.CombView.rdWriters LeanModels.Sv.CombView.Summary.rankObl'_of_groups
