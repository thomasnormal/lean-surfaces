import LeanModels.Sv.CombEqThm
import LeanModels.Sv.CombViewGroup
import LeanModels.Sv.PinAxioms

/-!
# Grouping the coverage obligation by signal name (WP-LIN)

`Summary.CoverObl` says that every bit a read observes has a source, and `SrcS σ n p` looks for that source among ALL sites
(`∃ b ∈ s.lsites, b.site.tgt.name = n ∧ …`): for every read, a disjunction over every site of the design, only the
writers of `n` of which survive the name test. Normalized by `simp` that is quadratic in the number of sites (reads times
sites; measured at a parametric chain of `n` plain sites: `cover` 52 400 / 146 150 thousand heartbeats at `n` = 11 / 21, and
beyond that the whole obligation runs out of `simp` steps and the goals come out in the site-witness form).

`coverObl_of_groups` states `CoverObl` for the explicit list `RW` the tactic computed (`rdWriters s.lsites`, checked by
`rfl` once, by the kernel): every site with its reads, each read with the writers of the signal it reads. The source of a
bit is asked of that list of writers only, in the body of `SrcS` itself (no new name reaches the normalizer: the goal is
`SrcS` with `s.lsites` replaced by the list of writers, and a site of another signal was `False` there anyway). The nesting of
`CoverObl` is kept (the loops of a site enclose all its reads), so the goals that come out are the ones the old route produced.
-/

namespace LeanModels.Sv
namespace CombView

namespace Summary
open LeanModels.Sv.CombEq

/-- **The coverage obligation, grouped by signal.** `RW` is `rdWriters s.lsites` (`hRW` by `rfl`); the source of a bit is
searched among the writers of its signal (the body of `SrcS`, over that list). -/
theorem coverObl_of_groups (s : Summary) (σ : String → Int) (RW : List (LSite × List (Acc × List LSite)))
    (hRW : rdWriters s.lsites = RW)
    (h : ∀ e ∈ RW, Loops.all e.1.hdrs σ fun σ' =>
      ∀ q ∈ e.2, ∀ k, k < (q.1.win σ' (s.dw σ)).2.2 →
        ((q.1.name ∈ s.inputNames ∧ (q.1.win σ' (s.dw σ)).2.1 + k < s.dw σ q.1.name) ∨
          ∃ b ∈ q.2, b.site.tgt.name = q.1.name ∧
            LoopsE b.hdrs σ fun σ2 =>
              (b.site.tgt.win σ2 (s.dw σ)).2.1 ≤ (q.1.win σ' (s.dw σ)).2.1 + k ∧
                (q.1.win σ' (s.dw σ)).2.1 + k <
                  (b.site.tgt.win σ2 (s.dw σ)).2.1 + (b.site.tgt.win σ2 (s.dw σ)).2.2)) :
    s.CoverObl σ := by
  subst hRW
  intro ls hls
  have he := h (ls, ls.site.rds.map fun r => (r, s.lsites.filter fun b => b.site.tgt.name == r.name))
    (List.mem_map.2 ⟨ls, hls, rfl⟩)
  rw [Loops.all_iff] at he ⊢
  intro σ' hr r hrm k hk
  have h1 := he σ' hr (r, s.lsites.filter fun b => b.site.tgt.name == r.name)
    (List.mem_map.2 ⟨r, hrm, rfl⟩) k hk
  rcases h1 with h1 | ⟨b, hb, hn, hl⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b, (List.mem_filter.1 hb).1, hn, hl⟩

end Summary

end CombView
end LeanModels.Sv

#pin_axioms LeanModels.Sv.CombView.Summary.coverObl_of_groups
