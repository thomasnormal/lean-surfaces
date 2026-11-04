import LeanModels.Sv.CombProcEq
import LeanModels.Sv.CombEqGroup
import LeanModels.Sv.PinAxioms

/-!
# Grouping the coverage obligation of a body of several windows by signal name (WP-LIN)

`CombEqGroup.lean` restricts `CoverObl` to the writers of the signal each read observes. `Summary.CoverOblM` (the form for
designs where some `always_comb` body writes several windows) asks for a source in THREE places: an input bit, a head window
of some site, or a FURTHER window of some site (`SrcSM`). The same restriction applies to the last two: only sites whose head
window is the read's signal, and only sites with a further window of that signal, can be the source.

`rdWritersM l` lists, for every site and every read, the two groups; `coverOblM_of_groups` is `CoverOblM` with `SrcSM`'s two
existentials asked over them (the body of `SrcSM` itself, so no new name reaches the normalizer). The list is computed by the
tactic and checked by the kernel with `rfl`, as for the other obligations (`CombViewGroup.lean`).
-/

namespace LeanModels.Sv
namespace CombView

/-- Every site with its reads, each read with the sites whose head window is its signal and the sites with a further window
of its signal (in site order). -/
def rdWritersM (l : List LSite) : List (LSite × List (Acc × List LSite × List LSite)) :=
  l.map fun a => (a, a.site.rds.map fun r =>
    (r, l.filter (fun b => b.site.tgt.name == r.name),
      l.filter (fun b => b.site.more.any fun y => y.name == r.name)))

namespace Summary
open LeanModels.Sv.CombEq

/-- **The coverage obligation of a body of several windows, grouped by signal.** `RW` is `rdWritersM s.lsites` (`hRW` by `rfl`). -/
theorem coverOblM_of_groups (s : Summary) (σ : String → Int)
    (RW : List (LSite × List (Acc × List LSite × List LSite)))
    (hRW : rdWritersM s.lsites = RW)
    (h : ∀ e ∈ RW, Loops.all e.1.hdrs σ fun σ' =>
      ∀ q ∈ e.2, ∀ k, k < (q.1.win σ' (s.dw σ)).2.2 →
        (((q.1.name ∈ s.inputNames ∧ (q.1.win σ' (s.dw σ)).2.1 + k < s.dw σ q.1.name) ∨
          ∃ b ∈ q.2.1, b.site.tgt.name = q.1.name ∧
            LoopsE b.hdrs σ fun σ2 =>
              (b.site.tgt.win σ2 (s.dw σ)).2.1 ≤ (q.1.win σ' (s.dw σ)).2.1 + k ∧
                (q.1.win σ' (s.dw σ)).2.1 + k <
                  (b.site.tgt.win σ2 (s.dw σ)).2.1 + (b.site.tgt.win σ2 (s.dw σ)).2.2) ∨
          ∃ b ∈ q.2.2, ∃ a ∈ b.site.more, a.name = q.1.name ∧
            LoopsE b.hdrs σ fun σ2 =>
              (a.win σ2 (s.dw σ)).2.1 ≤ (q.1.win σ' (s.dw σ)).2.1 + k ∧
                (q.1.win σ' (s.dw σ)).2.1 + k <
                  (a.win σ2 (s.dw σ)).2.1 + (a.win σ2 (s.dw σ)).2.2)) :
    s.CoverOblM σ := by
  subst hRW
  intro ls hls
  have he := h (ls, ls.site.rds.map fun r => (r, s.lsites.filter (fun b => b.site.tgt.name == r.name),
      s.lsites.filter (fun b => b.site.more.any fun y => y.name == r.name)))
    (List.mem_map.2 ⟨ls, hls, rfl⟩)
  rw [Loops.all_iff] at he ⊢
  intro σ' hr r hrm k hk
  have h1 := he σ' hr (r, s.lsites.filter (fun b => b.site.tgt.name == r.name),
      s.lsites.filter (fun b => b.site.more.any fun y => y.name == r.name))
    (List.mem_map.2 ⟨r, hrm, rfl⟩) k hk
  unfold Summary.SrcSM
  rcases h1 with (h1 | ⟨b, hb, hn, hl⟩) | ⟨b, hb, a, ha, hn, hl⟩
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr ⟨b, (List.mem_filter.1 hb).1, hn, hl⟩)
  · exact Or.inr ⟨b, (List.mem_filter.1 hb).1, a, ha, hn, hl⟩

end Summary

end CombView
end LeanModels.Sv

#pin_axioms LeanModels.Sv.CombView.rdWritersM LeanModels.Sv.CombView.Summary.coverOblM_of_groups
