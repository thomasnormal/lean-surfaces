import LeanModels.Sv.CombViewMain

/-!
# The obligations the two stages share: `SharedObl` (perf, 2026-11-04)

`sv_structure` and `sv_equations` both need the summary's `auto` obligation (the parameters' affine facts, every read
inside its declared vector) and its `inRange` obligation (every write window inside its vector): the soundness theorems
of both stages take them as hypotheses. Proved separately, the two tactics normalize them twice; measured on the
references (thousands of heartbeats, `sv_comb.profile`), the second time is fdivp 104 of 2 282, Newton 139 of 1 891,
mul_tree 78 of 772, add_n 19 of 134 (5 to 14% of the file).

`SharedObl d args` states the two once, for the design family `d` (`X.pdesign`) at the arguments `args` (the `Int` list
`X.sem N` instantiates, `[N]`). `sv_structure` proves it as a THIRD conjunct when the goal asks for it,

    theorem fdiv_struct … : CombDesign (design.sem W P) ∧ Acyclic (design.sem W P) ∧ SharedObl design.pdesign [W, P]

(`comb_acyclic_shared_view`, `comb_lex_shared_view`: the same obligations as the bundle `CombDesign ∧ Acyclic`, and the
two of them packaged), and `sv_equations` reads a `SharedObl` hypothesis of the design from the context instead of
normalizing `auto` and `inRange` again (it returns no `auto_k`/`inRange_k` goals then). Without it both tactics behave
as before: opt-in, nothing else changes.
-/

namespace LeanModels.Sv.CombView

/-- **The obligations `sv_structure` and `sv_equations` share** (module docstring): `auto` and `inRange` of the summary of
`d`, at the arguments `args`. -/
def SharedObl (d : PDesign) (args : List Int) : Prop :=
  ∀ s, d.summary = .ok s → s.AutoObl (s.val args) args ∧ s.InRangeObl (s.val args)

theorem SharedObl.auto {d : PDesign} {args : List Int} (h : SharedObl d args) {s : Summary}
    (hs : d.summary = .ok s) : s.AutoObl (s.val args) args :=
  (h s hs).1

theorem SharedObl.inRange {d : PDesign} {args : List Int} (h : SharedObl d args) {s : Summary}
    (hs : d.summary = .ok s) : s.InRangeObl (s.val args) :=
  (h s hs).2

theorem sharedObl_of {d : PDesign} {s : Summary} {args : List Int} (hs : d.summary = .ok s)
    (hauto : s.AutoObl (s.val args) args) (hin : s.InRangeObl (s.val args)) : SharedObl d args := by
  intro s' hs'
  have h := hs.symm.trans hs'
  injection h with h
  subst h
  exact ⟨hauto, hin⟩

/-- `comb_acyclic_view`, and the shared obligations packaged (`sv_structure` on the triple). -/
theorem comb_acyclic_shared_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (ρ : SiteId → Nat) (hrank : s.RankObl ρ (s.val args)) :
    CombDesign (d.instantiateGD2 args) ∧ Acyclic (d.instantiateGD2 args) ∧ SharedObl d args :=
  let h := comb_acyclic_view hs harity h1 hag hok hauto hin hdisj ρ hrank
  ⟨h.1, h.2, sharedObl_of hs hauto hin⟩

/-- … with a lexicographic key. -/
theorem comb_lex_shared_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (κ : SiteId → Key) (hrank : s.LexObl κ (s.val args)) :
    CombDesign (d.instantiateGD2 args) ∧ Acyclic (d.instantiateGD2 args) ∧ SharedObl d args :=
  let h := comb_lex_view hs harity h1 hag hok hauto hin hdisj κ hrank
  ⟨h.1, h.2, sharedObl_of hs hauto hin⟩

end LeanModels.Sv.CombView
