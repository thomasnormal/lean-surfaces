import LeanModels.Sv.Kernel.Core0Comb
import LeanModels.Sv.Comb2Proc
import LeanModels.Sv.NbaCommit

/-!
# E edge-process NBA targets

IEEE 1800-2023 §§10.4.2, 11.5.1: sample a packed element select when the
NBA is issued. Unknown, negative and out-of-range indices issue no update;
the RHS is still evaluated by the caller. The queued offset and value are
already fixed before the NBA region. No semantic fuel or AST rewriting.

Static targets retain their precise footprints. A runtime element select
reserves its whole declared signal (§11.5.3). The containment theorem is the
frame used by E's one-writer and no-clock-write checks. Dynamic concatenated
targets remain a loud boundary; static concatenations retain their rule.
-/

namespace LeanModels.Sv

set_option autoImplicit false

/-- A conservative, state-independent write footprint for an NBA target. -/
def Lhs2.nbaBounds (d : Design2) (t : Lhs2) : List Win :=
  match t.windows? d with
  | some ws => ws
  | none => match t with
    | .index n _ _ => ((d.declWidth n).map fun w => (n, 0, w)).toList
    | _ => []

/-- Admission of a packed runtime select includes its index expression. -/
def Lhs2.edgeOkB (d : Design2) : Lhs2 → Bool
  | .index n idx ew => (d.declWidth n).isSome && idx.wfB d && decide (0 < ew)
  | t => (t.windows? d).isSome

/-- The actual windows selected at issue time, before the NBA commit. -/
def Lhs2.edgeWindows (d : Design2) (st : SvState) : Lhs2 → Except String (List Win)
  | .index n idx ew =>
      match d.declWidth n with
      | none => .error s!"11.5.1: undeclared NBA select target '{n}'"
      | some w =>
          if ew = 0 then .error "11.5.1: zero-width NBA element select"
          else match evalPure2 st idx with
            | .ok iv => match indexInt? idx iv with
              | some i =>
                  if 0 ≤ i ∧ (i + 1) * (ew : Int) ≤ w then
                    .ok [(n, i.toNat * ew, ew)]
                  else .ok []
              | none => .ok []
            | .unsupported m => .error s!"11: {m}"
            | .timeout => .error "11: evaluation exhausted"
  | t => match t.windows? d with
    | some ws => .ok ws
    | none => .error "10.4.2: unsupported nonblocking assignment target"

/-- Index evaluation is total on an admitted target and a bound view. -/
theorem Lhs2.edgeWindows_total {d : Design2} {st : SvState}
    (hb : ∀ x ∈ d.symNames, ∃ v, SvState.lookup st x = some v)
    (t : Lhs2) (h : t.edgeOkB d = true) : ∃ ws, t.edgeWindows d st = .ok ws := by
  cases t with
  | index n idx ew =>
      simp only [Lhs2.edgeOkB, Bool.and_eq_true, Option.isSome_iff_exists,
        decide_eq_true_eq] at h
      obtain ⟨⟨⟨w, hw⟩, hi⟩, hew⟩ := h
      obtain ⟨hu, hid⟩ := Expr2.wfB_spec hi
      obtain ⟨iv, hiv⟩ := evalPure2_ok_of_wf hu fun x hx => hb x (hid x hx)
      simp only [Lhs2.edgeWindows, hw, ite_eq_right (by omega : ew ≠ 0), hiv]
      cases indexInt? idx iv with
      | none => exact ⟨[], rfl⟩
      | some i =>
          by_cases hr : 0 ≤ i ∧ (i + 1) * (ew : Int) ≤ w
          · exact ⟨[(n, i.toNat * ew, ew)], by simp [hr]⟩
          · exact ⟨[], by simp [hr]⟩
  | ident n | slice n lo w | concat ts =>
      simp only [Lhs2.edgeOkB, Option.isSome_iff_exists] at h
      obtain ⟨ws, hw⟩ := h
      exact ⟨ws, by simp only [Lhs2.edgeWindows, hw]⟩

/-- Every issued window is contained in a static footprint, for every view. -/
theorem Lhs2.edgeWindows_covered {d : Design2} {st : SvState} {t : Lhs2}
    {ws : List Win} (h : t.edgeWindows d st = .ok ws) :
    ∀ W ∈ ws, ∃ B ∈ t.nbaBounds d, Win.contains B W = true := by
  cases t with
  | index n idx ew =>
      simp only [Lhs2.edgeWindows] at h
      split at h
      · cases h
      · rename_i w hw
        split at h
        · cases h
        · split at h
          · rename_i iv hiv
            split at h
            · rename_i i hi
              split at h
              · rename_i hr
                simp only [Except.ok.injEq] at h
                subst ws
                intro W hW
                obtain rfl := List.mem_singleton.mp hW
                by_cases hl : ∃ c, idx = .lit c
                · obtain ⟨c, rfl⟩ := hl
                  simp only [evalPure2, Res.ok.injEq] at hiv
                  subst iv
                  simp only [indexInt?, Expr2.indexSigned, Bool.false_eq_true,
                    ite_false, Option.map_eq_some_iff] at hi
                  obtain ⟨k, hk, rfl⟩ := hi
                  refine ⟨(n, k * ew, ew), ?_, ?_⟩
                  · simp [Lhs2.nbaBounds, Lhs2.windows?_index_lit, hk]
                  · simp [Win.contains]
                · have hstatic : (Lhs2.index n idx ew).windows? d = none := by
                    cases idx <;> simp_all [Lhs2.windows?, Lhs2.window?]
                  refine ⟨(n, 0, w), ?_, ?_⟩
                  · simp [Lhs2.nbaBounds, hstatic, hw]
                  · rw [Win.contains_iff]
                    refine ⟨rfl, Nat.zero_le _, ?_⟩
                    have hi0 := hr.1
                    have hib := hr.2
                    have hn : (i.toNat : Int) = i := Int.toNat_of_nonneg hi0
                    have hnat : ((i.toNat * ew + ew : Nat) : Int) ≤ w := by
                      simpa only [Int.natCast_add, Int.natCast_mul, hn,
                        Int.add_mul, Int.one_mul] using hib
                    simpa only [Nat.zero_add] using Int.ofNat_le.mp hnat
              · cases h; simp
            · cases h; simp
          · cases h
          · cases h
  | ident n | slice n lo w | concat ts =>
      simp only [Lhs2.edgeWindows] at h
      split at h
      · rename_i ws' hw
        cases h
        intro W hW
        exact ⟨W, by simpa only [Lhs2.nbaBounds, hw] using hW,
          by simp [Win.contains]⟩
      · cases h

end LeanModels.Sv

#print axioms LeanModels.Sv.Lhs2.edgeWindows_total
#print axioms LeanModels.Sv.Lhs2.edgeWindows_covered
