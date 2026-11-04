import LeanModels.Sv.Comb2Base

/-!
# Committing nonblocking updates: disjoint updates commute (`LeanModels.Sv`)

`commitNba2` (`Sem2.lean`) commits an NBA queue in issue order. When updates from different blocks
write disjoint bits, the commit does not depend on the blocks' order (`commitNba2_perm`). Used by
E-core-1's R-EDGE (`Kernel/Core1Edge.lean`) and by the FF-only cycle lemma (`Seq2Cycle.lean`).
**Status: a `run2` library lemma** (about `commitNba2` only). Moved verbatim from
`Kernel/Core1Edge.lean` (arch-x1 `e39d0871`): when the two meet, `Core1Edge` imports this module and
drops its copy.
-/

namespace LeanModels.Sv

set_option autoImplicit false

/-! ## Committing nonblocking updates -/

/-- One nonblocking update (`commitNba2`'s step). -/
def nbaStep (st : SvState) (u : String × Nat × LVec) : SvState :=
  match SvState.lookup st u.1 with
  | some old => SvState.set st u.1 (old.insertAt u.2.1 u.2.2)
  | none => st

theorem commitNba2_cons (st : SvState) (u : String × Nat × LVec) (q : NbaQueue2) :
    commitNba2 st (u :: q) = commitNba2 (nbaStep st u) q := rfl

theorem commitNba2_append (st : SvState) (q₁ q₂ : NbaQueue2) :
    commitNba2 st (q₁ ++ q₂) = commitNba2 (commitNba2 st q₁) q₂ := by
  simp [commitNba2, List.foldl_append]

theorem keys_nbaStep (st : SvState) (u : String × Nat × LVec) :
    (nbaStep st u).map Prod.fst = st.map Prod.fst := by
  unfold nbaStep
  split
  · rename_i old h
    exact SvState.keys_set _ (SvState.lookup_isSome_iff.mp (by rw [h]; rfl))
  · rfl

theorem keys_commitNba2 : ∀ (st : SvState) (q : NbaQueue2),
    (commitNba2 st q).map Prod.fst = st.map Prod.fst
  | _, [] => rfl
  | st, u :: q => by rw [commitNba2_cons, keys_commitNba2, keys_nbaStep]

/-- A name no update writes is unchanged. -/
theorem lookup_commitNba2_of_not_mem {n : String} : ∀ (st : SvState) (q : NbaQueue2),
    (∀ u ∈ q, u.1 ≠ n) → SvState.lookup (commitNba2 st q) n = SvState.lookup st n
  | _, [], _ => rfl
  | st, u :: q, h => by
      rw [commitNba2_cons, lookup_commitNba2_of_not_mem _ q fun u' hu' => h u' (List.mem_cons_of_mem _ hu')]
      unfold nbaStep
      split
      · exact SvState.lookup_set_ne _ _ (h u (List.mem_cons_self ..))
      · rfl

/-- Two updates are disjoint: different signals, or disjoint bit ranges. -/
def NbaDisj (u u' : String × Nat × LVec) : Prop :=
  u.1 ≠ u'.1 ∨ u.2.1 + u.2.2.width ≤ u'.2.1 ∨ u'.2.1 + u'.2.2.width ≤ u.2.1

/-- **Disjoint updates commute.** -/
theorem nbaStep_comm {st : SvState} (hnd : (st.map Prod.fst).Nodup) {u u' : String × Nat × LVec}
    (h : NbaDisj u u') : nbaStep (nbaStep st u) u' = nbaStep (nbaStep st u') u := by
  apply SvState.ext
  · rw [keys_nbaStep, keys_nbaStep, keys_nbaStep, keys_nbaStep]
  · rw [keys_nbaStep, keys_nbaStep]; exact hnd
  · intro m
    obtain ⟨n, lo, p⟩ := u
    obtain ⟨n', lo', p'⟩ := u'
    simp only [NbaDisj] at h
    by_cases hnn : n = n'
    · subst hnn
      have hr : lo + p.width ≤ lo' ∨ lo' + p'.width ≤ lo := by
        rcases h with h | h | h
        · exact absurd rfl h
        · exact Or.inl h
        · exact Or.inr h
      unfold nbaStep
      cases hl : SvState.lookup st n with
      | none => simp [hl]
      | some old =>
          simp only [hl, SvState.lookup_set_self, SvState.lookup_set]
          rw [LVec.insertAt_comm hr]
          by_cases hm : n = m <;> simp [hm]
    · unfold nbaStep
      cases hl : SvState.lookup st n <;> cases hl' : SvState.lookup st n' <;>
        simp [hl, hl', SvState.lookup_set, hnn, Ne.symm hnn] <;>
        by_cases hm : n = m <;> by_cases hm' : n' = m <;> simp_all

/-- An update disjoint from every update of a block moves past it. -/
theorem commitNba2_move {u : String × Nat × LVec} : ∀ {st : SvState} {B R : NbaQueue2},
    (st.map Prod.fst).Nodup → (∀ u' ∈ B, NbaDisj u u') →
      commitNba2 st (u :: (B ++ R)) = commitNba2 st (B ++ u :: R)
  | _, [], _, _, _ => rfl
  | st, b :: B, R, hnd, h => by
      rw [List.cons_append, List.cons_append, commitNba2_cons, commitNba2_cons,
        nbaStep_comm hnd (h b (List.mem_cons_self ..)), ← commitNba2_cons, commitNba2_cons st b]
      exact commitNba2_move (by rw [keys_nbaStep]; exact hnd)
        fun u' hu' => h u' (List.mem_cons_of_mem _ hu')

/-- **Two blocks of pairwise disjoint updates commute.** -/
theorem commitNba2_swap : ∀ {st : SvState} {B₁ B₂ : NbaQueue2}, (st.map Prod.fst).Nodup →
    (∀ u ∈ B₁, ∀ u' ∈ B₂, NbaDisj u u') → commitNba2 st (B₁ ++ B₂) = commitNba2 st (B₂ ++ B₁)
  | _, [], _, _, _ => by simp
  | st, u :: B₁, B₂, hnd, h => by
      rw [List.cons_append, commitNba2_cons,
        commitNba2_swap (by rw [keys_nbaStep]; exact hnd)
          (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y hy),
        ← commitNba2_cons]
      exact commitNba2_move hnd fun u' hu' => h u (List.mem_cons_self ..) u' hu'

/-- **The commit of a family of blocks does not depend on their order**, when blocks of different
indices are disjoint. -/
theorem commitNba2_perm {B : Nat → NbaQueue2}
    (hd : ∀ p p', p ≠ p' → ∀ u ∈ B p, ∀ u' ∈ B p', NbaDisj u u') :
    ∀ {l l' : List Nat}, l.Perm l' → l.Nodup → ∀ {st : SvState}, (st.map Prod.fst).Nodup →
      commitNba2 st (l.flatMap B) = commitNba2 st (l'.flatMap B) := by
  intro l l' h
  induction h with
  | nil => intros; rfl
  | cons x _ ih =>
      intro hnd st hk
      simp only [List.flatMap_cons, commitNba2_append]
      exact ih (List.nodup_cons.mp hnd).2 (by rw [keys_commitNba2]; exact hk)
  | swap x y l =>
      intro hnd st hk
      have hxy : y ≠ x := fun h => (List.nodup_cons.mp hnd).1 (h ▸ List.mem_cons_self ..)
      simp only [List.flatMap_cons, ← List.append_assoc]
      rw [commitNba2_append st (B y ++ B x), commitNba2_append st (B x ++ B y),
        commitNba2_swap hk fun u hu u' hu' => hd y x hxy u hu u' hu']
  | trans h₁ _ ih₁ ih₂ =>
      intro hnd st hk
      rw [ih₁ hnd hk, ih₂ (h₁.nodup_iff.mp hnd) hk]

#print axioms nbaStep_comm
#print axioms commitNba2_perm

end LeanModels.Sv
