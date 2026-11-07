import LeanModels.Sv.Comb2Base

/-!
# Committing nonblocking updates: disjoint updates commute (`LeanModels.Sv`)

`commitNba2` (`Sem2.lean`) commits an NBA queue in issue order. When updates from different blocks
write disjoint bits, the commit does not depend on the blocks' order (`commitNba2_perm`). Used by
E-core-1's R-EDGE (`Kernel/Core1Edge.lean`) and by the FF-only cycle lemma (`Seq2Cycle.lean`).
**Status: a `run2` library lemma** (about `commitNba2` only). Moved verbatim from
`Kernel/Core1Edge.lean` (arch-x1 `e39d0871`); `Core1Edge` imports this module and has dropped its
copy, which collided with this one once the umbrella `LeanModels.lean` imported both.

Also here: `commitNba2_nil`/`_cons`/`_append`, and the commit restricted to one signal (`nbaFold`, with
`nbaFold_append`, `nbaFold_flatMap`, `nbaFold_flatMap_eq_self`, `width_nbaFold`) and `width_foldl_insertAt`.
-/

namespace LeanModels.Sv

set_option autoImplicit false

/-! ## Committing nonblocking updates -/

/-- One nonblocking update (`commitNba2`'s step). -/
def nbaStep (st : SvState) (u : String × Nat × LVec) : SvState :=
  match SvState.lookup st u.1 with
  | some old => SvState.set st u.1 (old.insertAt u.2.1 u.2.2)
  | none => st

/-- Committing the empty queue changes nothing. -/
theorem commitNba2_nil (st : SvState) : commitNba2 st [] = st := rfl

/-- Committing `u :: q` is `u`'s step, then the commit of `q`. -/
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

/-! ## Committing to one signal

A state of separate registers commits register by register: `nbaFold n q x` is the commit of the queue `q`
restricted to the signal `n`, applied to its old value `x`. -/

/-- The writes of a queue to the signal `n`, in order, over `x`. -/
def nbaFold (n : String) (q : NbaQueue2) (x : LVec) : LVec :=
  q.foldl (fun acc u => if u.1 = n then acc.insertAt u.2.1 u.2.2 else acc) x

/-- `nbaFold` of a concatenation: the first queue's writes, then the second's. -/
theorem nbaFold_append (n : String) (a b : NbaQueue2) (x : LVec) :
    nbaFold n (a ++ b) x = nbaFold n b (nbaFold n a x) :=
  List.foldl_append ..

/-- `nbaFold` of the queues of a family `f k`, `k ∈ l`, is the fold of each family member's `nbaFold`. -/
theorem nbaFold_flatMap {α : Type} (n : String) (f : α → NbaQueue2) : ∀ (l : List α) (x : LVec),
    nbaFold n (l.flatMap f) x = l.foldl (fun acc k => nbaFold n (f k) acc) x
  | [], _ => rfl
  | a :: l, x => by rw [List.flatMap_cons, nbaFold_append, nbaFold_flatMap n f l]; rfl

/-- A family whose every member's queue leaves the signal `n` unchanged leaves it unchanged. -/
theorem nbaFold_flatMap_eq_self {α : Type} {n : String} {f : α → NbaQueue2} (h : ∀ k x, nbaFold n (f k) x = x) :
    ∀ (l : List α) (x : LVec), nbaFold n (l.flatMap f) x = x
  | [], _ => rfl
  | a :: l, x => by rw [List.flatMap_cons, nbaFold_append, h, nbaFold_flatMap_eq_self h l]

/-- `nbaFold` keeps the width (every write is a select-write). -/
@[simp] theorem width_nbaFold (n : String) : ∀ (q : NbaQueue2) (x : LVec), (nbaFold n q x).width = x.width
  | [], _ => rfl
  | u :: q, x => by
    simp only [nbaFold, List.foldl_cons]
    rw [← nbaFold, width_nbaFold n q]; split <;> simp

/-- Applying every write of a queue to one vector (signal names ignored) keeps its width. -/
theorem width_foldl_insertAt (q : NbaQueue2) (c : LVec) :
    (q.foldl (fun acc u => acc.insertAt u.2.1 u.2.2) c).width = c.width := by
  induction q generalizing c with
  | nil => rfl
  | cons u q ih => rw [List.foldl_cons, ih, LVec.width_insertAt]

#print axioms nbaStep_comm
#print axioms commitNba2_perm

end LeanModels.Sv
