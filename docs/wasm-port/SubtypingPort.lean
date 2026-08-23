/-
  SubtypingPort.lean — instruction-subtyping structural lemmas.

  ════════════════════════════════════════════════════════════════════════
  ATTRIBUTION — THESE PROOFS ARE A PORT, NOT ORIGINAL WORK.

  The proof STRUCTURE of every theorem in this file is taken from

      spectec/isabelle_type_safety_proof/Subtyping_Properties.thy
      author : Aaron Lee
      branch : aaron/subtyping/inversion_lemmas   (zilinc/spectec)
      commit : e75dad778   (2026-06-19)
      licence: Apache-2.0 (the repository's spectec/ directory)

  in the SAME repository, on a branch that is NOT merged into
  `lean-backend`. Each theorem below names its Isabelle counterpart.
  The Isabelle development is in Isabelle/HOL; this is a translation to
  Lean 4 against the SpecTec-generated `wasm2.0` model, not a copy of any
  Lean text.
  ════════════════════════════════════════════════════════════════════════

  THE TRANSLATION IS NOT MECHANICAL, AND THE REASON IS A MEASURED FINDING.

  Isabelle's development closes both split lemmas with
  `metis list_all2_append2` / `list_all2_append1`.  The obvious Lean
  counterpart is Mathlib's `List.forall₂_take_append` /
  `List.forall₂_drop_append`, and a first attempt used them.  **It does not
  typecheck, and cannot.**  The generated model defines its OWN `Forall₂`
  (`wasm2.0.lean:16`):

      def Forall₂ (P) (xs₁) (xs₂) : Prop := ∀ t ∈ xs₁.zip xs₂, P t.1 t.2

  That is a ZIP-BASED predicate, not Mathlib's INDUCTIVE `List.Forall₂`.
  They are different constants, so no Mathlib `forall₂_*` lemma applies to
  the model at all.

  The difference is semantic, not cosmetic: **a zip-based `Forall₂` does
  not imply equal lengths**, because `zip` truncates to the shorter list.
  That is exactly why the generator emits `Resulttype_sub` with a SEPARATE
  explicit length premise — it knows its own `Forall₂` is length-blind.
  The first attempt tried to recover the length from the relation
  (`hall.length_eq`) and failed for that reason; the length must come from
  the constructor's own premise, which the proofs below use.

  So Isabelle's `list_all2` (inductive, length-aware) and this model's
  `Forall₂` (zip-based, length-blind) are NOT the same predicate, and the
  port has to re-derive the splitting argument from `List.zip_append`
  rather than cite a library lemma.  The Isabelle FACTORING still holds —
  refl, both split orientations, then trans — which is what the port takes
  from it.
-/

import Mathlib.Tactic
import «wasm2.0»
import «custom_notation»

open functype list

namespace SubtypingPort

/-- Every pair drawn from `l.zip l` has equal components.
    (The same lemma opens `typing_lemmas.lean`; restated because that file
    does not elaborate at this commit.) -/
theorem zip_self_eq {α : Type} (l : List α) : ∀ t ∈ l.zip l, t.1 = t.2 := by
  intro t h
  simp [List.zip] at *
  obtain ⟨a, _, h_eq⟩ := h
  subst h_eq
  rfl

/-- Reflexivity of `resulttypeSub`.
    Isabelle counterpart: `Resulttype_sub_refl`. -/
theorem rt_sub_refl (ts : List valtype) : ts subs< ts := by
  unfold resulttypeSub
  refine Resulttype_sub.mk_Resulttype_sub ts ts rfl ?_
  intro t ht
  rw [zip_self_eq ts t ht]
  exact Valtype_sub.refl _

/-- `instrtype_sub`, restated VERBATIM from `typing_lemmas.lean:1015`
    because that file does not elaborate (see the header). Wasm's
    stack-polymorphic instruction subtyping: an instruction typed
    `t1* -> t2*` may be used where `t* t1'* -> t* t2'*` is wanted, with a
    frame (`rest_in`/`rest_out`) threaded past it. -/
def instrtype_sub (original_ft contextualized_ft : functype) : Prop :=
  match original_ft, contextualized_ft with
  | mk_functype (mk_list original_input_type) (mk_list original_output_type),
    mk_functype (mk_list actual_supplied_input_type) (mk_list actual_needed_output_type) =>
    ∃ (rest_in rest_out supplied_in needed_out : List valtype),
      actual_supplied_input_type = rest_in ++ supplied_in
      ∧ actual_needed_output_type = rest_out ++ needed_out
      ∧ (rest_in subs< rest_out)
      ∧ (supplied_in subs< original_input_type)
      ∧ (original_output_type subs< needed_out)

/-- **O1.** Reflexivity of instruction-type subtyping.

    Isabelle counterpart: `instr_subtyping_refl`.

    The frame is instantiated EMPTY: with `rest_in = rest_out = []` the two
    append equations become `t = [] ++ t`, which is definitional, and the
    three side-conditions all become reflexivity. -/
theorem instrtype_sub_refl (ft : functype) : instrtype_sub ft ft := by
  obtain ⟨⟨t1s⟩, ⟨t2s⟩⟩ := ft
  exact ⟨[], [], t1s, t2s, rfl, rfl,
         rt_sub_refl [], rt_sub_refl t1s, rt_sub_refl t2s⟩

/-- The split lemma, LEFT orientation: an append on the RIGHT of the
    relation splits the left-hand list.
    Isabelle counterpart: `Resulttype_sub_split_left`. -/
theorem rt_sub_split_left (ts ts1 ts2 : List valtype)
    (h : ts subs< (ts1 ++ ts2)) :
    ∃ ts1' ts2', ts1' subs< ts1 ∧ ts2' subs< ts2 ∧ ts = ts1' ++ ts2' := by
  unfold resulttypeSub at h ⊢
  cases h with
  | mk_Resulttype_sub _ _ hlen hall =>
    -- The length comes from the CONSTRUCTOR's premise, never from `hall`:
    -- the model's `Forall₂` is zip-based and length-blind (see header).
    have hL : ts.length = ts1.length + ts2.length := by simpa using hlen
    have hTake : (ts.take ts1.length).length = ts1.length := by
      simp; omega
    have hsplit : ts.zip (ts1 ++ ts2)
        = (ts.take ts1.length).zip ts1 ++ (ts.drop ts1.length).zip ts2 := by
      conv_lhs => rw [← List.take_append_drop ts1.length ts]
      exact List.zip_append hTake
    refine ⟨ts.take ts1.length, ts.drop ts1.length, ?_, ?_,
            (List.take_append_drop _ _).symm⟩
    · refine Resulttype_sub.mk_Resulttype_sub _ _ hTake ?_
      intro t ht
      exact hall t (by rw [hsplit]; exact List.mem_append_left _ ht)
    · refine Resulttype_sub.mk_Resulttype_sub _ _ (by simp; omega) ?_
      intro t ht
      exact hall t (by rw [hsplit]; exact List.mem_append_right _ ht)

/-- The split lemma, RIGHT orientation: an append on the LEFT of the
    relation splits the right-hand list.
    Isabelle counterpart: `Resulttype_sub_split_right`.

    **A genuinely separate obligation, not a symmetry corollary** —
    `docs/wasm-soundness-census.md` §2.2 guessed it might be free by
    symmetry, and Aaron Lee's development refuted that guess: he proved the
    two separately, with different closers. -/
theorem rt_sub_split_right (ts1 ts2 ts : List valtype)
    (h : (ts1 ++ ts2) subs< ts) :
    ∃ ts1' ts2', ts1 subs< ts1' ∧ ts2 subs< ts2' ∧ ts = ts1' ++ ts2' := by
  unfold resulttypeSub at h ⊢
  cases h with
  | mk_Resulttype_sub _ _ hlen hall =>
    have hL : ts1.length + ts2.length = ts.length := by simpa using hlen
    have hTake : ts1.length = (ts.take ts1.length).length := by
      simp; omega
    have hsplit : (ts1 ++ ts2).zip ts
        = ts1.zip (ts.take ts1.length) ++ ts2.zip (ts.drop ts1.length) := by
      conv_lhs => rw [← List.take_append_drop ts1.length ts]
      exact List.zip_append hTake
    refine ⟨ts.take ts1.length, ts.drop ts1.length, ?_, ?_,
            (List.take_append_drop _ _).symm⟩
    · refine Resulttype_sub.mk_Resulttype_sub _ _ hTake ?_
      intro t ht
      exact hall t (by rw [hsplit]; exact List.mem_append_left _ ht)
    · refine Resulttype_sub.mk_Resulttype_sub _ _ (by simp; omega) ?_
      intro t ht
      exact hall t (by rw [hsplit]; exact List.mem_append_right _ ht)

end SubtypingPort
