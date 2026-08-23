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

/-- **THE BRIDGE.** The model's zip-based `Forall₂`, *under the length premise
    `Resulttype_sub` always carries*, is exactly Mathlib's inductive
    `List.Forall₂`.

    This refines `docs/backlog/wasm.md` `2026-08-23-wasm-4`, which concluded
    Mathlib's `forall₂_*` API "does not apply to this model at all". That is
    true of the LEMMAS applied directly — the two predicates are different
    constants — but Mathlib supplies the ADAPTER itself,
    `List.forall₂_iff_zip`, whose side condition is a length equality. And
    `Resulttype_sub` carries a length equality in its constructor, precisely
    because its `Forall₂` is length-blind.

    So the honest statement is: **the API does not apply pointwise, but it
    applies through a one-time bridge, and the bridge's premise is already in
    every `Resulttype_sub`.** Paying it once restores the whole library for
    everything downstream — which is what `rt_sub_trans` and `rt_sub_app`
    below spend it on. -/
theorem rt_bridge (ts1 ts2 : List valtype) :
    ts1 subs< ts2 ↔ List.Forall₂ Valtype_sub ts1 ts2 := by
  unfold resulttypeSub
  constructor
  · rintro ⟨_, _, hlen, hall⟩
    refine List.forall₂_iff_zip.mpr ⟨by simpa using hlen, ?_⟩
    intro a b hab
    exact hall (a, b) hab
  · intro h
    refine Resulttype_sub.mk_Resulttype_sub _ _ (by simpa using h.length_eq) ?_
    intro t ht
    exact List.forall₂_zip h (by simpa using ht)

/-- Transitivity of `Valtype_sub`. Two constructors, two cases.
    Isabelle counterpart: `Valtype_sub_trans`. -/
theorem valtype_sub_trans (a b c : valtype)
    (h1 : Valtype_sub a b) (h2 : Valtype_sub b c) : Valtype_sub a c := by
  cases h1 with
  | refl _ => exact h2
  | bot _  => exact Valtype_sub.bot c

/-- Transitivity of `resulttypeSub`.
    Isabelle counterpart: `Resulttype_sub_trans` (closes on `list_all2_trans`;
    here the bridge plus a two-case induction). O3 needs this. -/
theorem rt_sub_trans (ts1 ts2 ts3 : List valtype)
    (h1 : ts1 subs< ts2) (h2 : ts2 subs< ts3) : ts1 subs< ts3 := by
  rw [rt_bridge] at h1 h2 ⊢
  induction h1 generalizing ts3 with
  | nil => cases h2; exact List.Forall₂.nil
  | cons hab _ ih =>
    cases h2 with
    | cons hbc hr2 => exact List.Forall₂.cons (valtype_sub_trans _ _ _ hab hbc) (ih _ hr2)

/-- `resulttypeSub` is a congruence for `++`.
    Isabelle counterpart: `Resulttype_sub_append` (closes on
    `list_all2_appendI`; here the bridge plus `List.rel_append`). O3 needs
    this. -/
theorem rt_sub_app (a b c d : List valtype)
    (h1 : a subs< c) (h2 : b subs< d) : (a ++ b) subs< (c ++ d) := by
  rw [rt_bridge] at h1 h2 ⊢
  exact List.rel_append h1 h2


/-- **O3.** Transitivity of instruction-type subtyping.

    Isabelle counterpart: `instr_subtyping_trans` — 64 lines there, and the
    only one of the four needing a structured `proof -`. The port follows its
    shape exactly:

    * unfold `instrtype_sub` twice to get two frame decompositions;
    * **split the second against the first** — `rt_sub_split_left` on the
      DOMAIN (`d_sub_23 subs< ts_12 ++ d_sub_12`) and `rt_sub_split_right` on
      the RANGE (`ts'_12 ++ r_sub_12 subs< r_sub_23`). This is the step both
      split orientations exist for, and it is why they had to land first;
    * assemble the composite frame `ts_23 ++ a` / `ts'_23 ++ c` and discharge
      the five side conditions with `rt_sub_app`, `rt_sub_trans` and
      `List.append_assoc`. -/
theorem instrtype_sub_trans (ft1 ft2 ft3 : functype)
    (h12 : instrtype_sub ft1 ft2) (h23 : instrtype_sub ft2 ft3) :
    instrtype_sub ft1 ft3 := by
  obtain ⟨⟨d1⟩, ⟨r1⟩⟩ := ft1
  obtain ⟨⟨d2⟩, ⟨r2⟩⟩ := ft2
  obtain ⟨⟨d3⟩, ⟨r3⟩⟩ := ft3
  obtain ⟨i12, o12, si12, no12, hd2, hr2, hio12, hsi12, hno12⟩ := h12
  obtain ⟨i23, o23, si23, no23, hd3, hr3, hio23, hsi23, hno23⟩ := h23
  -- domain: split `si23 subs< d2 = i12 ++ si12`
  obtain ⟨a, b, ha, hb, hab⟩ := rt_sub_split_left si23 i12 si12 (hd2 ▸ hsi23)
  -- range: split `r2 = o12 ++ no12 subs< no23`
  obtain ⟨c, d, hc, hd, hcd⟩ := rt_sub_split_right o12 no12 no23 (hr2 ▸ hno23)
  refine ⟨i23 ++ a, o23 ++ c, b, d, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd3, hab, List.append_assoc]
  · rw [hr3, hcd, List.append_assoc]
  · exact rt_sub_app _ _ _ _ hio23 (rt_sub_trans _ _ _ (rt_sub_trans _ _ _ ha hio12) hc)
  · exact rt_sub_trans _ _ _ hb hsi12
  · exact rt_sub_trans _ _ _ hno12 hd

end SubtypingPort
