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

/-- **O2.** The RANGE may be weakened upward.

    Isabelle counterpart: `instr_subtyping_weaken2`.

    Census (`docs/backlog/wasm.md`): needs **no new prerequisite** — the
    frame's range half `rest_out ++ needed_out` is split against the weakened
    type by `rt_sub_split_right`, and the two resulting halves are composed
    with `rt_sub_trans`. -/
theorem instr_subtyping_weaken2 (tx1 tx2 ty1 ty2 ty2_sup : List valtype)
    (h : instrtype_sub (mkFunctype tx1 ty1) (mkFunctype tx2 ty2))
    (hsup : ty2 subs< ty2_sup) :
    instrtype_sub (mkFunctype tx1 ty1) (mkFunctype tx2 ty2_sup) := by
  obtain ⟨ri, ro, si, no, hx, hy, hio, hsi, hno⟩ := h
  obtain ⟨c, d, hc, hd, hcd⟩ := rt_sub_split_right ro no ty2_sup (hy ▸ hsup)
  exact ⟨ri, c, si, d, hx, hcd, rt_sub_trans _ _ _ hio hc, hsi,
         rt_sub_trans _ _ _ hno hd⟩

/-- **O4.** The DOMAIN may be strengthened downward.

    Isabelle counterpart: `instr_subtyping_strengthen2`. The dual of O2, and
    the reason the split lemma was needed in BOTH orientations: this one
    splits with `rt_sub_split_left` where O2 splits with `rt_sub_split_right`.
    Census: no new prerequisite. -/
theorem instr_subtyping_strengthen2 (tx1 tx2 ty1 ty2 tx2_sub : List valtype)
    (h : instrtype_sub (mkFunctype tx1 ty1) (mkFunctype tx2 ty2))
    (hsub : tx2_sub subs< tx2) :
    instrtype_sub (mkFunctype tx1 ty1) (mkFunctype tx2_sub ty2) := by
  obtain ⟨ri, ro, si, no, hx, hy, hio, hsi, hno⟩ := h
  obtain ⟨a, b, ha, hb, hab⟩ := rt_sub_split_left tx2_sub ri si (hx ▸ hsub)
  exact ⟨a, ro, b, no, hab, hy, rt_sub_trans _ _ _ ha hio,
         rt_sub_trans _ _ _ hb hsi, hno⟩

/-
  ══════════════════════════════════════════════════════════════════════════
  THE DECLINED REPAIR — recorded with its price, so a later lane wanting the
  strong form finds the cost already computed rather than re-deriving it.

  `typing_lemmas.lean:295-412` states `ais_empty_typing` as an IFF:

      Instrs_ok2 s c [] (t1s f-> t2s)
        ↔ (wf_context c ∧ wf_store s ∧ t1s subs< t2s)

  **It is BROKEN.** Two of the six baseline build errors live inside that
  span: `371:8 too many variable names provided` and `380:17 rcases failed`.

  REPAIRING IT WAS CONSIDERED AND DECLINED. The measurement that declined it:

  1. **O5 consumes only `.mp`, and only its THIRD component.** Both use sites,
     measured:
       * `typing_lemmas.lean:1753` —
         `have ⟨wf_c', wf_s_2, subsrel⟩ := (ais_empty_typing s c' ts1' ts2').mp instrs_ok2_1; exact subsrel`
       * `typing_lemmas.lean:1782` — the same shape at `ts2' ts3'`.
     Neither well-formedness conjunct and neither `.mpr` is ever used.

  2. **Isabelle abandoned the strong form.** In `Properties_Aux.thy` on
     `aaron/subtyping/instr_ok2_inversion_lemmas` (`e75dad778`), the
     equality-shaped `e_type_empty` is followed by **`oops`** — given up. What
     is proved there is `e_type_empty1`, one-directional. So the strong form
     is a dead end in the other assistant too, not merely unported.

  3. **THE PRICE A REPAIR WOULD CARRY: the baseline pin moves 6 → 4.** Errors
     `371` and `380` would depart with a fixed `ais_empty_typing`, changing
     the lane's pinned failure shape. Routing around it instead leaves the
     baseline untouched at 6, and `371`/`380` stand as known-broken.

  4. **The weak form costs ZERO new prerequisites** — `rt_sub_refl`,
     `rt_sub_trans` and `rt_sub_app`, all proved above. Isabelle's
     `e_type_empty1` concludes `empty-functype <ti: ft`, which is why it needs
     `instr_subtyping_sub_rule` and `instr_subtyping_frame_rule`; a `subs<`
     conclusion needs neither.

  Repairing upstream's file is upstream's business, and upstream contact is
  not this lane's to initiate. If a later lane does want the strong form, the
  price above is what it costs.
  ══════════════════════════════════════════════════════════════════════════
-/

/-- **O5's one missing prerequisite, in the WEAK form O5 actually consumes.**

    `typing_lemmas.lean:295` states `ais_empty_typing` as an IFF whose right
    side is a three-way conjunction:
    `Instrs_ok2 s c [] (t1s f-> t2s) ↔ (wf_context c ∧ wf_store s ∧ t1s subs< t2s)`.
    **O5 uses only `.mp`, and only its THIRD component** (measured at
    `typing_lemmas.lean:1753` and `:1782`, both of which read
    `have ⟨_, _, subsrel⟩ := (ais_empty_typing …).mp …; exact subsrel`).

    So this states exactly that third component. Three reasons, all measured:

    * **The full iff is not needed.** Nothing in O5 consumes the two
      well-formedness conjuncts or the `.mpr` direction.
    * **The original is BROKEN.** `ais_empty_typing` spans
      `typing_lemmas.lean:295-412`, and two of the six baseline build errors —
      `371:8 too many variable names provided` and `380:17 rcases failed` —
      are INSIDE it. There is no working Lean original to transcribe.
    * **Isabelle abandoned the strong form.** In
      `Properties_Aux.thy` (`aaron/subtyping/instr_ok2_inversion_lemmas`)
      the equality-shaped `e_type_empty` is followed by **`oops`** — given up.
      What is proved there is `e_type_empty1`, the one-directional form.

    Isabelle counterpart: **`e_type_empty1`**. Its conclusion is
    `empty-functype <ti: ft`, which needs `instr_subtyping_sub_rule` and
    `instr_subtyping_frame_rule`; **this weaker `subs<` conclusion needs
    neither**, and closes with machinery already proved above. -/
theorem ais_empty_subs (s : store) (c : context) (t1s t2s : List valtype)
    (h : Instrs_ok2 s c [] (mkFunctype t1s t2s)) : t1s subs< t2s := by
  -- `induction` cannot be used directly: `Instrs_ok2` is MUTUALLY INDUCTIVE
  -- with `Instr_ok2` and `Expr_ok2`, and the tactic refuses outright. The
  -- idiom is copied from the fork's own working proof of this very statement
  -- (`typing_lemmas.lean:326-329`): apply `Instrs_ok2.rec` explicitly with the
  -- sibling motives at `True`, then `all_goals try trivial` clears them.
  --
  -- The case binders arrive INACCESSIBLE, so they are taken with `rename_i`
  -- from the END rather than named positionally: a positional list is what
  -- `typing_lemmas.lean:371` gets wrong ("too many variable names provided"),
  -- and counting from the end is stable under changes to the constructor's
  -- leading arguments.
  have main :
      ∀ (l' : List admininstr) (ft : functype),
        Instrs_ok2 s c l' ft →
        ∀ (a b : List valtype),
          ([] : List admininstr) = l' →
          (mkFunctype a b) = ft →
          a subs< b := by
    -- `clear h` is LOAD-BEARING: without it `induction` sweeps the outer
    -- hypothesis into the motive and every IH arrives with a spurious leading
    -- `Instrs_ok2 s c [] (t1s f-> t2s) →`. The original does the same thing at
    -- `typing_lemmas.lean:325` (`clear instrs_ok2 gen_instrs_ok2_list t1s t2s l`).
    clear h
    intro l' ft hh
    induction hh
      using Instrs_ok2.rec
        (motive_1 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
    all_goals try trivial
    case empty =>
      intro a b _ heq
      unfold mkFunctype at heq
      injection heq with h1 h2
      injection h1 with h1
      injection h2 with h2
      subst h1; subst h2
      exact rt_sub_refl []
    case instr =>
      intro a b hempty _
      exact absurd hempty (by simp)
    case seq =>
      rename_i ih1 ih2
      intro a b hempty heq
      obtain ⟨e1, e2⟩ := List.append_eq_nil_iff.mp hempty.symm
      unfold mkFunctype at heq
      injection heq with h1 h2
      injection h1 with h1
      injection h2 with h2
      subst h1; subst h2
      have i1 := ih1 _ _ e1.symm rfl
      have i2 := ih2 _ _ e2.symm rfl
      exact rt_sub_trans _ _ _ i1 i2
    case sub =>
      rename_i hsub1 hsub2 _ _ _ ih
      intro a b hempty heq
      unfold mkFunctype at heq
      injection heq with h1 h2
      injection h1 with h1
      injection h2 with h2
      subst h1; subst h2
      have inner := ih _ _ hempty rfl
      have s1 : _ subs< _ := hsub1
      have s2 : _ subs< _ := hsub2
      exact rt_sub_trans _ _ _ s1 (rt_sub_trans _ _ _ inner s2)
    -- The case the ORIGINAL gets wrong: BOTH baseline errors (`371:8` and
    -- `380:17`) live here — an over-long positional binder list, then an
    -- `obtain` destructuring a functype EQUATION as if it were a pair.
    case Instrs_ok2_frame =>
      rename_i ih
      intro a b hempty heq
      unfold mkFunctype at heq
      injection heq with h1 h2
      injection h1 with h1
      injection h2 with h2
      subst h1; subst h2
      have inner := ih _ _ hempty rfl
      exact rt_sub_app _ _ _ _ (rt_sub_refl _) inner
  exact main [] (mkFunctype t1s t2s) h t1s t2s rfl rfl

/-- The FRAME rule for `instrtype_sub`: a frame may be pushed onto both sides
    of the contextualised type. Isabelle counterpart: `instr_subtyping_frame_rule`.
    Needed by O5's `Instrs_ok2_frame` case. -/
theorem instrtype_sub_frame (ts : List valtype) (ft1 : functype) (a b : List valtype)
    (h : instrtype_sub ft1 (mkFunctype a b)) :
    instrtype_sub ft1 (mkFunctype (ts ++ a) (ts ++ b)) := by
  obtain ⟨⟨p⟩, ⟨q⟩⟩ := ft1
  obtain ⟨ri, ro, si, no, hx, hy, hio, hsi, hno⟩ := h
  refine ⟨ts ++ ri, ts ++ ro, si, no, ?_, ?_, ?_, hsi, hno⟩
  · rw [hx, List.append_assoc]
  · rw [hy, List.append_assoc]
  · exact rt_sub_app _ _ _ _ (rt_sub_refl ts) hio

/-- **O5.** Single-instruction typing inversion for ADMINISTRATIVE instructions.

    Isabelle counterpart: `instr2_inversion_helper`. The original Lean proof is
    `typing_lemmas.lean:1682-1865` and is the file's LAST `sorry` (at `1865`,
    the `Instrs_ok2_frame` case).

    Every prerequisite is proved above: `instrtype_sub_refl` (O1),
    `instrtype_sub_trans` (O3), `instr_subtyping_weaken2` (O2),
    `instr_subtyping_strengthen2` (O4), `ais_empty_subs`, and the frame rule.

    The three idioms this file established are all load-bearing here:
    `Instrs_ok2.rec` with the sibling motives at `True` (the type is mutually
    inductive), `rename_i` from the END (case binders arrive inaccessible), and
    `clear` before inducting (or the outer hypothesis is swept into the motive
    and every IH grows a spurious premise). -/
theorem ais_single_typing_inversion (s : store) (c : context) (ai : admininstr)
    (ts1 ts2 : List valtype)
    (h : Instrs_ok2 s c [ai] (mkFunctype ts1 ts2)) :
    ∃ p q, Instr_ok2 s c ai (mkFunctype p q)
         ∧ instrtype_sub (mkFunctype p q) (mkFunctype ts1 ts2) := by
  have main :
      ∀ (l : List admininstr) (ft : functype),
        Instrs_ok2 s c l ft →
        ∀ (e : admininstr) (x y : List valtype),
          [e] = l → (mkFunctype x y) = ft →
          ∃ p q, Instr_ok2 s c e (mkFunctype p q)
               ∧ instrtype_sub (mkFunctype p q) (mkFunctype x y) := by
    clear h
    intro l ft hh
    induction hh
      using Instrs_ok2.rec
        (motive_1 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
    all_goals try trivial
    case empty =>
      intro e x y hl _
      exact absurd hl (by simp)
    case instr =>
      rename_i hinstr _ _ _ _
      intro e x y hl heq
      injection hl with he
      subst he
      unfold mkFunctype at heq
      injection heq with h1 h2
      injection h1 with h1
      injection h2 with h2
      subst h1; subst h2
      exact ⟨_, _, hinstr, instrtype_sub_refl _⟩
    case seq =>
      rename_i hd1 hd2 _ _ _ _ ih1 ih2
      intro e x y hl heq
      unfold mkFunctype at heq
      injection heq with h1 h2
      injection h1 with h1
      injection h2 with h2
      subst h1; subst h2
      rcases List.append_eq_singleton_iff.mp hl.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · -- l1 = [], l2 = [e] : the empty prefix contributes a `subs<` on the domain
        subst e1
        obtain ⟨p, q, hp, hq⟩ := ih2 e _ _ e2.symm rfl
        exact ⟨p, q, hp,
          instr_subtyping_strengthen2 _ _ _ _ _ hq (ais_empty_subs s _ _ _ hd1)⟩
      · -- l1 = [e], l2 = [] : the empty suffix contributes a `subs<` on the range
        subst e2
        obtain ⟨p, q, hp, hq⟩ := ih1 e _ _ e1.symm rfl
        exact ⟨p, q, hp,
          instr_subtyping_weaken2 _ _ _ _ _ hq (ais_empty_subs s _ _ _ hd2)⟩
    case sub =>
      rename_i hsub1 hsub2 _ _ _ ih
      intro e x y hl heq
      unfold mkFunctype at heq
      injection heq with h1 h2
      injection h1 with h1
      injection h2 with h2
      subst h1; subst h2
      obtain ⟨p, q, hp, hq⟩ := ih e _ _ hl rfl
      have s1 : _ subs< _ := hsub1
      have s2 : _ subs< _ := hsub2
      exact ⟨p, q, hp,
        instr_subtyping_weaken2 _ _ _ _ _ (instr_subtyping_strengthen2 _ _ _ _ _ hq s1) s2⟩
    case Instrs_ok2_frame =>
      rename_i ih
      intro e x y hl heq
      unfold mkFunctype at heq
      injection heq with h1 h2
      injection h1 with h1
      injection h2 with h2
      subst h1; subst h2
      obtain ⟨p, q, hp, hq⟩ := ih e _ _ hl rfl
      exact ⟨p, q, hp, instrtype_sub_frame _ _ _ _ hq⟩
  exact main [ai] (mkFunctype ts1 ts2) h ai ts1 ts2 rfl rfl

/-! ## A′ — the subtyping THEOREM, above the properties

    Ported from `Subtyping_Theorem.thy` and `Typing_Simplified.thy` on
    `aaron/store_extension/reduction` (`14b78c2bb`) — three files that are
    GREEN THROUGHOUT (19 + 14 + 4 lemmas, zero `sorry`, zero `oops`), unlike
    `Properties_Aux.thy` where 7 of 16 are incomplete. -/

/-- `Instrs_ok2` carries its well-formedness side conditions in EVERY
    constructor, so this needs no induction at all.
    Isabelle counterpart: `Instrs_ok2_wf` (`Typing_Simplified.thy:35`).

    **`cases` works here where `induction` refuses.** The mutual-inductive
    restriction that forced the `Instrs_ok2.rec` idiom elsewhere in this file
    applies to `induction` only; `cases` needs no sibling motives. -/
theorem instrs_ok2_wf {s : store} {c : context} {e : List admininstr} {ft : functype}
    (h : Instrs_ok2 s c e ft) : wf_store s ∧ wf_context c := by
  cases h <;> exact ⟨by assumption, by assumption⟩

/-- Every instruction in a typed sequence is well-formed.
    Isabelle counterpart: `Instrs_ok2_wf_instr` (`Typing_Simplified.thy:114`).

    **Much cheaper in Lean than in Isabelle, and the model is why.** Isabelle's
    proof routes through `wf_admininstr_instr` — an induction over `wf_instr`
    with a nested `Ref_ok` induction — because its `plain` case supplies
    `wf_instr`. The generated Lean `Instrs_ok2.instr` constructor supplies
    **`wf_admininstr` directly**, so `cases` plus an append split closes it. -/
theorem instrs_ok2_wf_instr {s : store} {c : context} {e : List admininstr} {ft : functype}
    (h : Instrs_ok2 s c e ft) : Forall (fun a => wf_admininstr a) e := by
  -- `cases` REORDERS the constructor's premises (`wf_context` lands last, the
  -- `Forall`s in the middle), so neither positional naming nor `rename_i` from
  -- the end is stable here. Each branch closes by `assumption` instead.
  cases h with
  | empty => intro a ha; exact absurd ha (by simp)
  | instr => intro a ha; simp at ha; subst ha; assumption
  | seq =>
    intro a ha
    rcases List.mem_append.mp ha with h' | h' <;> solve_by_elim
  | sub => assumption
  | Instrs_ok2_frame => assumption

/-- A frame may be pushed on, with the two frame halves related by `subs<`.
    Isabelle counterpart: `Instrs_ok2_frame_sub` (`Subtyping_Theorem.thy:41`). -/
theorem instrs_ok2_frame_sub {s : store} {c : context} {e : List admininstr}
    {ts ts' t1 t2 : List valtype}
    (hts : ts subs< ts')
    (h : Instrs_ok2 s c e (mkFunctype t1 t2)) :
    Instrs_ok2 s c e (mkFunctype (ts ++ t1) (ts' ++ t2)) := by
  obtain ⟨hs, hc⟩ := instrs_ok2_wf h
  have hw := instrs_ok2_wf_instr h
  have framed : Instrs_ok2 s c e (mkFunctype (ts ++ t1) (ts ++ t2)) :=
    Instrs_ok2.Instrs_ok2_frame s c e ts t1 t2 h hs hc hw
  exact Instrs_ok2.sub s c e (ts ++ t1) (ts' ++ t2) (ts ++ t1) (ts ++ t2) framed
    (rt_sub_refl _) (rt_sub_app _ _ _ _ hts (rt_sub_refl t2)) hs hc hw

/-- **THE A′ CAPSTONE.** Subtyping is ADMISSIBLE for the typing judgment: a
    typed instruction sequence may be retyped at any supertype.
    Isabelle counterpart: `Instrs_ok2_subtyping` (`Subtyping_Theorem.thy:57`).

    **The formulation differs and the adaptation is the interesting part.**
    Isabelle destructures an INDUCTIVE `Instrtype_sub` via its constructor
    `mk_Instrtype_sub`; this port carries the DEFINITIONAL ∃-form transcribed
    from `typing_lemmas.lean:1015`, so the frame decomposition arrives by
    `obtain` rather than by `cases` — shorter, and it is why the proof below is
    a handful of lines against Isabelle's structured block. -/
theorem instrs_ok2_subtyping {s : store} {c : context} {e : List admininstr}
    {t1s t2s t1s' t2s' : List valtype}
    (hsub : instrtype_sub (mkFunctype t1s t2s) (mkFunctype t1s' t2s'))
    (h : Instrs_ok2 s c e (mkFunctype t1s t2s)) :
    Instrs_ok2 s c e (mkFunctype t1s' t2s') := by
  obtain ⟨ri, ro, si, no, hx, hy, hio, hsi, hno⟩ := hsub
  obtain ⟨hs, hc⟩ := instrs_ok2_wf h
  have hw := instrs_ok2_wf_instr h
  -- retype the body at (si -> no) by subsumption, then frame with ri/ro
  have inner : Instrs_ok2 s c e (mkFunctype si no) :=
    Instrs_ok2.sub s c e si no t1s t2s h hsi hno hs hc hw
  have framed := instrs_ok2_frame_sub hio inner
  rw [hx, hy]
  exact framed

end SubtypingPort
