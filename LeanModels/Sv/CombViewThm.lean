import LeanModels.Sv.CombView

/-!
# `sv_structure`, stage 2: soundness of the summary's sites and the obligations

`CombView.lean` defines the summary. Here:

* the geometry of the declared arrays (`arrayElemWindow_row`, `arrayPartRead_part2`, … : the flat
  window an in-range access of each form lowers to);
* the per-site soundness theorem (`site_desc`): the process `instProcess2` builds for a template
  site is an `assign` to EXACTLY the promised target whose reads are CONTAINED in the promised
  ones, with no loud node and only declared identifiers;
* the obligations the summary leaves to the player, as compact `Prop`s over the loop indices
  (`InRangeObl`, `DisjObl`, `RankObl`, `LexObl`; `AutoObl` is for the tactic's `omega`).
-/

namespace LeanModels.Sv
namespace CombView

/-! ## Geometry of in-range accesses -/

/-- A 1-D zero-based descending array select, in range. -/
theorem arrayElemWindow_1d_in {E : IEnv} {n : String} {i : PExpr} {m k : Int}
    (hd : E.dims.lookup n = some [(m, 0)]) (hev : evalInt E i = .ok k) (hk0 : 0 ≤ k)
    (hkm : k ≤ m) : arrayElemWindow E n [i] = .ok (k, 1, true) := by
  have hm : 0 ≤ m := by omega
  rw [arrayElemWindow_of (arrayDims_of hd)
    (walkIndices_desc0_cons hm hev hk0 hkm (walkIndices_nil (env := E) []))]
  simp

/-- A row of a 2-D zero-based descending array. -/
theorem arrayElemWindow_row {E : IEnv} {n : String} {ie : PExpr} {m1 m2 k : Int}
    (hd : E.dims.lookup n = some [(m1, 0), (m2, 0)]) (hm2 : 0 ≤ m2)
    (hev : evalInt E ie = .ok k) (hk0 : 0 ≤ k) (hk1 : k ≤ m1) :
    arrayElemWindow E n [ie] = .ok (k * (m2 + 1), (m2 + 1).toNat, true) := by
  have hm1 : 0 ≤ m1 := by omega
  rw [arrayElemWindow_of (arrayDims_of hd)
    (walkIndices_desc0_cons hm1 hev hk0 hk1 (walkIndices_nil (env := E) [(m2, 0)]))]
  have h1 : ((dimCount m2 0 : Nat) : Int) = m2 + 1 := dimCount_desc0 hm2
  have h2 : dimCount m2 0 = (m2 + 1).toNat := by omega
  simp only [dimsStride, Nat.mul_one, h1, Int.add_zero]
  rw [h2]

/-- An element of a 2-D zero-based descending array. -/
theorem arrayElemWindow_cell2 {E : IEnv} {n : String} {ie je : PExpr} {m1 m2 i j : Int}
    (hd : E.dims.lookup n = some [(m1, 0), (m2, 0)])
    (hi : evalInt E ie = .ok i) (hi0 : 0 ≤ i) (hi1 : i ≤ m1)
    (hj : evalInt E je = .ok j) (hj0 : 0 ≤ j) (hj1 : j ≤ m2) :
    arrayElemWindow E n [ie, je] = .ok (i * (m2 + 1) + j, 1, true) :=
  arrayElemWindow_desc0_2 hd (by omega) (by omega) hi hi0 hi1 hj hj0 hj1

/-- Part `[hi:lo]` of a 1-D zero-based descending vector. -/
theorem arrayPartGeom_part1 {E : IEnv} {n : String} {a b : PExpr} {m hi lo : Int}
    (hd : E.dims.lookup n = some [(m, 0)]) (hm : 0 ≤ m)
    (ha : evalInt E a = .ok hi) (hb : evalInt E b = .ok lo) (hlh : lo ≤ hi) :
    arrayPartGeom E n [] .range a b = .ok (0, true, 1, dimCount m 0, lo, hi) := by
  have := arrayPartGeom_range_of (env := E) (n := n) (is := []) (a := a) (b := b)
    (es := [(m, 0)]) (pb := 0) (ok := true) (l := m) (r := 0) (inner := []) (k₁ := hi) (k₂ := lo)
    (arrayDims_of hd) (walkIndices_nil (env := E) [(m, 0)]) ha hb
    (by rw [labelOffset_desc0 hm, labelOffset_desc0 hm]; exact hlh)
  rw [this, labelOffset_desc0 hm, labelOffset_desc0 hm]
  simp

theorem arrayPartRead_part1 {E : IEnv} {n : String} {a b : PExpr} {m hi lo : Int}
    (hd : E.dims.lookup n = some [(m, 0)]) (hm : 0 ≤ m)
    (ha : evalInt E a = .ok hi) (hb : evalInt E b = .ok lo) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ m) :
    arrayPartRead E n [] .range a b = .slice (.ident n) lo.toNat (hi - lo + 1).toNat := by
  have hg := arrayPartGeom_part1 hd hm ha hb hlh
  have hc := dimCount_desc0 hm
  rw [arrayPartRead_of_inRange hg hlo (by omega)]
  simp

theorem arrayPartTarget_part1 {E : IEnv} {n : String} {a b : PExpr} {m hi lo : Int}
    (hd : E.dims.lookup n = some [(m, 0)]) (hm : 0 ≤ m)
    (ha : evalInt E a = .ok hi) (hb : evalInt E b = .ok lo) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ m) :
    arrayPartTarget E n [] .range a b =
      .ok (.slice n lo.toNat (hi - lo + 1).toNat, (hi - lo + 1).toNat) := by
  have hg := arrayPartGeom_part1 hd hm ha hb hlh
  have hc := dimCount_desc0 hm
  rw [arrayPartTarget_of_inRange hg hlo (by omega)]
  simp

/-- Part `[hi:lo]` of a row of a 2-D zero-based descending array. -/
theorem arrayPartGeom_part2 {E : IEnv} {n : String} {ie a b : PExpr} {m1 m2 k hi lo : Int}
    (hd : E.dims.lookup n = some [(m1, 0), (m2, 0)]) (hm2 : 0 ≤ m2)
    (hev : evalInt E ie = .ok k) (hk0 : 0 ≤ k) (hk1 : k ≤ m1)
    (ha : evalInt E a = .ok hi) (hb : evalInt E b = .ok lo) (hlh : lo ≤ hi) :
    arrayPartGeom E n [ie] .range a b =
      .ok (k * (m2 + 1), true, 1, dimCount m2 0, lo, hi) := by
  have hm1 : 0 ≤ m1 := by omega
  have hw := walkIndices_desc0_cons hm1 hev hk0 hk1 (walkIndices_nil (env := E) [(m2, 0)])
  have := arrayPartGeom_range_of (env := E) (n := n) (is := [ie]) (a := a) (b := b)
    (es := [(m1, 0), (m2, 0)]) (pb := k * (dimsStride [(m2, 0)] : Int) + 0) (ok := true)
    (l := m2) (r := 0) (inner := []) (k₁ := hi) (k₂ := lo)
    (arrayDims_of hd) hw ha hb
    (by rw [labelOffset_desc0 hm2, labelOffset_desc0 hm2]; exact hlh)
  rw [this, labelOffset_desc0 hm2, labelOffset_desc0 hm2]
  have h1 : ((dimCount m2 0 : Nat) : Int) = m2 + 1 := dimCount_desc0 hm2
  simp only [dimsStride, Nat.mul_one, h1, Int.add_zero]

theorem arrayPartRead_part2 {E : IEnv} {n : String} {ie a b : PExpr} {m1 m2 k hi lo : Int}
    (hd : E.dims.lookup n = some [(m1, 0), (m2, 0)])
    (hev : evalInt E ie = .ok k) (hk0 : 0 ≤ k) (hk1 : k ≤ m1)
    (ha : evalInt E a = .ok hi) (hb : evalInt E b = .ok lo) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ m2) :
    arrayPartRead E n [ie] .range a b =
      .slice (.ident n) (k * (m2 + 1) + lo).toNat (hi - lo + 1).toNat := by
  have hm2 : 0 ≤ m2 := by omega
  have hg := arrayPartGeom_part2 hd hm2 hev hk0 hk1 ha hb hlh
  have hc := dimCount_desc0 hm2
  rw [arrayPartRead_of_inRange hg hlo (by omega)]
  simp

theorem arrayPartTarget_part2 {E : IEnv} {n : String} {ie a b : PExpr} {m1 m2 k hi lo : Int}
    (hd : E.dims.lookup n = some [(m1, 0), (m2, 0)])
    (hev : evalInt E ie = .ok k) (hk0 : 0 ≤ k) (hk1 : k ≤ m1)
    (ha : evalInt E a = .ok hi) (hb : evalInt E b = .ok lo) (hlo : 0 ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ m2) :
    arrayPartTarget E n [ie] .range a b =
      .ok (.slice n (k * (m2 + 1) + lo).toNat (hi - lo + 1).toNat, (hi - lo + 1).toNat) := by
  have hm2 : 0 ≤ m2 := by omega
  have hg := arrayPartGeom_part2 hd hm2 hev hk0 hk1 ha hb hlh
  have hc := dimCount_desc0 hm2
  rw [arrayPartTarget_of_inRange hg hlo (by omega)]
  simp

/-! ## Inversion of the recognizers -/

theorem elemAcc?_cases {ds : List DeclT} {n : String} {is : List PExpr} {a : Acc}
    (h : elemAcc? ds n is = .ok a) :
    (∃ i x, is = [i] ∧ affOf? i = some x ∧ a = .cell1 n x) ∨
    (∃ i x w, is = [i] ∧ affOf? i = some x ∧ a = .row n w x) ∨
    (∃ i j x y w, is = [i, j] ∧ affOf? i = some x ∧ affOf? j = some y ∧ a = .cell2 n w x y) := by
  unfold elemAcc? at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    simp_all <;> (subst_vars; try simp) <;> (try (refine ⟨_, _, ⟨rfl, rfl⟩, ?_, ?_⟩ <;> assumption))

theorem partAcc?_cases {ds : List DeclT} {n : String} {is : List PExpr} {mode : PartMode}
    {hi lo : PExpr} {a : Acc} (h : partAcc? ds n is mode hi lo = .ok a) :
    mode = .range ∧
    ((∃ x y, is = [] ∧ affOf? hi = some x ∧ affOf? lo = some y ∧ a = .part1 n x y) ∨
     (∃ i r x y w, is = [i] ∧ affOf? i = some r ∧ affOf? hi = some x ∧ affOf? lo = some y ∧
        a = .part2 n w r x y)) := by
  unfold partAcc? at h
  split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> (try split at h) <;>
    (try split at h) <;> simp_all <;> (subst_vars; try simp) <;>
    (try (refine ⟨_, _, ⟨rfl, rfl⟩, ?_, ?_⟩ <;> assumption))

theorem tgtOf?_cases {ds : List DeclT} {l : PLhs} {a : Acc} (h : tgtOf? ds l = .ok a) :
    (∃ n, l = .ident n ∧ a = .whole n) ∨
    (∃ n i x, l = .bitSel n i ∧ affOf? i = some x ∧ bitAcc? ds n x = .ok a) ∨
    (∃ n is, l = .arrayElem n is ∧ elemAcc? ds n is = .ok a) ∨
    (∃ n is mode hi lo, l = .arrayPart n is mode hi lo ∧ partAcc? ds n is mode hi lo = .ok a) ∨
    (∃ n msb lsb, l = .partSel n msb lsb ∧ partAcc? ds n [] .range msb lsb = .ok a) := by
  cases l with
  | ident n =>
    left
    simp only [tgtOf?, Except.ok.injEq] at h
    exact ⟨n, rfl, h.symm⟩
  | bitSel n i =>
    right; left
    simp only [tgtOf?] at h
    rcases hx : affOf? i with _ | x
    · simp [hx] at h
    · simp only [hx] at h
      exact ⟨n, i, x, rfl, hx, h⟩
  | partSel n m l => right; right; right; right; exact ⟨n, m, l, rfl, h⟩
  | concat ps => simp [tgtOf?] at h
  | arrayElem n is => right; right; left; exact ⟨n, is, rfl, h⟩
  | arrayPart n is mode hi lo => right; right; right; left; exact ⟨n, is, mode, hi, lo, rfl, h⟩

theorem siteOf?_cases {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOf? ds pos p = .ok st) :
    (∃ t v rds, p = .assign t v ∧ rhsRds? ds v = .ok rds ∧ st = ⟨pos, .whole t, rds, p, [], v.cnames, v.rcounts⟩) ∨
    (∃ l v tg rds, p = .assignL l v ∧ tgtOf? ds l = .ok tg ∧ rhsRds? ds v = .ok rds ∧
      st = ⟨pos, tg, rds, p, [], v.cnames, v.rcounts⟩) := by
  cases p with
  | assign t v =>
    left
    simp only [siteOf?] at h
    rcases hr : rhsRds? ds v with e | rds
    · simp [hr] at h
    · simp only [hr, forceSite_eq, Except.ok.injEq] at h
      exact ⟨t, v, rds, rfl, hr, h.symm⟩
  | assignL l v =>
    right
    simp only [siteOf?] at h
    rcases ht : tgtOf? ds l with e | tg
    · simp [ht] at h
    · rcases hr : rhsRds? ds v with e | rds
      · simp [ht, hr] at h
      · simp only [ht, hr, forceSite_eq, Except.ok.injEq] at h
        exact ⟨l, v, tg, rds, rfl, ht, hr, h.symm⟩
  | alwaysFF _ _ => simp [siteOf?] at h
  | alwaysPlain _ _ => simp [siteOf?] at h
  | alwaysComb _ => simp [siteOf?] at h
  | alwaysFFR _ _ _ _ => simp [siteOf?] at h
  | unsupported _ _ => simp [siteOf?] at h

theorem siteOf?_proc {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOf? ds pos p = .ok st) : st.proc = p := by
  rcases siteOf?_cases h with ⟨t, v, rds, rfl, -, rfl⟩ | ⟨l, v, tg, rds, rfl, -, -, rfl⟩ <;> rfl

/-- The sites of the first fragment write one window. -/
theorem siteOf?_more {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOf? ds pos p = .ok st) : st.more = [] := by
  rcases siteOf?_cases h with ⟨t, v, rds, rfl, -, rfl⟩ | ⟨l, v, tg, rds, rfl, -, -, rfl⟩ <;> rfl

theorem signedCast_of_rds {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : rdsOf? ds e = .ok rs) :
    e.signedCast = false := by
  cases e <;> first | rfl | (simp [rdsOf?, rdsLeaf?, leafRd?] at h)

/-! ### The operators of the fragment (WP-G S2): inversions of the recognizer -/

theorem binOk_cases {op : SymBinOp} (h : binOk op = true) :
    op = .m0 .and ∨ op = .m0 .or ∨ op = .m0 .xor ∨ op = .land ∨ op = .lor ∨ op = .m0 .eq ∨
      op = .m0 .ne := by
  cases op with
  | m0 b => cases b <;> simp_all [binOk]
  | _ => simp_all [binOk]

theorem rdsOf?_binary {ds : List DeclT} {op : SymBinOp} {l r : PExpr} {rs : List Acc}
    (h : rdsOf? ds (.binary op l r) = .ok rs) :
    binOk op = true ∧ ∃ ra rb, rdsOf? ds l = .ok ra ∧ rdsOf? ds r = .ok rb ∧ rs = ra ++ rb := by
  simp only [rdsOf?] at h
  by_cases hb : binOk op = true
  · rw [if_pos hb] at h
    rcases hl : rdsOf? ds l with e1 | ra
    · simp [hl] at h
    · rcases hr : rdsOf? ds r with e2 | rb
      · simp [hl, hr] at h
      · simp only [hl, hr, Except.ok.injEq] at h
        exact ⟨hb, ra, rb, rfl, rfl, h.symm⟩
  · rw [if_neg hb] at h
    simp at h

theorem rdsOf?_unary {ds : List DeclT} {op : SymUnaryOp} {a : PExpr} {rs : List Acc}
    (h : rdsOf? ds (.unary op a) = .ok rs) :
    (op = .m0 .bnot ∨ op = .m0 .lnot) ∧ rdsOf? ds a = .ok rs := by
  cases op with
  | m0 u => cases u <;> simp_all [rdsOf?]
  | _ => simp [rdsOf?] at h

theorem rdsOf?_ternary {ds : List DeclT} {c t e : PExpr} {rs : List Acc}
    (h : rdsOf? ds (.ternary c t e) = .ok rs) :
    ∃ rc rt re, rdsOf? ds c = .ok rc ∧ rdsOf? ds t = .ok rt ∧ rdsOf? ds e = .ok re ∧
      rs = rc ++ rt ++ re := by
  simp only [rdsOf?] at h
  rcases hc : rdsOf? ds c with e1 | rc
  · simp [hc] at h
  · rcases ht : rdsOf? ds t with e2 | rt
    · simp [hc, ht] at h
    · rcases he : rdsOf? ds e with e3 | re
      · simp [hc, ht, he] at h
      · simp only [hc, ht, he, Except.ok.injEq] at h
        exact ⟨rc, rt, re, rfl, rfl, rfl, h.symm⟩

theorem rdsOf?_reduce {ds : List DeclT} {op : RedOp} {a : PExpr} {rs : List Acc}
    (h : rdsOf? ds (.reduce op a) = .ok rs) : rdsOf? ds a = .ok rs := by
  simpa [rdsOf?] using h

/-- `rdsLeaf?` is `leafRd?` in a one-element list. -/
theorem rdsLeaf_ok' {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : rdsLeaf? ds e = .ok rs) :
    ∃ a, leafRd? ds e = .ok a ∧ rs = [a] := by
  unfold rdsLeaf? at h
  rcases hl : leafRd? ds e with m | a
  · simp [hl] at h
  · simp only [hl, Except.ok.injEq] at h
    exact ⟨a, rfl, h.symm⟩

/-! ### WP-B2: inversions of the word-level recognizer `rdsOfW?` -/

theorem ctxOpW_cases {op : SymBinOp} (h : ctxOpW op = true) :
    op = .m0 .and ∨ op = .m0 .or ∨ op = .m0 .xor ∨ op = .m0 .add ∨ op = .m0 .sub ∨ op = .mul ∨
      ∃ c : CmpOp, op = .m0 c.ex := by
  cases op with
  | m0 b =>
      cases b <;> simp_all [ctxOpW]
      · exact ⟨.eq, rfl⟩
      · exact ⟨.ne, rfl⟩
      · exact ⟨.lt, rfl⟩
      · exact ⟨.le, rfl⟩
      · exact ⟨.gt, rfl⟩
      · exact ⟨.ge, rfl⟩
  | _ => simp_all [ctxOpW]

theorem selfOpW_cases {op : SymBinOp} (h : selfOpW op = true) : op = .land ∨ op = .lor := by
  cases op with
  | m0 b => cases b <;> simp_all [selfOpW]
  | _ => simp_all [selfOpW]

theorem selfOpW_false_of_ctx {op : SymBinOp} (h : ctxOpW op = true) : selfOpW op = false := by
  cases hs : selfOpW op
  · rfl
  · rcases selfOpW_cases hs with rfl | rfl <;> simp [ctxOpW] at h

theorem selfOpW_false_of_sh {op : SymBinOp} (h : shOpW op = true) : selfOpW op = false := by
  cases hs : selfOpW op
  · rfl
  · rcases selfOpW_cases hs with rfl | rfl <;> simp [shOpW] at h

theorem shOpW_cases {op : SymBinOp} (h : shOpW op = true) :
    (∃ s, op = .m0 (.shl s)) ∨ op = .m0 (.shr false) := by
  cases op with
  | m0 b =>
      cases b with
      | shl s => exact Or.inl ⟨s, rfl⟩
      | shr s => cases s <;> simp_all [shOpW]
      | _ => simp_all [shOpW]
  | _ => simp_all [shOpW]

theorem shSign_shr {op : SymBinOp} (h : op = .m0 (.shr false)) : shSign op = false := by
  subst h; rfl

theorem rdsOfW?_binary {ds : List DeclT} {op : SymBinOp} {l r : PExpr} {rs : List Acc}
    (h : rdsOfW? ds (.binary op l r) = .ok rs) :
    (ctxOpW op = true ∧ ∃ ra rb, rdsOfW? ds l = .ok ra ∧ rdsOfW? ds r = .ok rb ∧ rs = ra ++ rb) ∨
    (selfOpW op = true ∧ ∃ ra rb, rdsOf? ds l = .ok ra ∧ rdsOf? ds r = .ok rb ∧ rs = ra ++ rb) ∨
    (shOpW op = true ∧ ∃ ra rb, shLeftRd? ds (shSign op) l = .ok ra ∧ shAmtRd? ds r = .ok rb ∧ rs = ra ++ rb) := by
  simp only [rdsOfW?] at h
  by_cases hb : ctxOpW op = true
  · rw [if_pos hb] at h
    cases hm : mulOk op l r
    · simp [hm] at h
    rw [if_pos hm] at h
    left
    rcases hl : rdsOfW? ds l with e1 | ra
    · simp [hl] at h
    · rcases hr : rdsOfW? ds r with e2 | rb
      · simp [hl, hr] at h
      · simp only [hl, hr, Except.ok.injEq] at h
        exact ⟨hb, ra, rb, rfl, rfl, h.symm⟩
  · rw [if_neg hb] at h
    by_cases hs : selfOpW op = true
    · rw [if_pos hs] at h
      right; left
      rcases hl : rdsOf? ds l with e1 | ra
      · simp [hl] at h
      · rcases hr : rdsOf? ds r with e2 | rb
        · simp [hl, hr] at h
        · simp only [hl, hr, Except.ok.injEq] at h
          exact ⟨hs, ra, rb, rfl, rfl, h.symm⟩
    · rw [if_neg hs] at h
      by_cases hsh : shOpW op = true
      · rw [if_pos hsh] at h
        right; right
        rcases hl : shLeftRd? ds (shSign op) l with e1 | ra
        · simp [hl] at h
        · rcases hr : shAmtRd? ds r with e2 | rb
          · simp [hl, hr] at h
          · simp only [hl, hr, Except.ok.injEq] at h
            exact ⟨hsh, ra, rb, rfl, rfl, h.symm⟩
      · rw [if_neg hsh] at h
        simp at h

/-- A recognized product has a signal access among its factors (`mulOk`). -/
theorem rdsOfW?_mul {ds : List DeclT} {l r : PExpr} {rs : List Acc}
    (h : rdsOfW? ds (.binary .mul l r) = .ok rs) : (sigOpd l || sigOpd r) = true := by
  simp only [rdsOfW?, ctxOpW, ↓reduceIte] at h
  cases hm : mulOk .mul l r
  · simp [hm] at h
  · have e : (SymBinOp.mul != SymBinOp.mul) = false := rfl
    simpa [mulOk, e] using hm

/-- The operand of a shift is a literal, an unsized constant, or one signal access. -/
theorem shOpdRd?_cases {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : shOpdRd? ds e = .ok rs) :
    (∃ v, e = .lit v ∧ rs = []) ∨ (∃ k, e = .int k ∧ rs = []) ∨
      (∃ a, leafRd? ds e = .ok a ∧ rs = [a]) := by
  cases e with
  | lit v => left; exact ⟨v, rfl, by simpa [shOpdRd?] using h.symm⟩
  | int k => right; left; exact ⟨k, rfl, by simpa [shOpdRd?] using h.symm⟩
  | ident n =>
      right; right
      obtain ⟨a, ha, hrs⟩ := rdsLeaf_ok' (by simpa [shOpdRd?] using h)
      exact ⟨a, ha, hrs⟩
  | bitSel b i =>
      right; right
      obtain ⟨a, ha, hrs⟩ := rdsLeaf_ok' (by simpa [shOpdRd?] using h)
      exact ⟨a, ha, hrs⟩
  | partSel b m l =>
      right; right
      obtain ⟨a, ha, hrs⟩ := rdsLeaf_ok' (by simpa [shOpdRd?] using h)
      exact ⟨a, ha, hrs⟩
  | arrayElem n is =>
      right; right
      obtain ⟨a, ha, hrs⟩ := rdsLeaf_ok' (by simpa [shOpdRd?] using h)
      exact ⟨a, ha, hrs⟩
  | arrayPart n is m a b =>
      right; right
      obtain ⟨a', ha, hrs⟩ := rdsLeaf_ok' (by simpa [shOpdRd?] using h)
      exact ⟨a', ha, hrs⟩
  | _ => simp [shOpdRd?] at h

/-- The left operand of a shift of signedness `s`: a shift operand, possibly under the marker that keeps the
signedness (`Resize` for an unsigned shift, `SignedResize` for a signed one). -/
theorem shLeftRd?_cases {ds : List DeclT} {s : Bool} {e : PExpr} {rs : List Acc} (h : shLeftRd? ds s e = .ok rs) :
    ∃ x, (e = x ∨ (s = false ∧ ∃ m, e = .resize m x) ∨ (s = true ∧ ∃ m, e = .signedResize m x)) ∧
      shOpdRd? ds x = .ok rs := by
  cases e with
  | resize m x =>
      cases s
      · exact ⟨x, Or.inr (Or.inl ⟨rfl, m, rfl⟩), by simpa [shLeftRd?] using h⟩
      · simp [shLeftRd?] at h
  | signedResize m x =>
      cases s
      · simp [shLeftRd?] at h
      · exact ⟨x, Or.inr (Or.inr ⟨rfl, m, rfl⟩), by simpa [shLeftRd?] using h⟩
  | _ => exact ⟨_, Or.inl rfl, by simpa [shLeftRd?] using h⟩

theorem rdsOfW?_unary {ds : List DeclT} {op : SymUnaryOp} {a : PExpr} {rs : List Acc}
    (h : rdsOfW? ds (.unary op a) = .ok rs) :
    (op = .m0 .bnot ∧ rdsOfW? ds a = .ok rs) ∨ (op = .m0 .lnot ∧ rdsOf? ds a = .ok rs) := by
  cases op with
  | m0 u => cases u <;> simp_all [rdsOfW?]
  | _ => simp [rdsOfW?] at h

theorem rdsOfW?_ternary {ds : List DeclT} {c t e : PExpr} {rs : List Acc}
    (h : rdsOfW? ds (.ternary c t e) = .ok rs) :
    ∃ rc rt re, rdsOf? ds c = .ok rc ∧ rdsOfW? ds t = .ok rt ∧ rdsOfW? ds e = .ok re ∧
      rs = rc ++ rt ++ re := by
  simp only [rdsOfW?] at h
  rcases hc : rdsOf? ds c with e1 | rc
  · simp [hc] at h
  · rcases ht : rdsOfW? ds t with e2 | rt
    · simp [hc, ht] at h
    · rcases he : rdsOfW? ds e with e3 | re
      · simp [hc, ht, he] at h
      · simp only [hc, ht, he, Except.ok.injEq] at h
        exact ⟨rc, rt, re, rfl, rfl, rfl, h.symm⟩

theorem rdsOfW?_reduce {ds : List DeclT} {op : RedOp} {a : PExpr} {rs : List Acc}
    (h : rdsOfW? ds (.reduce op a) = .ok rs) : rdsOf? ds a = .ok rs := by
  simpa [rdsOfW?] using h

theorem resizeRd?_ok {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : resizeRd? ds e = .ok rs) :
    ∃ a, leafRd? ds e = .ok a ∧ rs = [a] := by
  cases e with
  | ident n =>
      simp only [resizeRd?] at h
      rcases hl : leafRd? ds (.ident n) with m | a
      · simp [hl] at h
      · simp only [hl, Except.ok.injEq] at h
        exact ⟨a, rfl, h.symm⟩
  | bitSel b i =>
      simp only [resizeRd?] at h
      rcases hl : leafRd? ds (.bitSel b i) with m | a
      · simp [hl] at h
      · simp only [hl, Except.ok.injEq] at h
        exact ⟨a, rfl, h.symm⟩
  | partSel b msb lsb =>
      simp only [resizeRd?] at h
      rcases hl : leafRd? ds (.partSel b msb lsb) with m | a
      · simp [hl] at h
      · simp only [hl, Except.ok.injEq] at h
        exact ⟨a, rfl, h.symm⟩
  | arrayElem n is =>
      simp only [resizeRd?] at h
      rcases hl : leafRd? ds (.arrayElem n is) with m | a
      · simp [hl] at h
      · simp only [hl, Except.ok.injEq] at h
        exact ⟨a, rfl, h.symm⟩
  | arrayPart n is mode hi lo =>
      simp only [resizeRd?] at h
      rcases hl : leafRd? ds (.arrayPart n is mode hi lo) with m | a
      · simp [hl] at h
      · simp only [hl, Except.ok.injEq] at h
        exact ⟨a, rfl, h.symm⟩
  | _ => simp [resizeRd?] at h

/-- A width conversion is accepted around a sized literal (no read) and around one access. -/
theorem rdsOfW?_resize {ds : List DeclT} {m : Nat} {e : PExpr} {rs : List Acc}
    (h : rdsOfW? ds (.resize m e) = .ok rs) :
    (∃ v, e = .lit v ∧ rs = []) ∨ ((∀ v, e ≠ .lit v) ∧ ∃ a, leafRd? ds e = .ok a ∧ rs = [a]) ∨
      (e.isOpW = true ∧ rdsOfW? ds e = .ok rs) := by
  cases e with
  | lit v =>
      left
      simp [rdsOfW?] at h
      exact ⟨v, rfl, h⟩
  | ident n =>
      right; left
      exact ⟨(fun v h => by cases h), resizeRd?_ok (by simpa [rdsOfW?] using h)⟩
  | bitSel b i =>
      right; left
      exact ⟨(fun v h => by cases h), resizeRd?_ok (by simpa [rdsOfW?] using h)⟩
  | partSel b msb lsb =>
      right; left
      exact ⟨(fun v h => by cases h), resizeRd?_ok (by simpa [rdsOfW?] using h)⟩
  | arrayElem n is =>
      right; left
      exact ⟨(fun v h => by cases h), resizeRd?_ok (by simpa [rdsOfW?] using h)⟩
  | arrayPart n is mo a b =>
      right; left
      exact ⟨(fun v h => by cases h), resizeRd?_ok (by simpa [rdsOfW?] using h)⟩
  | binary op l r => right; right; exact ⟨rfl, h⟩
  | unary op a => right; right; exact ⟨rfl, h⟩
  | ternary c t f => right; right; exact ⟨rfl, h⟩
  | reduce op a => right; right; exact ⟨rfl, h⟩
  | int v => right; right; exact ⟨rfl, h⟩
  | concat ps => right; right; exact ⟨rfl, h⟩
  | _ => simp [rdsOfW?] at h

theorem signedCast_of_rdsW {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : rdsOfW? ds e = .ok rs) :
    e.signedCast = false := by
  cases e <;> first | rfl | (simp [rdsOfW?, rdsLeaf?, leafRd?] at h)

/-! ## Derived definitions on the summary -/

/-- Structural well-formedness of a summary: decidable closed data, discharged by `decide`. -/
def Summary.StructOk (s : Summary) : Prop :=
  s.declNames.Nodup ∧
  (∀ ls ∈ s.lsites, ∀ n ∈ ls.site.names, n ∈ s.declNames) ∧
  (∀ ls ∈ s.lsites, ∀ a ∈ ls.site.tgt :: ls.site.more, a.name ∉ s.inputNames) ∧
  (∀ ls ∈ s.lsites, ∀ n ∈ ls.site.affNames, n ∈ ls.hdrs.map (·.g) ++ s.params) ∧
  (∀ p ∈ s.hdrPaths, (p.map (·.g) ++ s.params).Nodup ∧
    ∀ h ∈ p, (∀ n ∈ h.bound.names, n ∈ s.params) ∧ 0 ≤ h.c0) ∧
  (∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, n ∈ s.params) ∧
  (∀ ls ∈ s.lsites, ∀ a ∈ ls.site.tgt :: (ls.site.more ++ ls.site.rds), s.accOk a = true) ∧
  s.lsites.Pairwise (fun a b => a.key ≠ b.key)

instance (s : Summary) : Decidable s.StructOk := by
  unfold Summary.StructOk; infer_instance

namespace Summary

variable (s : Summary)

/-- Dimension facts of an access (nonnegativity of the row width's label): discharged by the
tactic's `omega`. -/
def DimNum (σ : String → Int) : Acc → Prop
  | .row n _ _ => 0 ≤ s.dm σ n 1
  | _ => True

/-- The in-range facts of an access, in the form a player reads: indices nonnegative and inside the
declared dimensions (`dm σd n k` is the most significant label of the `k`-th dimension of `n`). -/
def InR (σd σs : String → Int) : Acc → Prop
  | .whole _ => True
  | .bit _ a => 0 ≤ a.eval σs
  | .cell1 n a => 0 ≤ a.eval σs ∧ a.eval σs ≤ s.dm σd n 0
  | .row n _ r => 0 ≤ r.eval σs ∧ r.eval σs ≤ s.dm σd n 0
  | .cell2 n _ r c =>
      0 ≤ r.eval σs ∧ r.eval σs ≤ s.dm σd n 0 ∧ 0 ≤ c.eval σs ∧ c.eval σs ≤ s.dm σd n 1
  | .part1 n hi lo => 0 ≤ lo.eval σs ∧ lo.eval σs ≤ hi.eval σs ∧ hi.eval σs ≤ s.dm σd n 0
  | .part2 n _ r hi lo =>
      0 ≤ r.eval σs ∧ r.eval σs ≤ s.dm σd n 0 ∧ 0 ≤ lo.eval σs ∧ lo.eval σs ≤ hi.eval σs ∧
        hi.eval σs ≤ s.dm σd n 1

/-- A site's write window lies inside its declared signal (`inWidth`). -/
def InWin (σd σs : String → Int) (st : TSite) : Prop :=
  s.InR σd σs st.tgt ∧
    (match st.tgt with
     | .bit n a => a.eval σs + 1 ≤ (s.dw σd n : Int)
     | _ => True)

/-- The facts the tactic closes by `omega`: reads in range, dimensions nonnegative, loop bounds
within the generate fuel. The fuel is `(Σ|args| + 2)² + 64` (`PDesign.surfaceFuel`), so any loop
count affine in the parameters with coefficient sum at most 4 is within it: the bound used here is
the linear `4 · Σ|args| + 60` (a loop over `2*N` columns is admitted; svGolf `mul` tree design). -/
def AutoObl (σ : String → Int) (args : List Int) : Prop :=
  (∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' => ∀ r ∈ ls.site.rds, s.InR σ σ' r) ∧
  (∀ ls ∈ s.lsites, ∀ a ∈ ls.site.tgt :: (ls.site.more ++ ls.site.rds), s.DimNum σ a) ∧
  (∀ p ∈ s.hdrPaths, ∀ h ∈ p, (h.bound.eval σ - h.c0).toNat ≤ 4 * (args.map Int.natAbs).sum + 60)

/-- A FURTHER target access of a site (`TSite.more`) lies inside its declared signal: `InWin` for one access. -/
def InWinAcc (σd σs : String → Int) (a : Acc) : Prop :=
  s.InR σd σs a ∧
    (match a with
     | .bit n x => x.eval σs + 1 ≤ (s.dw σd n : Int)
     | _ => True)

/-- **Every write window in range.** The head window of each site (`InWin`), and, for a design with a site that
writes several windows (WP-G S1b), the further windows. The second conjunct is guarded by the decidable test
"no site has a further window", which `simp` decides FIRST (`↓reduceIte`) and so drops unread: for every design
without such a site the obligation normalizes exactly as before. -/
def InRangeObl (σ : String → Int) : Prop :=
  (∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' => s.InWin σ σ' ls.site) ∧
  (if (∀ b ∈ s.lsites, b.site.more = []) then True else
    ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' => ∀ a ∈ ls.site.more,
      s.InR σ σ' a ∧
        (match a with
         | .bit n x => x.eval σ' + 1 ≤ (s.dw σ n : Int)
         | _ => True)) ∧
  (if (∀ b ∈ s.lsites, b.site.rcounts = []) then True else
    ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' => ∀ c ∈ ls.site.rcounts, 0 ≤ c.eval σ')

/-- The sites that drive (a window of) the signal `n`. -/
def writersOf (n : String) : List LSite := s.lsites.filter fun b => b.site.tgt.name == n

/-- **One driver per bit** for a pair of located sites: at every pair of loop valuations that are
not the same instance, the write windows are disjoint. -/
def DisjOne (σ : String → Int) (a b : LSite) : Prop :=
  Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
    a.id σ1 ≠ b.id σ2 →
      Win.overlaps (a.site.tgt.win σ1 (s.dw σ)) (b.site.tgt.win σ2 (s.dw σ)) = false

/-- **The windows of ONE instance of a site pairwise disjoint** (a body of several windows writes each bit once). -/
def DisjWithin (σ : String → Int) : Prop :=
  ∀ a ∈ s.lsites, Loops.all a.hdrs σ fun σ1 =>
    (a.site.tgt :: a.site.more).Pairwise fun x y =>
      Win.overlaps (x.win σ1 (s.dw σ)) (y.win σ1 (s.dw σ)) = false

/-- **One driver per bit for the FURTHER windows of the sites that write several** (WP-G S1b): every window `y`
beyond the first of a site `b`, against every window `x` of every site `a`, at every pair of loop valuations
that are not the same instance; and the windows of one instance of a site pairwise disjoint (`DisjWithin`). (The
head windows against each other are `DisjObl`'s first two conjuncts.) -/
def DisjMore (σ : String → Int) : Prop :=
  (∀ a ∈ s.lsites, ∀ b ∈ s.lsites, ∀ y ∈ b.site.more, ∀ x ∈ a.site.tgt :: a.site.more,
    Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
      a.id σ1 ≠ b.id σ2 →
        Win.overlaps (x.win σ1 (s.dw σ)) (y.win σ2 (s.dw σ)) = false) ∧
  s.DisjWithin σ

def DisjObl (σ : String → Int) : Prop :=
  s.lsites.Pairwise (s.DisjOne σ) ∧ (∀ a ∈ s.lsites, s.DisjOne σ a a) ∧
  (if (∀ b ∈ s.lsites, b.site.more = []) then True else
    (∀ a ∈ s.lsites, ∀ b ∈ s.lsites, ∀ y ∈ b.site.more, ∀ x ∈ a.site.tgt :: a.site.more,
      Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
        a.id σ1 ≠ b.id σ2 →
          Win.overlaps (x.win σ1 (s.dw σ)) (y.win σ2 (s.dw σ)) = false) ∧
    (∀ a ∈ s.lsites, Loops.all a.hdrs σ fun σ1 =>
      (a.site.tgt :: a.site.more).Pairwise fun x y =>
        Win.overlaps (x.win σ1 (s.dw σ)) (y.win σ1 (s.dw σ)) = false))

/-- **The rank decreases along every read of a FURTHER window** (WP-G S1b): the same obligation for the windows
beyond the first of the sites that write several. The writer is the SITE (`b.id`), so the rank of a body is one
value whatever the number of its windows. -/
def RankMore (R : SiteId → SiteId → Prop) (σ : String → Int) : Prop :=
  ∀ b ∈ s.lsites, ∀ y ∈ b.site.more, ∀ a ∈ s.lsites, ∀ r ∈ a.site.rds, y.name = r.name →
    Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
      ReadWin.overlaps (r.rd σ1) (y.win σ2 (s.dw σ)) = true → R (b.id σ2) (a.id σ1)

/-- **The rank decreases along every read** (design principle 13: sites by identity): whenever a
read window of `a` overlaps the window `b` writes, `b`'s identity is related to `a`'s by `R`
(writer first). -/
def RankObl' (R : SiteId → SiteId → Prop) (σ : String → Int) : Prop :=
  (∀ a ∈ s.lsites, ∀ r ∈ a.site.rds, ∀ b ∈ s.writersOf r.name,
    Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
      ReadWin.overlaps (r.rd σ1) (b.site.tgt.win σ2 (s.dw σ)) = true → R (b.id σ2) (a.id σ1)) ∧
  (if (∀ b ∈ s.lsites, b.site.more = []) then True else
    ∀ b ∈ s.lsites, ∀ y ∈ b.site.more, ∀ a ∈ s.lsites, ∀ r ∈ a.site.rds, y.name = r.name →
      Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
        ReadWin.overlaps (r.rd σ1) (y.win σ2 (s.dw σ)) = true → R (b.id σ2) (a.id σ1))

/-- … for a `Nat`-valued rank over site identities. -/
def RankObl (ρ : SiteId → Nat) (σ : String → Int) : Prop :=
  s.RankObl' (fun w r => ρ w < ρ r) σ

/-- … for a lexicographic key over site identities (row, column, phase). -/
def LexObl (κ : SiteId → Key) (σ : String → Int) : Prop :=
  s.RankObl' (fun w r => KLt (κ w) (κ r)) σ

end Summary

/-! ### The guarded conjuncts as plain obligations (WP-G S1b, gate c2)

The guarded conjuncts of `InRangeObl`, `DisjObl` and `RankObl'` say nothing when no site has a further window, and the
obligation proper when one does; as hypotheses they are used through the extractors below, which hold in both cases
(the vacuous one included). -/

theorem Summary.InRangeObl.rc_all {s : Summary} {σ : String → Int} (hin : s.InRangeObl σ) :
    ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' => ∀ c ∈ ls.site.rcounts, 0 ≤ c.eval σ' := by
  obtain ⟨-, -, h⟩ := hin
  by_cases hc : ∀ b ∈ s.lsites, b.site.rcounts = []
  · intro ls hls
    rw [Loops.all_iff]
    intro σ' _ c hc'
    rw [hc ls hls] at hc'
    exact absurd hc' (by simp)
  · rw [if_neg hc] at h
    exact h

theorem Summary.InRangeObl.more_all {s : Summary} {σ : String → Int} (hin : s.InRangeObl σ) :
    ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' => ∀ a ∈ ls.site.more, s.InWinAcc σ σ' a := by
  obtain ⟨-, h, -⟩ := hin
  by_cases hc : ∀ b ∈ s.lsites, b.site.more = []
  · intro ls hls
    rw [Loops.all_iff]
    intro σ' _ a ha
    rw [hc ls hls] at ha
    exact absurd ha (by simp)
  · rw [if_neg hc] at h
    intro ls hls
    exact (Loops.all_iff _ _ _).mpr fun σ' hr a ha => (h ls hls |> (Loops.all_iff _ _ _).mp) σ' hr a ha

/-- A summary none of whose sites has a further window has pairwise disjoint windows per site, trivially. -/
theorem Summary.DisjWithin.of_single {s : Summary} {σ : String → Int}
    (hc : ∀ b ∈ s.lsites, b.site.more = []) : s.DisjWithin σ := by
  intro a ha
  rw [Loops.all_iff]
  intro σ1 _
  rw [hc a ha]
  exact List.pairwise_singleton _ _

theorem Summary.DisjObl.more_all {s : Summary} {σ : String → Int} (hd : s.DisjObl σ) : s.DisjMore σ := by
  obtain ⟨-, -, h⟩ := hd
  by_cases hc : ∀ b ∈ s.lsites, b.site.more = []
  · refine ⟨fun a ha b hb y hy => ?_, Summary.DisjWithin.of_single hc⟩
    rw [hc b hb] at hy
    exact absurd hy (by simp)
  · rw [if_neg hc] at h
    exact h

theorem Summary.DisjObl.within_all {s : Summary} {σ : String → Int} (hd : s.DisjObl σ) : s.DisjWithin σ :=
  hd.more_all.2

theorem Summary.RankObl'.more_all {s : Summary} {R : SiteId → SiteId → Prop} {σ : String → Int}
    (hr : s.RankObl' R σ) : s.RankMore R σ := by
  obtain ⟨-, h⟩ := hr
  by_cases hc : ∀ b ∈ s.lsites, b.site.more = []
  · intro b hb y hy
    rw [hc b hb] at hy
    exact absurd hy (by simp)
  · rw [if_neg hc] at h
    exact h

/-! ## Expression-level facts -/

/-- What the summary promises about an instantiated expression. -/
def RdOK (σ : String → Int) (rs : List Acc) (x : Expr2) : Prop :=
  x.unsupportedFree = true ∧ (∀ r ∈ x.reads, r ∈ rs.map (Acc.rd σ)) ∧
    ∀ i ∈ x.idents, i ∈ rs.map Acc.name

theorem RdOK.binary {σ : String → Int} {ra rb : List Acc} {x y : Expr2} (op : BinOp)
    (hx : RdOK σ ra x) (hy : RdOK σ rb y) : RdOK σ (ra ++ rb) (.binary op x y) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · simp [Expr2.unsupportedFree, hx1, hy1]
  · intro r hr
    simp only [Expr2.reads, List.mem_append] at hr
    simp only [List.map_append, List.mem_append]
    rcases hr with h | h
    · exact Or.inl (hx2 r h)
    · exact Or.inr (hy2 r h)
  · intro i hi
    simp only [Expr2.idents, List.mem_append] at hi
    simp only [List.map_append, List.mem_append]
    rcases hi with h | h
    · exact Or.inl (hx3 i h)
    · exact Or.inr (hy3 i h)

theorem RdOK.resize {σ : String → Int} {rs : List Acc} {x : Expr2} (w : Nat)
    (h : RdOK σ rs x) : RdOK σ rs (.resize w x) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa [Expr2.unsupportedFree] using h1,
    fun r hr => h2 r (by simpa [Expr2.reads] using hr),
    fun i hi => h3 i (by simpa [Expr2.idents] using hi)⟩

theorem RdOK.repl {σ : String → Int} {rs : List Acc} {x : Expr2} (n : Nat)
    (h : RdOK σ rs x) : RdOK σ rs (.repl n x) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa [Expr2.unsupportedFree] using h1, by simpa [Expr2.reads] using h2,
    by simpa [Expr2.idents] using h3⟩

theorem RdOK.unary {σ : String → Int} {rs : List Acc} {x : Expr2} (op : UnaryOp)
    (h : RdOK σ rs x) : RdOK σ rs (.unary op x) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa [Expr2.unsupportedFree] using h1,
    fun r hr => h2 r (by simpa [Expr2.reads] using hr),
    fun i hi => h3 i (by simpa [Expr2.idents] using hi)⟩

theorem RdOK.reduce {σ : String → Int} {rs : List Acc} {x : Expr2} (op : RedOp)
    (h : RdOK σ rs x) : RdOK σ rs (.reduce op x) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa [Expr2.unsupportedFree] using h1,
    fun r hr => h2 r (by simpa [Expr2.reads] using hr),
    fun i hi => h3 i (by simpa [Expr2.idents] using hi)⟩

theorem RdOK.logical {σ : String → Int} {ra rb : List Acc} {x y : Expr2} (isAnd : Bool)
    (hx : RdOK σ ra x) (hy : RdOK σ rb y) : RdOK σ (ra ++ rb) (.logical isAnd x y) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · simp [Expr2.unsupportedFree, hx1, hy1]
  · intro r hr
    simp only [Expr2.reads, List.mem_append] at hr
    simp only [List.map_append, List.mem_append]
    rcases hr with h | h
    · exact Or.inl (hx2 r h)
    · exact Or.inr (hy2 r h)
  · intro i hi
    simp only [Expr2.idents, List.mem_append] at hi
    simp only [List.map_append, List.mem_append]
    rcases hi with h | h
    · exact Or.inl (hx3 i h)
    · exact Or.inr (hy3 i h)

theorem RdOK.ternary {σ : String → Int} {ra rb rc : List Acc} {g a b : Expr2} (hg : RdOK σ ra g)
    (ha : RdOK σ rb a) (hb : RdOK σ rc b) : RdOK σ (ra ++ rb ++ rc) (.ternary g a b) := by
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨?_, fun r hr => ?_, fun i hi => ?_⟩
  · simp [Expr2.unsupportedFree, g1, a1, b1]
  · simp only [Expr2.reads, List.mem_append] at hr
    simp only [List.map_append, List.mem_append]
    rcases hr with (h | h) | h
    · exact Or.inl (Or.inl (g2 r h))
    · exact Or.inl (Or.inr (a2 r h))
    · exact Or.inr (b2 r h)
  · simp only [Expr2.idents, List.mem_append] at hi
    simp only [List.map_append, List.mem_append]
    rcases hi with (h | h) | h
    · exact Or.inl (Or.inl (g3 i h))
    · exact Or.inl (Or.inr (a3 i h))
    · exact Or.inr (b3 i h)

theorem RdOK.concat_cons {σ : String → Int} {ra rb : List Acc} {x : Expr2} {l : List Expr2}
    (hx : RdOK σ ra x) (hl : RdOK σ rb (.concat l.toArray)) :
    RdOK σ (ra ++ rb) (.concat (x :: l).toArray) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hl1, hl2, hl3⟩ := hl
  have e1 : (Expr2.concat (x :: l).toArray).unsupportedFree =
      (x.unsupportedFree && (Expr2.concat l.toArray).unsupportedFree) := by
    simp [Expr2.unsupportedFree, Expr2.listUnsupportedFree]
  have e2 : (Expr2.concat (x :: l).toArray).reads = x.reads ++ (Expr2.concat l.toArray).reads := by
    simp [Expr2.reads, Expr2.listReads]
  have e3 : (Expr2.concat (x :: l).toArray).idents = x.idents ++ (Expr2.concat l.toArray).idents := by
    simp [Expr2.idents, Expr2.listIdents]
  refine ⟨by rw [e1, hx1, hl1]; rfl, ?_, ?_⟩
  · intro r hr
    rw [e2] at hr
    simp only [List.mem_append] at hr
    simp only [List.map_append, List.mem_append]
    rcases hr with h | h
    · exact Or.inl (hx2 r h)
    · exact Or.inr (hl2 r h)
  · intro i hi
    rw [e3] at hi
    simp only [List.mem_append] at hi
    simp only [List.map_append, List.mem_append]
    rcases hi with h | h
    · exact Or.inl (hx3 i h)
    · exact Or.inr (hl3 i h)

theorem RdOK.concat_nil {σ : String → Int} : RdOK σ [] (.concat (#[] : Array Expr2)) := by
  simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents, Expr2.listUnsupportedFree,
    Expr2.listReads, Expr2.listIdents]

/-- `fitExpr2` is `instExpr2` at some context, possibly under one `resize`. -/
theorem fitExpr2_cases (E : IEnv) (elems : List (String × Nat)) (ctx : Option Nat) (e : PExpr)
    (hs : e.signedCast = false) :
    (∃ c, fitExpr2 E elems ctx e = instExpr2 E elems c e) ∨
    (∃ w c, fitExpr2 E elems ctx e = .resize w (instExpr2 E elems c e)) := by
  unfold fitExpr2
  cases ctx with
  | none => exact Or.inl ⟨none, rfl⟩
  | some tw =>
    by_cases hr : rigidExpr e = true
    · simp only [hr, if_true]
      rcases hw : selfWidth2 E elems e with _ | sw
      · exact Or.inl ⟨_, rfl⟩
      · by_cases hsw : (sw == tw) = true
        · simp only [hsw, if_true]
          exact Or.inl ⟨_, rfl⟩
        · have hsw' : (sw == tw) = false := by simpa using hsw
          simp only [hsw', hs, Bool.and_false, Bool.false_eq_true, if_false]
          exact Or.inr ⟨tw, _, rfl⟩
    · have hr' : rigidExpr e = false := by simpa using hr
      simp only [hr', Bool.false_eq_true, if_false]
      exact Or.inl ⟨_, rfl⟩

theorem RdOK.fit {σ : String → Int} {rs : List Acc} {E : IEnv} {elems : List (String × Nat)}
    {e : PExpr} (hs : e.signedCast = false)
    (h : ∀ c, RdOK σ rs (instExpr2 E elems c e)) (ctx : Option Nat) :
    RdOK σ rs (fitExpr2 E elems ctx e) := by
  rcases fitExpr2_cases E elems ctx e hs with ⟨c, hc⟩ | ⟨w, c, hc⟩
  · rw [hc]; exact h c
  · rw [hc]; exact RdOK.resize w (h c)

theorem RdOK.resizeSigned {σ : String → Int} {rs : List Acc} {x : Expr2} (w : Nat)
    (h : RdOK σ rs x) : RdOK σ rs (.resizeSigned w x) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa [Expr2.unsupportedFree] using h1,
    fun r hr => h2 r (by simpa [Expr2.reads] using hr),
    fun i hi => h3 i (by simpa [Expr2.idents] using hi)⟩

theorem RdOK.fitDiv {σ : String → Int} {rs : List Acc} {x : Expr2} (h : RdOK σ rs x) (s : Bool)
    (c w : Option Nat) : RdOK σ rs (fitDivOperand2 s c w x) := by
  cases c <;> cases w <;> simp only [fitDivOperand2]
  · exact h
  · exact h
  · exact h
  · split
    · exact h
    · cases s
      · simp only [Bool.false_eq_true, if_false]
        exact RdOK.resize _ h
      · simp only [if_true]
        exact RdOK.resizeSigned _ h

theorem RdOK.ctxTrunc {σ : String → Int} {rs : List Acc} {x : Expr2} (h : RdOK σ rs x) (ctx ow : Option Nat) :
    RdOK σ rs (ctxTrunc2 ctx ow x) := by
  cases ctx <;> cases ow <;> simp only [ctxTrunc2]
  · exact h
  · exact h
  · exact h
  · split
    · exact h
    · exact RdOK.resize _ h

/-- A gate node instantiates to the gate over two `fitExpr2`s at one context. -/
theorem instExpr2_gate (E : IEnv) (elems : List (String × Nat)) (ctx : Option Nat) (bop : BinOp)
    (hb : bop = .and ∨ bop = .or ∨ bop = .xor) (l r : PExpr) :
    ∃ c, instExpr2 E elems ctx (.binary (.m0 bop) l r) =
      .binary bop (fitExpr2 E elems c l) (fitExpr2 E elems c r) := by
  rcases hb with rfl | rfl | rfl <;> cases ctx <;> simp [instExpr2] <;>
    first | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl⟩

/-! ## The new operators of the fragment (WP-G S2): `instExpr2` / `selfWidth2` / `rigidMax2` equations

One equation per constructor, the facts the combined shape theorem (`CombEq.skT_shape`) and the read lemmas
rest on. Spike: `svgolf/design/always-comb/spike/S2Spike.lean`. -/

section s2eqns
variable {env : IEnv} {elems : List (String × Nat)}

theorem ie_lnot (ctx : Option Nat) (a : PExpr) :
    instExpr2 env elems ctx (.unary (.m0 .lnot) a) = .unary .lnot (instExpr2 env elems none a) := by
  simp [instExpr2]

theorem ie_bnot_some (w : Nat) (a : PExpr) (h : (rigidMax2 env elems a).getD w ≤ w) :
    instExpr2 env elems (some w) (.unary (.m0 .bnot) a) =
      .unary .bnot (fitExpr2 env elems (some w) a) := by
  simp [instExpr2, h]

theorem ie_bnot_none (a : PExpr) :
    instExpr2 env elems none (.unary (.m0 .bnot) a) =
      .unary .bnot (instExpr2 env elems (selfWidth2 env elems a) a) := by
  simp [instExpr2]

/-- `~a` at any context: `~` over an instantiation or a fit of `a`, possibly under one `resize`. -/
theorem ie_bnot_cases (ctx : Option Nat) (a : PExpr) :
    (∃ c, instExpr2 env elems ctx (.unary (.m0 .bnot) a) = .unary .bnot (instExpr2 env elems c a)) ∨
    (∃ c, instExpr2 env elems ctx (.unary (.m0 .bnot) a) = .unary .bnot (fitExpr2 env elems c a)) ∨
    (∃ w c, instExpr2 env elems ctx (.unary (.m0 .bnot) a) =
      .resize w (.unary .bnot (fitExpr2 env elems c a))) := by
  cases ctx with
  | none => exact Or.inl ⟨selfWidth2 env elems a, ie_bnot_none a⟩
  | some w =>
      by_cases h : (rigidMax2 env elems a).getD w ≤ w
      · exact Or.inr (Or.inl ⟨some w, ie_bnot_some w a h⟩)
      · exact Or.inr (Or.inr ⟨w, some ((rigidMax2 env elems a).getD w), by simp [instExpr2, h]⟩)

theorem ie_ternary_some (w : Nat) (c t e : PExpr) :
    instExpr2 env elems (some w) (.ternary c t e) =
      .ternary (instExpr2 env elems none c) (fitExpr2 env elems (some w) t)
        (fitExpr2 env elems (some w) e) := by
  simp [instExpr2]

theorem ie_ternary_none (w : Nat) (c t e : PExpr)
    (ht : selfWidth2 env elems t = some w) (he : selfWidth2 env elems e = some w) :
    instExpr2 env elems none (.ternary c t e) =
      .ternary (instExpr2 env elems none c) (fitExpr2 env elems (some w) t)
        (fitExpr2 env elems (some w) e) := by
  simp [instExpr2, ht, he]

theorem ie_ternary_cases (ctx : Option Nat) (c t e : PExpr) :
    ∃ a, instExpr2 env elems ctx (.ternary c t e) =
      .ternary (instExpr2 env elems none c) (fitExpr2 env elems a t) (fitExpr2 env elems a e) := by
  cases ctx <;> simp [instExpr2] <;> first | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl⟩

theorem ie_land (ctx : Option Nat) (l r : PExpr) :
    instExpr2 env elems ctx (.binary .land l r) =
      .logical true (instExpr2 env elems (selfWidth2 env elems l) l)
        (instExpr2 env elems (selfWidth2 env elems r) r) := by
  simp [instExpr2] <;> rfl

theorem ie_lor (ctx : Option Nat) (l r : PExpr) :
    instExpr2 env elems ctx (.binary .lor l r) =
      .logical false (instExpr2 env elems (selfWidth2 env elems l) l)
        (instExpr2 env elems (selfWidth2 env elems r) r) := by
  simp [instExpr2] <;> rfl

theorem ie_reduce (ctx : Option Nat) (op : RedOp) (a : PExpr) :
    instExpr2 env elems ctx (.reduce op a) =
      .reduce op (instExpr2 env elems (selfWidth2 env elems a) a) := by
  simp [instExpr2]

/-- A comparison at any context: the two operands fitted to ONE width (`instExpr2`'s comparison arm). -/
theorem ie_cmp_cases (c : CmpOp) (ctx : Option Nat) (l r : PExpr) :
    ∃ cx, instExpr2 env elems ctx (.binary (.m0 c.ex) l r) =
      .binary c.ex (fitExpr2 env elems cx l) (fitExpr2 env elems cx r) := by
  cases ctx <;> cases c <;> simp [instExpr2, CmpOp.ex] <;> first | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl⟩

theorem ie_eq_cases (ctx : Option Nat) (l r : PExpr) :
    ∃ c, instExpr2 env elems ctx (.binary (.m0 .eq) l r) =
      .binary .eq (fitExpr2 env elems c l) (fitExpr2 env elems c r) := by
  cases ctx <;> simp [instExpr2] <;> first | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl⟩

theorem ie_ne_cases (ctx : Option Nat) (l r : PExpr) :
    ∃ c, instExpr2 env elems ctx (.binary (.m0 .ne) l r) =
      .binary .ne (fitExpr2 env elems c l) (fitExpr2 env elems c r) := by
  cases ctx <;> simp [instExpr2] <;> first | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl⟩

theorem ie_eq (ctx : Option Nat) (w : Nat) (l r : PExpr) (hl : selfWidth2 env elems l = some w)
    (hr : selfWidth2 env elems r = some w) :
    instExpr2 env elems ctx (.binary (.m0 .eq) l r) =
      .binary .eq (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r) := by
  simp [instExpr2, hl, hr]

theorem ie_ne (ctx : Option Nat) (w : Nat) (l r : PExpr) (hl : selfWidth2 env elems l = some w)
    (hr : selfWidth2 env elems r = some w) :
    instExpr2 env elems ctx (.binary (.m0 .ne) l r) =
      .binary .ne (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r) := by
  simp [instExpr2, hl, hr]

theorem ie_cmp (c : CmpOp) (ctx : Option Nat) (a b : Nat) (l r : PExpr)
    (hl : selfWidth2 env elems l = some a) (hr : selfWidth2 env elems r = some b) :
    instExpr2 env elems ctx (.binary (.m0 c.ex) l r) =
      .binary c.ex (fitExpr2 env elems (some (max a b)) l) (fitExpr2 env elems (some (max a b)) r) := by
  cases c <;> simp [instExpr2, CmpOp.ex, hl, hr]

theorem sw_lnot (a : PExpr) : selfWidth2 env elems (.unary (.m0 .lnot) a) = some 1 := by
  simp [selfWidth2]

theorem sw_bnot (a : PExpr) :
    selfWidth2 env elems (.unary (.m0 .bnot) a) = selfWidth2 env elems a := by
  simp [selfWidth2]

theorem sw_land (l r : PExpr) : selfWidth2 env elems (.binary .land l r) = some 1 := by
  simp [selfWidth2]

theorem sw_lor (l r : PExpr) : selfWidth2 env elems (.binary .lor l r) = some 1 := by
  simp [selfWidth2]

theorem sw_cmp (c : CmpOp) (l r : PExpr) : selfWidth2 env elems (.binary (.m0 c.ex) l r) = some 1 := by
  cases c <;> simp [selfWidth2, CmpOp.ex]

theorem sw_eq (l r : PExpr) : selfWidth2 env elems (.binary (.m0 .eq) l r) = some 1 := by
  simp [selfWidth2]

theorem sw_ne (l r : PExpr) : selfWidth2 env elems (.binary (.m0 .ne) l r) = some 1 := by
  simp [selfWidth2]

theorem sw_reduce (op : RedOp) (a : PExpr) : selfWidth2 env elems (.reduce op a) = some 1 := by
  simp [selfWidth2]

theorem sw_ternary (w : Nat) (c t e : PExpr)
    (ht : selfWidth2 env elems t = some w) (he : selfWidth2 env elems e = some w) :
    selfWidth2 env elems (.ternary c t e) = some w := by
  simp [selfWidth2, ht, he]

theorem rm_bnot (a : PExpr) :
    rigidMax2 env elems (.unary (.m0 .bnot) a) = rigidMax2 env elems a := by
  simp [rigidMax2]

theorem rm_lnot (a : PExpr) : rigidMax2 env elems (.unary (.m0 .lnot) a) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_land (l r : PExpr) : rigidMax2 env elems (.binary .land l r) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_lor (l r : PExpr) : rigidMax2 env elems (.binary .lor l r) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_cmp (c : CmpOp) (l r : PExpr) : rigidMax2 env elems (.binary (.m0 c.ex) l r) = some 1 := by
  cases c <;> simp [rigidMax2, selfWidth2, CmpOp.ex]

theorem rm_eq (l r : PExpr) : rigidMax2 env elems (.binary (.m0 .eq) l r) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_ne (l r : PExpr) : rigidMax2 env elems (.binary (.m0 .ne) l r) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_reduce (op : RedOp) (a : PExpr) : rigidMax2 env elems (.reduce op a) = some 1 := by
  simp [rigidMax2, selfWidth2]

theorem rm_ternary (w : Nat) (c t e : PExpr)
    (ht : rigidMax2 env elems t = some w) (he : rigidMax2 env elems e = some w) :
    rigidMax2 env elems (.ternary c t e) = some w := by
  simp [rigidMax2, ht, he]

/-! ### WP-B2: `+`, `-` and the `Resize` marker -/

/-- The flags `instExpr2`'s `.resize` arm reads, for a leaf the recognizer accepts: not context-propagating, not a
constant leaf, and no negative-genvar guard applies. -/
theorem leaf_flags {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a) :
    e.ctxPropagates = false ∧ e.constLeaf = false ∧
      ∀ (env : IEnv) (m w : Nat), (PExpr.resize m e).negGenvarWidened env w = none := by
  cases e <;> simp [leafRd?] at h <;>
    first
    | exact ⟨rfl, rfl, fun _ _ _ => rfl⟩
    | (split at h <;> simp_all)
    | skip

/-- `a + b` and `a - b` at any context: the operation over two fits, possibly under one `resize` (an operand wider
than the context is operated on at its own width and truncated). -/
theorem ie_addsub_cases (b : BinOp) (hb : b = .add ∨ b = .sub) (ctx : Option Nat) (l r : PExpr) :
    (∃ c, instExpr2 env elems ctx (.binary (.m0 b) l r) =
      .binary b (fitExpr2 env elems c l) (fitExpr2 env elems c r)) ∨
    (∃ w c, instExpr2 env elems ctx (.binary (.m0 b) l r) =
      .resize w (.binary b (fitExpr2 env elems c l) (fitExpr2 env elems c r))) := by
  cases ctx with
  | none =>
      refine Or.inl ?_
      rcases hb with rfl | rfl <;> (unfold instExpr2; exact ⟨_, rfl⟩)
  | some w =>
      by_cases h : (ctxOpWidth2 env elems l r).getD w ≤ w
      · exact Or.inl ⟨some w, by rcases hb with rfl | rfl <;> simp [instExpr2, h]⟩
      · exact Or.inr ⟨w, some ((ctxOpWidth2 env elems l r).getD w),
          by rcases hb with rfl | rfl <;> simp [instExpr2, h]⟩

/-! ### WP-B2: `*` (a product with a signal-access factor is no constant) -/

/-- A signal access, bare or under the `Resize` marker, has no constant value at any type. -/
theorem evalAt_sigOpd {e : PExpr} (h : sigOpd e = true) (ty : Nat × Bool) (v : Int) :
    evalAt env ty e ≠ .ok v := by
  cases e with
  | ident n => simp [evalAt]
  | bitSel b i => cases b <;> simp_all [sigOpd, evalAt, ctype, bind, Except.bind]
  | partSel b m l => cases b <;> simp_all [sigOpd, evalAt, ctype, bind, Except.bind]
  | arrayElem n is => simp [evalAt]
  | arrayPart n is md a b => simp [evalAt]
  | resize w a =>
      cases a with
      | bitSel b i =>
          cases b <;> simp_all [sigOpd, evalAt, ctype, bind, Except.bind, PExpr.ctxPropagates, PExpr.negGenvarAt]
      | partSel b m l => cases b <;> simp_all [sigOpd, evalAt, ctype, bind, Except.bind]
      | _ => simp_all [sigOpd, evalAt, ctype, bind, Except.bind]
  | _ => simp [sigOpd] at h

theorem isInt_sigOpd {e : PExpr} (h : sigOpd e = true) : e.isInt env = false := by
  cases e <;> simp_all [sigOpd]

/-- **A product with a signal-access factor is no constant**: `evalInt` fails on it, so `instExpr2` lowers it as an
operation, the way it lowers `+`. -/
theorem evalInt_mul_sig {l r : PExpr} (h : (sigOpd l || sigOpd r) = true) (v : Int) :
    evalInt env (.binary .mul l r) ≠ .ok v := by
  have hi : (l.isInt env && r.isInt env) = false := by
    rcases Bool.or_eq_true_iff.mp h with h' | h' <;> simp [isInt_sigOpd h']
  have hat : ∀ ty x, evalAt env ty (.binary .mul l r) ≠ .ok x := by
    intro ty x
    rcases hl : evalAt env ty l with m | a
    · simp [evalAt, SymBinOp.constClass, hl, bind, Except.bind]
    · rcases hr : evalAt env ty r with m | b
      · simp [evalAt, SymBinOp.constClass, hl, hr, bind, Except.bind]
      · rcases Bool.or_eq_true_iff.mp h with h' | h'
        · exact absurd hl (evalAt_sigOpd h' ty a)
        · exact absurd hr (evalAt_sigOpd h' ty b)
  rcases hc : ctype env (.binary .mul l r) with m | ⟨w, s⟩
  · simp [evalInt, hi, evalSized, hc, bind, Except.bind]
  · rcases he : evalAt env (w, s) (.binary .mul l r) with m | x
    · simp [evalInt, hi, evalSized, hc, he, bind, Except.bind]
    · exact absurd he (hat _ x)

/-- `a * b` at any context, one factor a signal access: the operation over two fits, possibly under one `resize`, the
shape of `+` (`ie_addsub_cases`). -/
theorem ie_mul_cases {l r : PExpr} (hm : (sigOpd l || sigOpd r) = true) (ctx : Option Nat) :
    (∃ c, instExpr2 env elems ctx (.binary .mul l r) =
      .binary .mul (fitExpr2 env elems c l) (fitExpr2 env elems c r)) ∨
    (∃ w c, instExpr2 env elems ctx (.binary .mul l r) =
      .resize w (.binary .mul (fitExpr2 env elems c l) (fitExpr2 env elems c r))) := by
  rcases he : evalInt env (.binary .mul l r) with e | v
  · cases ctx with
    | none =>
        refine Or.inl ?_
        simp only [instExpr2, he]
        exact ⟨_, rfl⟩
    | some w =>
        by_cases h : (ctxOpWidth2 env elems l r).getD w ≤ w
        · exact Or.inl ⟨some w, by simp [instExpr2, he, h]⟩
        · exact Or.inr ⟨w, some ((ctxOpWidth2 env elems l r).getD w), by simp [instExpr2, he, h]⟩
  · exact absurd he (evalInt_mul_sig hm v)

/-- … at a context the factors fit (`instExpr2_add`). -/
theorem instExpr2_mul {l r : PExpr} (hm : (sigOpd l || sigOpd r) = true) (w : Nat)
    (hw : (ctxOpWidth2 env elems l r).getD w ≤ w) :
    instExpr2 env elems (some w) (.binary .mul l r) =
      .binary .mul (fitExpr2 env elems (some w) l) (fitExpr2 env elems (some w) r) := by
  rcases he : evalInt env (.binary .mul l r) with e | v
  · simp [instExpr2, he, hw]
  · exact absurd he (evalInt_mul_sig hm v)

/-- … and at no context (a self-determined position: the wider of the factors' own widths). -/
theorem ie_mul_none {l r : PExpr} (hm : (sigOpd l || sigOpd r) = true) {a c : Nat}
    (hl : selfWidth2 env elems l = some a) (hr : selfWidth2 env elems r = some c) :
    instExpr2 env elems none (.binary .mul l r) =
      .binary .mul (fitExpr2 env elems (some (max a c)) l) (fitExpr2 env elems (some (max a c)) r) := by
  rcases he : evalInt env (.binary .mul l r) with e | v
  · simp [instExpr2, he, hl, hr]
  · exact absurd he (evalInt_mul_sig hm v)

/-- A marker over a non-propagating, non-constant operand is, at every context, a `resize` over an
instantiation of it. -/
theorem ie_resize_cases {e : PExpr} (hcp : e.ctxPropagates = false) (hcl : e.constLeaf = false)
    (hng : ∀ (env : IEnv) (m w : Nat), (PExpr.resize m e).negGenvarWidened env w = none)
    (ctx : Option Nat) (m : Nat) :
    ∃ x c, instExpr2 env elems ctx (.resize m e) = .resize x (instExpr2 env elems c e) := by
  cases ctx with
  | none => exact ⟨m, selfWidth2 env elems e, by simp [instExpr2]⟩
  | some cw =>
      rcases hs : selfWidth2 env elems e with _ | sw
      · exact ⟨cw, none, by simp [instExpr2, hs]⟩
      · by_cases h : sw < cw
        · exact ⟨cw, some sw, by simp [instExpr2, hs, h, hcp, hng]⟩
        · exact ⟨cw, some sw, by simp [instExpr2, hs, h, hcl]⟩

/-- The flags `instExpr2`'s `.resize` arm reads for an operation (or an unsized constant) under the marker. -/
theorem op_flags {e : PExpr} (hop : e.isOpW = true) :
    e.constLeaf = false ∧ ∀ (env : IEnv) (m w : Nat), (PExpr.resize m e).negGenvarWidened env w = none := by
  cases e <;> simp [PExpr.isOpW] at hop <;> simp [PExpr.constLeaf, PExpr.negGenvarWidened]

/-- A marker around an operation at any context (WP-B2 gate 2b): a `resize` over an instantiation of the operand, or
(an operand that follows a wider context) the operand instantiated at that context. -/
theorem ie_resize_op {e : PExpr} (hop : e.isOpW = true) (ctx : Option Nat) (m : Nat) :
    (∃ x c, instExpr2 env elems ctx (.resize m e) = .resize x (instExpr2 env elems c e)) ∨
    (∃ cw, instExpr2 env elems ctx (.resize m e) = instExpr2 env elems (some cw) e) := by
  obtain ⟨hcl, hng⟩ := op_flags hop
  cases ctx with
  | none => exact Or.inl ⟨m, selfWidth2 env elems e, by simp [instExpr2]⟩
  | some cw =>
      rcases hs : selfWidth2 env elems e with _ | sw
      · exact Or.inl ⟨cw, none, by simp [instExpr2, hs]⟩
      · by_cases h : sw < cw
        · by_cases hp : e.ctxPropagates = true
          · exact Or.inr ⟨cw, by simp [instExpr2, hs, h, hp]⟩
          · have hp' : e.ctxPropagates = false := by simpa using hp
            exact Or.inl ⟨cw, some sw, by simp [instExpr2, hs, h, hp', hng]⟩
        · exact Or.inl ⟨cw, some sw, by simp [instExpr2, hs, h, hcl]⟩

/-- The exact shape of a marker around an operation whose natural width is known. -/
theorem ie_resize_op_eq {e : PExpr} (hop : e.isOpW = true) {sw : Nat}
    (hs : selfWidth2 env elems e = some sw) (cw m : Nat) :
    instExpr2 env elems (some cw) (.resize m e) =
      if sw < cw ∧ e.ctxPropagates = true then instExpr2 env elems (some cw) e
      else .resize cw (instExpr2 env elems (some sw) e) := by
  obtain ⟨hcl, hng⟩ := op_flags hop
  by_cases h : sw < cw
  · by_cases hp : e.ctxPropagates = true
    · simp [instExpr2, hs, h, hp]
    · have hp' : e.ctxPropagates = false := by simpa using hp
      simp [instExpr2, hs, h, hp', hng]
  · simp [instExpr2, hs, h, hcl]

theorem ie_int (ctx : Option Nat) (v : Int) :
    instExpr2 env elems ctx (.int v) = .lit (LVec.ofInt (ctx.getD 32) v) := by
  simp [instExpr2]

/-- A run-time left shift at any context (WP-B2 gate 3): `ctxTrunc2` over the shift of two `instDivOperand2`s (the left
operand at the context extended to its own width, the amount at its own width). -/
theorem ie_shl_form (s : Bool) (ctx : Option Nat) (l r : PExpr) :
    ∃ lc, instExpr2 env elems ctx (.binary (.m0 (.shl s)) l r) =
      ctxTrunc2 ctx lc (.binary (.shl s) (instDivOperand2 env elems s lc l)
        (instDivOperand2 env elems false (shiftAmtWidth2 env elems r) r)) := by
  unfold instExpr2; exact ⟨_, rfl⟩

theorem ie_shr_form (ctx : Option Nat) (l r : PExpr) :
    ∃ lc, instExpr2 env elems ctx (.binary (.m0 (.shr false)) l r) =
      ctxTrunc2 ctx lc (.binary (.shr false) (instDivOperand2 env elems false lc l)
        (instDivOperand2 env elems false (shiftAmtWidth2 env elems r) r)) := by
  unfold instExpr2; exact ⟨_, rfl⟩

/-- The default arm of `instDivOperand2` (an operand that is a signal access, a literal or an unsized constant). -/
theorem instDiv_default (s : Bool) (c : Option Nat) (e : PExpr)
    (he : (∃ v, e = .lit v) ∨ (∃ k, e = .int k) ∨ (∃ n, e = .ident n) ∨ (∃ b i, e = .bitSel b i) ∨
      (∃ n is, e = .arrayElem n is) ∨ (∃ n is m a b, e = .arrayPart n is m a b) ∨
      (∃ b m l, e = .partSel b m l)) :
    instDivOperand2 env elems s c e =
      fitDivOperand2 s c (divOperandWidth2 env elems e)
        (instExpr2 env elems ((divOperandWidth2 env elems e).orElse (fun _ => c)) e) := by
  rcases he with ⟨v, rfl⟩ | ⟨k, rfl⟩ | ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ | ⟨n, is, m, a, b, rfl⟩ |
      ⟨b, m, l, rfl⟩ <;>
    simp only [instDivOperand2]

/-- The `Resize` marker is transparent for `instDivOperand2` of an UNSIGNED shift (the arm ignores the signedness it is
given and lowers the operand unsigned). -/
theorem instDiv_resize (s : Bool) (c : Option Nat) (m : Nat) (e : PExpr)
    (he : (∃ v, e = .lit v) ∨ (∃ k, e = .int k) ∨ (∃ n, e = .ident n) ∨ (∃ b i, e = .bitSel b i) ∨
      (∃ n is, e = .arrayElem n is) ∨ (∃ n is m a b, e = .arrayPart n is m a b) ∨
      (∃ b m l, e = .partSel b m l)) :
    instDivOperand2 env elems s c (.resize m e) =
      instDivOperand2 env elems false (c.orElse (fun _ => some m)) e := by
  rcases he with ⟨v, rfl⟩ | ⟨k, rfl⟩ | ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ | ⟨n, is, m', a, b, rfl⟩ |
      ⟨b, m'', l, rfl⟩ <;>
    simp only [instDivOperand2]

/-- The `SignedResize` marker lowers its operand SIGNED (the arm ignores the signedness it is given). -/
theorem instDiv_sresize (s : Bool) (c : Option Nat) (m : Nat) (e : PExpr) :
    instDivOperand2 env elems s c (.signedResize m e) =
      instDivOperand2 env elems true (c.orElse (fun _ => some m)) e := by
  simp only [instDivOperand2]

end s2eqns

/-! ## The environment facts the site lemmas read -/

/-- The semantic facts about an access's declaration and indices (the `Ctx`-level form of
`Summary.InR`). -/
def AccGeom (σ : String → Int) (DG : String → Option (List (Int × Int)))
    (EW : String → Option Nat) : Acc → Prop
  | .whole _ => True
  | .bit n a => 0 ≤ a.eval σ ∧ EW n = some 1
  | .cell1 n a => ∃ m, DG n = some [(m, 0)] ∧ 0 ≤ a.eval σ ∧ a.eval σ ≤ m
  | .row n w r =>
      ∃ m1 m2, DG n = some [(m1, 0), (m2, 0)] ∧ 0 ≤ m2 ∧ w.eval σ = m2 + 1 ∧ 0 ≤ r.eval σ ∧
        r.eval σ ≤ m1
  | .cell2 n w r c =>
      ∃ m1 m2, DG n = some [(m1, 0), (m2, 0)] ∧ w.eval σ = m2 + 1 ∧ 0 ≤ r.eval σ ∧
        r.eval σ ≤ m1 ∧ 0 ≤ c.eval σ ∧ c.eval σ ≤ m2
  | .part1 n hi lo =>
      ∃ m, DG n = some [(m, 0)] ∧ 0 ≤ lo.eval σ ∧ lo.eval σ ≤ hi.eval σ ∧ hi.eval σ ≤ m
  | .part2 n w r hi lo =>
      ∃ m1 m2, DG n = some [(m1, 0), (m2, 0)] ∧ w.eval σ = m2 + 1 ∧ 0 ≤ r.eval σ ∧
        r.eval σ ≤ m1 ∧ 0 ≤ lo.eval σ ∧ lo.eval σ ≤ hi.eval σ ∧ hi.eval σ ≤ m2

/-- The element width `buildElems` records for a declaration of the evaluated dimensions `ds`: the width of the second
dimension of a two-dimensional one, `1` otherwise (`DeclT.elemW`, on `DeclT.vals`). -/
def elemWOfDims : List (Int × Int) → Nat
  | [_, p] => 1 * ((p.1 - p.2).natAbs + 1)
  | _ => 1

theorem DeclT.elemW_vals (σ : String → Int) (dt : DeclT) : dt.elemW σ = elemWOfDims (dt.vals σ) := by
  unfold DeclT.elemW DeclT.vals
  rcases hd : dt.dims with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [elemWOfDims]

/-- The instantiation environment's facts the site lemmas read. -/
structure Ctx (σ : String → Int) (E : IEnv) (elems : List (String × Nat))
    (DW : String → Option Nat) (DG : String → Option (List (Int × Int)))
    (EW : String → Option Nat) (ns : List String) : Prop where
  agree : Agrees σ E ns
  widths : ∀ n, E.widths.lookup n = DW n
  /-- WP-B2 gate 4a: the element width of a declaration of known dimensions (what a legacy row or part select reads).
  (Declared BEFORE `elems`: a later field would see that field, not the parameter, under the name `elems`.) -/
  elemsG : ∀ n ds, DG n = some ds → elems.lookup n = some (elemWOfDims ds)
  elems : ∀ n, EW n = some 1 → elems.lookup n = some 1
  dims : ∀ n ds, DG n = some ds → E.dims.lookup n = some ds

theorem Ctx.bindVal {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
    {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
    {EW : String → Option Nat} {ns : List String}
    (C : Ctx σ E elems DW DG EW ns) (g : String) (i : Int) :
    Ctx (bindσ g i σ) (E.bindVal g i) elems DW DG EW (g :: ns) :=
  ⟨C.agree.bindVal g i, C.widths, C.elemsG, C.elems, C.dims⟩

/-- Everything a site lemma needs about one access. -/
def AccOK (σ : String → Int) (DW : String → Option Nat)
    (DG : String → Option (List (Int × Int))) (EW : String → Option Nat) (ns : List String)
    (a : Acc) : Prop :=
  (DW a.name).isSome = true ∧ AccGeom σ DG EW a ∧ ∀ x ∈ a.affs, ∀ n ∈ x.names, n ∈ ns

section sites

variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- The element width of a zero-based two-dimensional declaration is its row width. -/
theorem ctxElemsRow (C : Ctx σ E elems DW DG EW ns) {n : String} {m1 m2 : Int}
    (hdg : DG n = some [(m1, 0), (m2, 0)]) (hm2 : 0 ≤ m2) : elems.lookup n = some (m2 + 1).toNat := by
  have h := C.elemsG n _ hdg
  have e : elemWOfDims [(m1, 0), (m2, 0)] = (m2 + 1).toNat := by simp [elemWOfDims]; omega
  rwa [e] at h

/-- … and of a one-dimensional one is one. -/
theorem ctxElemsOne (C : Ctx σ E elems DW DG EW ns) {n : String} {m : Int}
    (hdg : DG n = some [(m, 0)]) : elems.lookup n = some 1 :=
  C.elemsG n _ hdg

/-- **A legacy part select of a one-dimensional declaration** instantiates to the window `Acc.part1` promises. -/
theorem inst_partSel (C : Ctx σ E elems DW DG EW ns) {n : String} {msb lsb : PExpr} {x y : Aff} {m : Int}
    (hdg : DG n = some [(m, 0)]) (hx : affOf? msb = some x) (hy : affOf? lsb = some y)
    (hagx : ∀ a ∈ [x, y], ∀ v ∈ a.names, E.vals.lookup v = some (σ v))
    (hy0 : 0 ≤ y.eval σ) (hyx : y.eval σ ≤ x.eval σ) (ctx : Option Nat) :
    instExpr2 E elems ctx (.partSel (.ident n) msb lsb) =
      .slice (.ident n) (y.eval σ).toNat (x.eval σ - y.eval σ + 1).toNat := by
  obtain ⟨hix, heh⟩ := affOf?_sound msb x hx (hagx x (by simp))
  obtain ⟨-, hel⟩ := affOf?_sound lsb y hy (hagx y (by simp))
  rw [instExpr2_partSel_ident ctx (ctxElemsOne C hdg) heh hel ⟨hy0, hyx⟩ (Or.inl hix)]
  have h1 : ((x.eval σ - y.eval σ).toNat + 1) * 1 = (x.eval σ - y.eval σ + 1).toNat := by omega
  rw [h1, Nat.mul_one]

/-- … and its self-width. -/
theorem selfWidth_partSel (C : Ctx σ E elems DW DG EW ns) {n : String} {msb lsb : PExpr} {x y : Aff} {m : Int}
    (hdg : DG n = some [(m, 0)]) (hx : affOf? msb = some x) (hy : affOf? lsb = some y)
    (hagx : ∀ a ∈ [x, y], ∀ v ∈ a.names, E.vals.lookup v = some (σ v))
    (hy0 : 0 ≤ y.eval σ) (hyx : y.eval σ ≤ x.eval σ) :
    selfWidth2 E elems (.partSel (.ident n) msb lsb) = some (x.eval σ - y.eval σ + 1).toNat := by
  obtain ⟨-, heh⟩ := affOf?_sound msb x hx (hagx x (by simp))
  obtain ⟨-, hel⟩ := affOf?_sound lsb y hy (hagx y (by simp))
  rw [selfWidth2_partSel_of (by simpa using ctxElemsOne C hdg) heh hel ⟨hy0, hyx⟩]
  have h1 : ((x.eval σ - y.eval σ).toNat + 1) * 1 = (x.eval σ - y.eval σ + 1).toNat := by omega
  rw [h1]

/-- … and the write window of a legacy part-select target. -/
theorem instLhs_partSel (C : Ctx σ E elems DW DG EW ns) {n : String} {msb lsb : PExpr} {x y : Aff} {m : Int}
    (hdg : DG n = some [(m, 0)]) (hx : affOf? msb = some x) (hy : affOf? lsb = some y)
    (hagx : ∀ a ∈ [x, y], ∀ v ∈ a.names, E.vals.lookup v = some (σ v))
    (hy0 : 0 ≤ y.eval σ) (hyx : y.eval σ ≤ x.eval σ) :
    instLhs2 E elems (.partSel n msb lsb) =
      .ok (.slice n (y.eval σ).toNat (x.eval σ - y.eval σ + 1).toNat, (x.eval σ - y.eval σ + 1).toNat) := by
  obtain ⟨hix, heh⟩ := affOf?_sound msb x hx (hagx x (by simp))
  obtain ⟨-, hel⟩ := affOf?_sound lsb y hy (hagx y (by simp))
  rw [instLhs2_partSel (ctxElemsOne C hdg) heh hel ⟨hy0, hyx⟩ (Or.inl hix)]
  have h1 : ((x.eval σ - y.eval σ).toNat + 1) * 1 = (x.eval σ - y.eval σ + 1).toNat := by omega
  rw [h1, Nat.mul_one]

/-- **A leaf read**: the instantiated expression is the window the access promises (or an
identifier), with no loud node. -/
theorem inst_leaf (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a) (ctx : Option Nat) :
    RdOK σ [a] (instExpr2 E elems ctx e) := by
  obtain ⟨hdec, hgeo, hns⟩ := ha
  have hagx : ∀ x ∈ a.affs, ∀ n ∈ x.names, E.vals.lookup n = some (σ n) :=
    fun x hx n hn => C.agree n (hns x hx n hn)
  cases e with
  | ident n =>
      simp only [leafRd?, Except.ok.injEq] at h
      subst h
      simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents, Acc.rd, Acc.name]
  | bitSel b i =>
      cases b with
      | ident n =>
          simp only [leafRd?] at h
          rcases hx : affOf? i with _ | x
          · simp [hx] at h
          · simp only [hx] at h
            rcases bitAcc?_cases ds n x with hb | ⟨w, hb⟩ <;> rw [hb] at h <;>
              simp only [Except.ok.injEq] at h <;> subst h
            · obtain ⟨hnn, hel⟩ := hgeo
              have hel' : elems.lookup n = some 1 := C.elems n hel
              obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
              rw [instExpr2_bitSel_ident ctx hel' hev hnn]
              simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
                Acc.rd, Acc.name, Acc.lo]
            · -- a legacy select of a row of a two-dimensional declaration
              obtain ⟨m1, m2, hdg, hm2, hw, hx0, hx1⟩ := hgeo
              have hel' := ctxElemsRow C hdg hm2
              obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
              rw [instExpr2_bitSel_ident ctx hel' hev hx0]
              simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
                Acc.rd, Acc.name, Acc.lo, Acc.wid, rmN, hw]
      | _ => simp [leafRd?] at h
  | partSel b msb lsb =>
      cases b with
      | ident n =>
          simp only [leafRd?] at h
          obtain ⟨-, hc⟩ := partAcc?_cases h
          rcases hc with ⟨x, y, -, hx, hy, rfl⟩ | ⟨i, r, x, y, w, hnil, -⟩
          · obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hgeo
            rw [inst_partSel C hdg hx hy hagx hy0 hyx ctx]
            simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
              Acc.rd, Acc.name, Acc.lo, Acc.wid]
          · exact absurd hnil (by simp)
      | _ => simp [leafRd?] at h
  | arrayElem n is =>
      simp only [leafRd?] at h
      rcases elemAcc?_cases h with ⟨i, x, rfl, hx, rfl⟩ | ⟨i, x, w, rfl, hx, rfl⟩ |
        ⟨i, j, x, y, w, rfl, hx, hy, rfl⟩
      · -- n[i], 1-D
        obtain ⟨m, hdg, hx0, hx1⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
        rw [instExpr2_arrayElem, arrayElemRead_of_inRange (arrayElemWindow_1d_in hd hev hx0 hx1)]
        simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
          Acc.rd, Acc.name, Acc.lo]
      · -- n[i], a row of a 2-D array
        obtain ⟨m1, m2, hdg, hm2, hw, hx0, hx1⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
        rw [instExpr2_arrayElem,
          arrayElemRead_of_inRange (arrayElemWindow_row hd hm2 hev hx0 hx1)]
        have hrow := rmN_row_toNat (W := m2 + 1) (i := x.eval σ) (by omega) hx0
        simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
          Acc.rd, Acc.name, Acc.lo, Acc.wid, hw, hrow]
      · -- n[i][j]
        obtain ⟨m1, m2, hdg, hw, hx0, hx1, hy0, hy1⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, hevi⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
        obtain ⟨-, hevj⟩ := affOf?_sound j y hy (hagx y (by simp [Acc.affs]))
        rw [instExpr2_arrayElem, arrayElemRead_of_inRange
          (arrayElemWindow_cell2 hd hevi hx0 hx1 hevj hy0 hy1)]
        have hcell := rmN_eq_toNat (W := m2 + 1) (i := x.eval σ) (j := y.eval σ) (by omega) hx0 hy0
        simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
          Acc.rd, Acc.name, Acc.lo, hw, hcell]
  | arrayPart n is mode hi lo =>
      simp only [leafRd?] at h
      obtain ⟨rfl, hc⟩ := partAcc?_cases h
      rcases hc with ⟨x, y, rfl, hx, hy, rfl⟩ | ⟨i, r, x, y, w, rfl, hr, hx, hy, rfl⟩
      · -- n[hi:lo], 1-D
        obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, heh⟩ := affOf?_sound hi x hx (hagx x (by simp [Acc.affs]))
        obtain ⟨-, hel⟩ := affOf?_sound lo y hy (hagx y (by simp [Acc.affs]))
        have hg := arrayPartGeom_part1 hd (by omega) heh hel hyx
        rw [instExpr2_arrayPart _ (dynPartPlan_of_geom hg),
          arrayPartRead_part1 hd (by omega) heh hel hy0 hyx hxm]
        simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
          Acc.rd, Acc.name, Acc.lo, Acc.wid]
      · -- n[i][hi:lo], part of a row
        obtain ⟨m1, m2, hdg, hw, hr0, hr1, hy0, hyx, hxm⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, hei⟩ := affOf?_sound i r hr (hagx r (by simp [Acc.affs]))
        obtain ⟨-, heh⟩ := affOf?_sound hi x hx (hagx x (by simp [Acc.affs]))
        obtain ⟨-, hel⟩ := affOf?_sound lo y hy (hagx y (by simp [Acc.affs]))
        have hg := arrayPartGeom_part2 hd (by omega) hei hr0 hr1 heh hel hyx
        rw [instExpr2_arrayPart _ (dynPartPlan_of_geom hg),
          arrayPartRead_part2 hd hei hr0 hr1 heh hel hy0 hyx hxm]
        have hcell := rmN_eq_toNat (W := m2 + 1) (i := r.eval σ) (j := y.eval σ) (by omega) hr0 hy0
        simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
          Acc.rd, Acc.name, Acc.lo, Acc.wid, hw, hcell]
  | _ => simp [leafRd?] at h

theorem inst_rdsLeaf (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {e : PExpr}
    {rs : List Acc} (h : rdsLeaf? ds e = .ok rs)
    (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (ctx : Option Nat) :
    RdOK σ rs (instExpr2 E elems ctx e) := by
  unfold rdsLeaf? at h
  rcases hl : leafRd? ds e with m | a
  · simp [hl] at h
  · simp only [hl, Except.ok.injEq] at h
    subst h
    exact inst_leaf C hl (hacc a (by simp)) ctx

/-- The parts of a concatenation. -/
theorem inst_parts (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRd? ds ps = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) →
      RdOK σ rs (.concat (instParts2 E elems ps).toArray)
  | [], rs, h, _ => by
      simp only [partsRd?, Except.ok.injEq] at h
      subst h
      simp only [instParts2_nil]
      exact RdOK.concat_nil
  | p :: ps, rs, h, hacc => by
      simp only [partsRd?] at h
      rcases hp : partRd? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRd? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          have h1 : RdOK σ ra (instExpr2 E elems (selfWidth2 E elems p) p) := by
            unfold partRd? at hp
            cases p with
            | lit v =>
                simp only [Except.ok.injEq] at hp
                subst hp
                simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
            | _ =>
                exact inst_rdsLeaf C hp (fun a ha => hacc a (List.mem_append_left _ ha)) _
          have h2 := inst_parts C ps rb hq (fun a ha => hacc a (List.mem_append_right _ ha))
          rw [instParts2_cons]
          exact RdOK.concat_cons h1 h2

/-- **The reads of an expression of the fragment**, at any context. -/
theorem inst_rd (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} :
    ∀ (e : PExpr) (rs : List Acc), rdsOf? ds e = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ∀ ctx, RdOK σ rs (instExpr2 E elems ctx e)
  | .lit v, rs, h, _, ctx => by
      simp only [rdsOf?, Except.ok.injEq] at h
      subst h
      simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  | .binary op l r, rs, h, hacc, ctx => by
      obtain ⟨hb, ra, rb, hl, hr', rfl⟩ := rdsOf?_binary h
      have ihl := inst_rd C l ra hl (fun a ha => hacc a (List.mem_append_left _ ha))
      have ihr := inst_rd C r rb hr' (fun a ha => hacc a (List.mem_append_right _ ha))
      have hfl := RdOK.fit (E := E) (elems := elems) (signedCast_of_rds hl) ihl
      have hfr := RdOK.fit (E := E) (elems := elems) (signedCast_of_rds hr') ihr
      have gate : ∀ g : BinOp, (g = .and ∨ g = .or ∨ g = .xor) →
          RdOK σ (ra ++ rb) (instExpr2 E elems ctx (.binary (.m0 g) l r)) := by
        intro g hg
        obtain ⟨c, hc⟩ := instExpr2_gate E elems ctx g hg l r
        rw [hc]
        exact RdOK.binary _ (hfl c) (hfr c)
      rcases binOk_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact gate .and (Or.inl rfl)
      · exact gate .or (Or.inr (Or.inl rfl))
      · exact gate .xor (Or.inr (Or.inr rfl))
      · rw [ie_land]; exact RdOK.logical true (ihl _) (ihr _)
      · rw [ie_lor]; exact RdOK.logical false (ihl _) (ihr _)
      · obtain ⟨c, hc⟩ := ie_eq_cases (env := E) (elems := elems) ctx l r
        rw [hc]; exact RdOK.binary _ (hfl c) (hfr c)
      · obtain ⟨c, hc⟩ := ie_ne_cases (env := E) (elems := elems) ctx l r
        rw [hc]; exact RdOK.binary _ (hfl c) (hfr c)
  | .unary op a, rs, h, hacc, ctx => by
      obtain ⟨hop, ha⟩ := rdsOf?_unary h
      have iha := inst_rd C a rs ha hacc
      rcases hop with rfl | rfl
      · have hs := signedCast_of_rds ha
        rcases ie_bnot_cases (env := E) (elems := elems) ctx a with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨w, c, hc⟩
        · rw [hc]; exact RdOK.unary _ (iha c)
        · rw [hc]; exact RdOK.unary _ (RdOK.fit hs iha c)
        · rw [hc]; exact RdOK.resize w (RdOK.unary _ (RdOK.fit hs iha c))
      · rw [ie_lnot]; exact RdOK.unary _ (iha none)
  | .ternary c t e, rs, h, hacc, ctx => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := rdsOf?_ternary h
      have ihc := inst_rd C c rc hc
        (fun a ha => hacc a (List.mem_append_left _ (List.mem_append_left _ ha)))
      have iht := inst_rd C t rt ht
        (fun a ha => hacc a (List.mem_append_left _ (List.mem_append_right _ ha)))
      have ihe := inst_rd C e re he (fun a ha => hacc a (List.mem_append_right _ ha))
      obtain ⟨a0, ha0⟩ := ie_ternary_cases (env := E) (elems := elems) ctx c t e
      rw [ha0]
      exact RdOK.ternary (ihc none) (RdOK.fit (signedCast_of_rds ht) iht a0)
        (RdOK.fit (signedCast_of_rds he) ihe a0)
  | .reduce op a, rs, h, hacc, ctx => by
      have iha := inst_rd C a rs (rdsOf?_reduce h) hacc
      rw [ie_reduce]; exact RdOK.reduce _ (iha _)
  | .concat ps, rs, h, hacc, ctx => by
      simp only [rdsOf?] at h
      rw [instExpr2_concat]
      exact inst_parts C ps rs h hacc
  | .ident n, rs, h, hacc, ctx => inst_rdsLeaf C (by simpa [rdsOf?] using h) hacc ctx
  | .bitSel b i, rs, h, hacc, ctx => inst_rdsLeaf C (by simpa [rdsOf?] using h) hacc ctx
  | .partSel b m l, rs, h, hacc, ctx => inst_rdsLeaf C (by simpa [rdsOf?] using h) hacc ctx
  | .arrayElem n is, rs, h, hacc, ctx => inst_rdsLeaf C (by simpa [rdsOf?] using h) hacc ctx
  | .arrayPart n is m a b, rs, h, hacc, ctx => inst_rdsLeaf C (by simpa [rdsOf?] using h) hacc ctx
  | .repl .., rs, h, _, _
  | .paramRef .., rs, h, _, _
  | .genvarRef .., rs, h, _, _ | .enumRef .., rs, h, _, _
  | .int .., rs, h, _, _ | .fill .., rs, h, _, _
  | .resize .., rs, h, _, _ | .signedResize .., rs, h, _, _
  | .squash2 .., rs, h, _, _ | .sysCall .., rs, h, _, _
  | .cast .., rs, h, _, _ | .unsupported .., rs, h, _, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

/-- A leaf the recognizer accepts is a signal access. -/
theorem leafKind_of_leafRd {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a) :
    (∃ n, e = .ident n) ∨ (∃ b i, e = .bitSel b i) ∨ (∃ n is, e = .arrayElem n is) ∨
      (∃ n is m a b, e = .arrayPart n is m a b) ∨ (∃ b m l, e = .partSel b m l) := by
  cases e <;> simp [leafRd?] at h <;> simp

/-- The kinds of operand `instDiv_default` covers, from a recognized shift operand. -/
theorem shOpdKind {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : shOpdRd? ds e = .ok rs) :
    (∃ v, e = .lit v) ∨ (∃ k, e = .int k) ∨ (∃ n, e = .ident n) ∨ (∃ b i, e = .bitSel b i) ∨
      (∃ n is, e = .arrayElem n is) ∨ (∃ n is m a b, e = .arrayPart n is m a b) ∨
      (∃ b m l, e = .partSel b m l) := by
  rcases shOpdRd?_cases h with ⟨v, rfl, -⟩ | ⟨k, rfl, -⟩ | ⟨a, hl, -⟩
  · exact Or.inl ⟨v, rfl⟩
  · exact Or.inr (Or.inl ⟨k, rfl⟩)
  · rcases leafKind_of_leafRd hl with h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-- **The reads of a shift operand** (the amount, or the left operand without its marker), at any context. -/
theorem rd_shOpd (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {e : PExpr} {rs : List Acc}
    (h : shOpdRd? ds e = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (s : Bool) (c : Option Nat) :
    RdOK σ rs (instDivOperand2 E elems s c e) := by
  rw [instDiv_default s c e (shOpdKind h)]
  refine RdOK.fitDiv ?_ s _ _
  rcases shOpdRd?_cases h with ⟨v, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨a, hl, rfl⟩
  · simp [instExpr2, RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  · simp [instExpr2, RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  · exact inst_leaf C hl (hacc a (by simp)) _

/-- The amount of a shift is a bare genvar (a constant of the instance) or a shift operand. -/
theorem shAmtRd?_cases {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : shAmtRd? ds e = .ok rs) :
    (∃ g, e = .genvarRef g ∧ rs = []) ∨
    (∃ n, e = .paramRef n none ∧ rs = []) ∨ shOpdRd? ds e = .ok rs := by
  cases e with
  | genvarRef g => left; exact ⟨g, rfl, by simpa [shAmtRd?] using h.symm⟩
  | paramRef n pkg =>
      cases pkg with
      | none => right; left; exact ⟨n, rfl, by simpa [shAmtRd?] using h⟩
      | some p => right; right; simpa [shAmtRd?] using h
  | _ => right; right; simpa [shAmtRd?] using h

theorem cnames_binary_l {op : SymBinOp} {l r : PExpr} {n : String} (h : n ∈ l.cnames) :
    n ∈ (PExpr.binary op l r).cnames := by simp [PExpr.cnames, h]
theorem cnames_binary_r {op : SymBinOp} {l r : PExpr} {n : String} (h : n ∈ r.cnames) :
    n ∈ (PExpr.binary op l r).cnames := by simp [PExpr.cnames, h]
theorem cnames_unary {op : SymUnaryOp} {a : PExpr} {n : String} (h : n ∈ a.cnames) :
    n ∈ (PExpr.unary op a).cnames := by simpa [PExpr.cnames] using h
theorem cnames_reduce {op : RedOp} {a : PExpr} {n : String} (h : n ∈ a.cnames) :
    n ∈ (PExpr.reduce op a).cnames := by simpa [PExpr.cnames] using h
theorem cnames_resize {m : Nat} {a : PExpr} {n : String} (h : n ∈ a.cnames) :
    n ∈ (PExpr.resize m a).cnames := by simpa [PExpr.cnames] using h
theorem cnames_ternary_c {c t e : PExpr} {n : String} (h : n ∈ c.cnames) : n ∈ (PExpr.ternary c t e).cnames := by
  simp [PExpr.cnames, h]
theorem cnames_ternary_t {c t e : PExpr} {n : String} (h : n ∈ t.cnames) : n ∈ (PExpr.ternary c t e).cnames := by
  simp [PExpr.cnames, h]
theorem cnames_ternary_e {c t e : PExpr} {n : String} (h : n ∈ e.cnames) : n ∈ (PExpr.ternary c t e).cnames := by
  simp [PExpr.cnames, h]
/-- A genvar named as the amount of a shift is among the constants of the expression. -/
theorem cnames_amount {op : SymBinOp} {l r : PExpr} (hb : shOpW op = true) {g : String} (hg : r = .genvarRef g) :
    g ∈ (PExpr.binary op l r).cnames := by
  subst hg
  rcases shOpW_cases hb with ⟨s, rfl⟩ | rfl <;> simp [PExpr.cnames]

theorem cnames_amount_param {op : SymBinOp} {l r : PExpr} (hb : shOpW op = true)
    {n : String} (hn : r = .paramRef n none) :
    n ∈ (PExpr.binary op l r).cnames := by
  subst r
  rcases shOpW_cases hb with ⟨s, rfl⟩ | rfl <;> simp [PExpr.cnames]

theorem rcounts_binary_l {op : SymBinOp} {l r : PExpr} {c : Aff} (h : c ∈ l.rcounts) :
    c ∈ (PExpr.binary op l r).rcounts := by simp [PExpr.rcounts, h]
theorem rcounts_binary_r {op : SymBinOp} {l r : PExpr} {c : Aff} (h : c ∈ r.rcounts) :
    c ∈ (PExpr.binary op l r).rcounts := by simp [PExpr.rcounts, h]
theorem rcounts_ternary_t {x t e : PExpr} {c : Aff} (h : c ∈ t.rcounts) :
    c ∈ (PExpr.ternary x t e).rcounts := by simp [PExpr.rcounts, h]
theorem rcounts_ternary_e {x t e : PExpr} {c : Aff} (h : c ∈ e.rcounts) :
    c ∈ (PExpr.ternary x t e).rcounts := by simp [PExpr.rcounts, h]

/-- The constants of an operand are those of the expression around it (`ConstOK` descends). -/
theorem cok_binary_l {σ : String → Int} {ns : List String} {op : SymBinOp} {l r : PExpr}
    (h : ConstOK σ ns (.binary op l r)) : ConstOK σ ns l :=
  ⟨fun n hn => h.1 n (cnames_binary_l hn), fun c hc => h.2 c (rcounts_binary_l hc)⟩
theorem cok_binary_r {σ : String → Int} {ns : List String} {op : SymBinOp} {l r : PExpr}
    (h : ConstOK σ ns (.binary op l r)) : ConstOK σ ns r :=
  ⟨fun n hn => h.1 n (cnames_binary_r hn), fun c hc => h.2 c (rcounts_binary_r hc)⟩
theorem cok_unary {σ : String → Int} {ns : List String} {op : SymUnaryOp} {a : PExpr}
    (h : ConstOK σ ns (.unary op a)) : ConstOK σ ns a :=
  ⟨fun n hn => h.1 n (cnames_unary hn), fun c hc => h.2 c (by simpa [PExpr.rcounts] using hc)⟩
theorem cok_resize {σ : String → Int} {ns : List String} {m : Nat} {a : PExpr}
    (h : ConstOK σ ns (.resize m a)) : ConstOK σ ns a :=
  ⟨fun n hn => h.1 n (cnames_resize hn), fun c hc => h.2 c (by simpa [PExpr.rcounts] using hc)⟩
theorem cok_ternary_t {σ : String → Int} {ns : List String} {x t e : PExpr}
    (h : ConstOK σ ns (.ternary x t e)) : ConstOK σ ns t :=
  ⟨fun n hn => h.1 n (cnames_ternary_t hn), fun c hc => h.2 c (rcounts_ternary_t hc)⟩
theorem cok_ternary_e {σ : String → Int} {ns : List String} {x t e : PExpr}
    (h : ConstOK σ ns (.ternary x t e)) : ConstOK σ ns e :=
  ⟨fun n hn => h.1 n (cnames_ternary_e hn), fun c hc => h.2 c (rcounts_ternary_e hc)⟩

/-! ### Replication (WP-B2 gate 4c) -/

/-- The constants of a list of concatenation parts. -/
def PartsCO (σ : String → Int) (ns : List String) (ps : List PExpr) : Prop :=
  (∀ n ∈ ps.flatMap repNames, n ∈ ns) ∧ ∀ c ∈ ps.flatMap repCount, 0 ≤ c.eval σ

theorem partsCO_cons {σ : String → Int} {ns : List String} {p : PExpr} {ps : List PExpr}
    (h : PartsCO σ ns (p :: ps)) :
    PartsCO σ ns ps ∧ (∀ n ∈ repNames p, n ∈ ns) ∧ ∀ c ∈ repCount p, 0 ≤ c.eval σ := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨⟨fun n hn => h1 n (by simp [hn]), fun c hc => h2 c (by simp [hc])⟩,
    fun n hn => h1 n (by simp [hn]), fun c hc => h2 c (by simp [hc])⟩

/-- The argument of a replication is a literal (no read) or one access (a non-literal). -/
theorem notWhole_ok {r : Except String (List Acc)} {rs : List Acc} (h : notWhole r = .ok rs) :
    r = .ok rs ∧ ∀ n, rs ≠ [.whole n] := by
  rcases r with e | l
  · simp [notWhole] at h
  · rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
    · simp only [notWhole, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, fun n => by simp⟩
    · cases x <;> simp [notWhole] at h <;> (subst h; exact ⟨rfl, fun n => by simp⟩)
    · simp only [notWhole, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, fun n => by simp⟩

theorem repArgRd?_cases {ds : List DeclT} {a : PExpr} {rs : List Acc} (h : repArgRd? ds a = .ok rs) :
    (∃ v, a = .concat [.lit v] ∧ rs = []) ∨
      (∃ e, a = .concat [e] ∧ rdsLeaf? ds e = .ok rs ∧ (∀ v, e ≠ .lit v) ∧ ∀ n, rs ≠ [.whole n]) := by
  by_cases hc : ∃ e, a = .concat [e]
  · obtain ⟨e, rfl⟩ := hc
    by_cases hl : ∃ v, e = .lit v
    · obtain ⟨v, rfl⟩ := hl
      left
      exact ⟨v, rfl, by simpa [repArgRd?] using h.symm⟩
    · right
      have hnl : ∀ v, e ≠ .lit v := fun v hv => hl ⟨v, hv⟩
      have h' : notWhole (rdsLeaf? ds e) = .ok rs := by
        cases e <;> first | exact h | exact absurd rfl (hnl _)
      obtain ⟨h1, h2⟩ := notWhole_ok h'
      exact ⟨e, rfl, h1, hnl, h2⟩
  · exfalso
    cases a with
    | concat ps =>
        rcases ps with _ | ⟨e, _ | ⟨e2, t⟩⟩
        · simp [repArgRd?] at h
        · exact hc ⟨e, rfl⟩
        · simp [repArgRd?] at h
    | _ => simp [repArgRd?] at h

/-- A leaf read of a replication argument is not a replication. -/
theorem rdsLeaf_ne_repl {ds : List DeclT} {p : PExpr} {rs : List Acc} (h : rdsLeaf? ds p = .ok rs) :
    ∀ c a, p ≠ .repl c a := by
  intro c a hp
  subst hp
  simp [rdsLeaf?, leafRd?] at h

theorem repRd?_cases {ds : List DeclT} {c a : PExpr} {rs : List Acc} (h : repRd? ds c a = .ok rs) :
    ∃ k, affOf? c = some k ∧ repArgRd? ds a = .ok rs := by
  unfold repRd? at h
  rcases hk : affOf? c with _ | k
  · simp [hk] at h
  · simp only [hk] at h
    exact ⟨k, rfl, h⟩

/-- The count of a replication evaluates to its affine form and is non-negative (the scope and range facts of
`ConstOK`). -/
theorem repl_facts (C : Ctx σ E elems DW DG EW ns) {c a : PExpr} {k : Aff} (hk : affOf? c = some k)
    (hco : ConstOK σ ns (.repl c a)) : evalInt E c = .ok (k.eval σ) ∧ 0 ≤ k.eval σ := by
  have hn : ∀ n ∈ k.names, E.vals.lookup n = some (σ n) := by
    intro n hn
    apply C.agree n
    apply hco.1 n
    simp [PExpr.cnames, repAff, hk, hn]
  have hpos : 0 ≤ k.eval σ := by
    apply hco.2 k
    simp [PExpr.rcounts, repAff, hk]
  exact ⟨(affOf?_sound c k hk hn).2, hpos⟩

/-- **A replication instantiates to the replication of its argument at its own width.** -/
theorem inst_repl (C : Ctx σ E elems DW DG EW ns) {c a : PExpr} {k : Aff} (hk : affOf? c = some k)
    (hco : ConstOK σ ns (.repl c a)) (ctx : Option Nat) :
    instExpr2 E elems ctx (.repl c a) =
      .repl (k.eval σ).toNat (instExpr2 E elems (selfWidth2 E elems a) a) := by
  obtain ⟨hev, hpos⟩ := repl_facts C hk hco
  simp [instExpr2, hev, hpos]

/-- … and its self-determined width is the count times the argument's. -/
theorem selfWidth_repl (C : Ctx σ E elems DW DG EW ns) {c a : PExpr} {k : Aff} {w : Nat}
    (hk : affOf? c = some k) (hco : ConstOK σ ns (.repl c a)) (hw : selfWidth2 E elems a = some w) :
    selfWidth2 E elems (.repl c a) = some ((k.eval σ).toNat * w) := by
  obtain ⟨hev, hpos⟩ := repl_facts C hk hco
  simp [selfWidth2, hev, hpos, hw]

/-- … and `RdOK`. -/
theorem rd_repl (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {c a : PExpr} {rs : List Acc}
    (h : repRd? ds c a = .ok rs) (hacc : ∀ x ∈ rs, AccOK σ DW DG EW ns x) (hco : ConstOK σ ns (.repl c a))
    (ctx : Option Nat) : RdOK σ rs (instExpr2 E elems ctx (.repl c a)) := by
  obtain ⟨k, hk, harg⟩ := repRd?_cases h
  rw [inst_repl C hk hco ctx]
  refine RdOK.repl _ ?_
  rcases repArgRd?_cases harg with ⟨v, rfl, rfl⟩ | ⟨e, rfl, hl, -, -⟩
  · rw [instExpr2_concat, instParts2_cons, instParts2_nil]
    have h1 : RdOK σ [] (instExpr2 E elems (selfWidth2 E elems (.lit v)) (.lit v)) := by
      simp [instExpr2, RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
    exact RdOK.concat_cons h1 RdOK.concat_nil
  · rw [instExpr2_concat, instParts2_cons, instParts2_nil]
    have h1 := inst_rdsLeaf C hl hacc (selfWidth2 E elems e)
    have h2 := RdOK.concat_cons h1 (RdOK.concat_nil (σ := σ))
    rwa [List.append_nil] at h2

/-- The parts of a word-level concatenation (literals, accesses, replications). -/
theorem inst_partsW (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRdW? ds ps = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → PartsCO σ ns ps →
      RdOK σ rs (.concat (instParts2 E elems ps).toArray)
  | [], rs, h, _, _ => by
      simp only [partsRdW?, Except.ok.injEq] at h
      subst h
      simp only [instParts2_nil]
      exact RdOK.concat_nil
  | p :: ps, rs, h, hacc, hco => by
      simp only [partsRdW?] at h
      rcases hp : partRdW? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRdW? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          obtain ⟨hco', hn, hc⟩ := partsCO_cons hco
          have h1 : RdOK σ ra (instExpr2 E elems (selfWidth2 E elems p) p) := by
            unfold partRdW? at hp
            cases p with
            | lit v =>
                simp only [Except.ok.injEq] at hp
                subst hp
                simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
            | repl c a =>
                exact rd_repl C hp (fun x hx => hacc x (List.mem_append_left _ hx))
                  ⟨fun n hn' => hn n hn', fun k hk => hc k hk⟩ _
            | _ =>
                exact inst_rdsLeaf C hp (fun a ha => hacc a (List.mem_append_left _ ha)) _
          have h2 := inst_partsW C ps rb hq (fun a ha => hacc a (List.mem_append_right _ ha)) hco'
          rw [instParts2_cons]
          exact RdOK.concat_cons h1 h2

/-- **The reads of the amount of a shift**, at any context: as `rd_shOpd`, or a genvar bound in the instance (a literal of
its value at the amount's own width). -/
theorem rd_shAmt (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {e : PExpr} {rs : List Acc}
    (h : shAmtRd? ds e = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a)
    (hg : ∀ g, e = .genvarRef g → g ∈ ns)
    (hp : ∀ n, e = .paramRef n none → n ∈ ns) (c : Option Nat) :
    RdOK σ rs (instDivOperand2 E elems false c e) := by
  rcases shAmtRd?_cases h with ⟨g, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | h'
  · have hb : E.vals.lookup g = some (σ g) := C.agree g (hg g rfl)
    have e1 : instDivOperand2 E elems false c (.genvarRef g) =
        fitDivOperand2 false c (some 32) (.lit (LVec.ofInt 32 (σ g))) := by
      simp [instDivOperand2, instExpr2, hb, divOperandWidth2] <;> first | done | rfl
    rw [e1]
    refine RdOK.fitDiv ?_ false _ _
    simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  · have hb : E.vals.lookup n = some (σ n) := C.agree n (hp n rfl)
    have e1 : instDivOperand2 E elems false c (.paramRef n none) =
        fitDivOperand2 false c (some 32) (.lit (LVec.ofInt 32 (σ n))) := by
      simp [instDivOperand2, instExpr2, intLit2_eq, hb, divOperandWidth2]
    rw [e1]
    refine RdOK.fitDiv ?_ false _ _
    simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  · exact rd_shOpd C h' hacc false c

/-- … and of the left operand of a shift (the marker is transparent). -/
theorem rd_shLeft (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {s : Bool} {e : PExpr} {rs : List Acc}
    (h : shLeftRd? ds s e = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (c : Option Nat) :
    RdOK σ rs (instDivOperand2 E elems s c e) := by
  obtain ⟨x, hx, hxo⟩ := shLeftRd?_cases h
  rcases hx with rfl | ⟨rfl, m, rfl⟩ | ⟨rfl, m, rfl⟩
  · exact rd_shOpd C hxo hacc s c
  · rw [instDiv_resize false c m x (shOpdKind hxo)]
    exact rd_shOpd C hxo hacc false _
  · rw [instDiv_sresize true c m x]
    exact rd_shOpd C hxo hacc true _

/-- **The reads of an expression of the word-level fragment** (WP-B2), at any context: the context-determined
positions through `rdsOfW?`, the self-determined operands through the v1 theorem `inst_rd`. -/
theorem inst_rdW (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} :
    ∀ (e : PExpr) (rs : List Acc), rdsOfW? ds e = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ConstOK σ ns e → ∀ ctx, RdOK σ rs (instExpr2 E elems ctx e)
  | .lit v, rs, h, _, _, ctx => by
      simp only [rdsOfW?, Except.ok.injEq] at h
      subst h
      simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  | .binary op l r, rs, h, hacc, hcn, ctx => by
      rcases rdsOfW?_binary h with ⟨hb, ra, rb, hl, hr', rfl⟩ | ⟨hb, ra, rb, hl, hr', rfl⟩ |
        ⟨hb, ra, rb, hl, hr', rfl⟩
      · have ihl := inst_rdW C l ra hl (fun a ha => hacc a (List.mem_append_left _ ha))
          (cok_binary_l hcn)
        have ihr := inst_rdW C r rb hr' (fun a ha => hacc a (List.mem_append_right _ ha))
          (cok_binary_r hcn)
        have hfl := RdOK.fit (E := E) (elems := elems) (signedCast_of_rdsW hl) ihl
        have hfr := RdOK.fit (E := E) (elems := elems) (signedCast_of_rdsW hr') ihr
        have gate : ∀ g : BinOp, (g = .and ∨ g = .or ∨ g = .xor) →
            RdOK σ (ra ++ rb) (instExpr2 E elems ctx (.binary (.m0 g) l r)) := by
          intro g hg
          obtain ⟨c, hc⟩ := instExpr2_gate E elems ctx g hg l r
          rw [hc]
          exact RdOK.binary _ (hfl c) (hfr c)
        have addsub : ∀ g : BinOp, (g = .add ∨ g = .sub) →
            RdOK σ (ra ++ rb) (instExpr2 E elems ctx (.binary (.m0 g) l r)) := by
          intro g hg
          rcases ie_addsub_cases (env := E) (elems := elems) g hg ctx l r with ⟨c, hc⟩ | ⟨w, c, hc⟩
          · rw [hc]; exact RdOK.binary _ (hfl c) (hfr c)
          · rw [hc]; exact RdOK.resize w (RdOK.binary _ (hfl c) (hfr c))
        rcases ctxOpW_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | ⟨cm, rfl⟩
        · exact gate .and (Or.inl rfl)
        · exact gate .or (Or.inr (Or.inl rfl))
        · exact gate .xor (Or.inr (Or.inr rfl))
        · exact addsub .add (Or.inl rfl)
        · exact addsub .sub (Or.inr rfl)
        · rcases ie_mul_cases (env := E) (elems := elems) (rdsOfW?_mul h) ctx with ⟨c, hc⟩ | ⟨w, c, hc⟩
          · rw [hc]; exact RdOK.binary _ (hfl c) (hfr c)
          · rw [hc]; exact RdOK.resize w (RdOK.binary _ (hfl c) (hfr c))
        · obtain ⟨c, hc⟩ := ie_cmp_cases (env := E) (elems := elems) cm ctx l r
          rw [hc]; exact RdOK.binary _ (hfl c) (hfr c)
      · have ihl := inst_rd C l ra hl (fun a ha => hacc a (List.mem_append_left _ ha))
        have ihr := inst_rd C r rb hr' (fun a ha => hacc a (List.mem_append_right _ ha))
        rcases selfOpW_cases hb with rfl | rfl
        · rw [ie_land]; exact RdOK.logical true (ihl _) (ihr _)
        · rw [ie_lor]; exact RdOK.logical false (ihl _) (ihr _)
      · -- a run-time shift (WP-B2 gate 3)
        have hR := rd_shAmt C hr' (fun a ha => hacc a (List.mem_append_right _ ha))
          (fun g hgr => hcn.1 g (cnames_amount hb hgr))
          (fun n hnr => hcn.1 n (cnames_amount_param hb hnr))
        rcases shOpW_cases hb with ⟨s, rfl⟩ | rfl
        · have hL : ∀ c, RdOK σ ra (instDivOperand2 E elems s c l) :=
            rd_shLeft C hl (fun a ha => hacc a (List.mem_append_left _ ha))
          obtain ⟨lc, hlc⟩ := ie_shl_form (env := E) (elems := elems) s ctx l r
          rw [hlc]; exact RdOK.ctxTrunc (RdOK.binary _ (hL lc) (hR _)) ctx lc
        · have hL : ∀ c, RdOK σ ra (instDivOperand2 E elems false c l) :=
            rd_shLeft C hl (fun a ha => hacc a (List.mem_append_left _ ha))
          obtain ⟨lc, hlc⟩ := ie_shr_form (env := E) (elems := elems) ctx l r
          rw [hlc]; exact RdOK.ctxTrunc (RdOK.binary _ (hL lc) (hR _)) ctx lc
  | .unary op a, rs, h, hacc, hcn, ctx => by
      rcases rdsOfW?_unary h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · have iha := inst_rdW C a rs ha hacc (cok_unary hcn)
        have hs := signedCast_of_rdsW ha
        rcases ie_bnot_cases (env := E) (elems := elems) ctx a with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨w, c, hc⟩
        · rw [hc]; exact RdOK.unary _ (iha c)
        · rw [hc]; exact RdOK.unary _ (RdOK.fit hs iha c)
        · rw [hc]; exact RdOK.resize w (RdOK.unary _ (RdOK.fit hs iha c))
      · have iha := inst_rd C a rs ha hacc
        rw [ie_lnot]; exact RdOK.unary _ (iha none)
  | .ternary c t e, rs, h, hacc, hcn, ctx => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := rdsOfW?_ternary h
      have ihc := inst_rd C c rc hc
        (fun a ha => hacc a (List.mem_append_left _ (List.mem_append_left _ ha)))
      have iht := inst_rdW C t rt ht
        (fun a ha => hacc a (List.mem_append_left _ (List.mem_append_right _ ha)))
        (cok_ternary_t hcn)
      have ihe := inst_rdW C e re he (fun a ha => hacc a (List.mem_append_right _ ha))
        (cok_ternary_e hcn)
      obtain ⟨a0, ha0⟩ := ie_ternary_cases (env := E) (elems := elems) ctx c t e
      rw [ha0]
      exact RdOK.ternary (ihc none) (RdOK.fit (signedCast_of_rdsW ht) iht a0)
        (RdOK.fit (signedCast_of_rdsW he) ihe a0)
  | .reduce op a, rs, h, hacc, hcn, ctx => by
      have iha := inst_rd C a rs (rdsOfW?_reduce h) hacc
      rw [ie_reduce]; exact RdOK.reduce _ (iha _)
  | .concat ps, rs, h, hacc, hcn, ctx => by
      simp only [rdsOfW?] at h
      rw [instExpr2_concat]
      exact inst_partsW C ps rs h hacc hcn
  | .repl c a, rs, h, hacc, hcn, ctx => rd_repl C h hacc hcn ctx
  | .resize m e, rs, h, hacc, hcn, ctx => by
      rcases rdsOfW?_resize h with ⟨v, rfl, rfl⟩ | ⟨hn, a, hl, rfl⟩ | ⟨hop, hr⟩
      · obtain ⟨x, c, hx⟩ := ie_resize_cases (env := E) (elems := elems) (e := .lit v)
          rfl rfl (fun _ _ _ => by simp [PExpr.negGenvarWidened]) ctx m
        rw [hx]
        exact RdOK.resize x (by simp [RdOK, instExpr2, Expr2.unsupportedFree, Expr2.reads, Expr2.idents])
      · obtain ⟨hcp, hcl, hng⟩ := leaf_flags hl
        obtain ⟨x, c, hx⟩ := ie_resize_cases (env := E) (elems := elems) hcp hcl hng ctx m
        rw [hx]
        exact RdOK.resize x (inst_rdsLeaf C (ds := ds) (e := e) (rs := [a]) (by simp [rdsLeaf?, hl]) hacc c)
      · have ih := inst_rdW C e rs hr hacc (cok_resize hcn)
        rcases ie_resize_op (env := E) (elems := elems) hop ctx m with ⟨x, c, hx⟩ | ⟨cw, hx⟩
        · rw [hx]; exact RdOK.resize x (ih c)
        · rw [hx]; exact ih _
  | .int v, rs, h, _, _, ctx => by
      simp only [rdsOfW?, Except.ok.injEq] at h
      subst h
      rw [ie_int]
      simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  | .ident n, rs, h, hacc, hcn, ctx => inst_rdsLeaf C (by simpa [rdsOfW?] using h) hacc ctx
  | .bitSel b i, rs, h, hacc, hcn, ctx => inst_rdsLeaf C (by simpa [rdsOfW?] using h) hacc ctx
  | .partSel b m l, rs, h, hacc, hcn, ctx => inst_rdsLeaf C (by simpa [rdsOfW?] using h) hacc ctx
  | .arrayElem n is, rs, h, hacc, hcn, ctx => inst_rdsLeaf C (by simpa [rdsOfW?] using h) hacc ctx
  | .arrayPart n is m a b, rs, h, hacc, hcn, ctx => inst_rdsLeaf C (by simpa [rdsOfW?] using h) hacc ctx
  | .paramRef .., rs, h, _, _, _
  | .genvarRef .., rs, h, _, _, _ | .enumRef .., rs, h, _, _, _
  | .fill .., rs, h, _, _, _
  | .signedResize .., rs, h, _, _, _
  | .squash2 .., rs, h, _, _, _ | .sysCall .., rs, h, _, _, _
  | .cast .., rs, h, _, _, _ | .unsupported .., rs, h, _, _, _ => by
      simp [rdsOfW?, rdsLeaf?, leafRd?] at h

/-- The right-hand side of a site of the word-level fragment, at the target's width. -/
theorem rhs_ok (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {v : PExpr} {rds : List Acc}
    (h : rhsRds? ds v = .ok rds) (hacc : ∀ a ∈ rds, AccOK σ DW DG EW ns a) (hcn : ConstOK σ ns v)
    (w : Nat) :
    RdOK σ rds (fitExpr2 E elems (some w) v) := by
  by_cases hf : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hf
    simp only [rhsRds?, Except.ok.injEq] at h
    subst h
    rw [fitExpr2_of_not_rigid w rfl]
    simp [instExpr2, RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  · have hr : rhsRds? ds v = rdsOfW? ds v := by
      cases v <;> first | rfl | (exfalso; exact hf ⟨_, rfl⟩)
    rw [hr] at h
    exact RdOK.fit (signedCast_of_rdsW h) (inst_rdW C v rds h hacc hcn) (some w)

/-! ## One site -/

/-- The instantiated process `p` is an `assign` to the footprint's target (the footprint has no further window),
reading only the footprint's reads. -/
def Desc (names : List String) (si : SiteInst) (p : Process2) : Prop :=
  ∃ e, p = .assign si.tgt e ∧ (∀ r ∈ e.reads, r ∈ si.rd) ∧ e.unsupportedFree = true ∧
    (∀ x ∈ e.idents, x ∈ names) ∧ si.more = []

/-- The lowering of a target access: the promised `Lhs2`, whatever the context width. -/
theorem instLhs_acc (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {l : PLhs} {a : Acc}
    (h : tgtOf? ds l = .ok a) (ha : AccOK σ DW DG EW ns a) :
    ∃ w, instLhs2 E elems l = .ok (a.lhs σ, w) := by
  obtain ⟨hdec, hgeo, hns⟩ := ha
  have hagx : ∀ x ∈ a.affs, ∀ n ∈ x.names, E.vals.lookup n = some (σ n) :=
    fun x hx n hn => C.agree n (hns x hx n hn)
  rcases tgtOf?_cases h with ⟨n, rfl, rfl⟩ | ⟨n, i, x, rfl, hx, hba⟩ | ⟨n, is, rfl, he⟩ |
    ⟨n, is, mode, hi, lo, rfl, hp⟩ | ⟨n, msb, lsb, rfl, hp⟩
  · -- whole signal
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hdec
    have hW : E.widths.lookup n = some w := by rw [C.widths n]; simpa [Acc.name] using hw
    exact ⟨w, by rw [instLhs2_ident hW]; rfl⟩
  · -- n[i]
    rcases bitAcc?_cases ds n x with hb | ⟨w, hb⟩ <;> rw [hb] at hba <;> simp only [Except.ok.injEq] at hba <;>
      subst hba
    · obtain ⟨hnn, hel⟩ := hgeo
      have hel' : elems.lookup n = some 1 := C.elems n hel
      obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      exact ⟨1, by rw [instLhs2_bitSel hel' hev hnn]; simp [Acc.lhs, Acc.lo]⟩
    · -- a legacy select of a row
      obtain ⟨m1, m2, hdg, hm2, hw, hx0, hx1⟩ := hgeo
      have hel' := ctxElemsRow C hdg hm2
      obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      exact ⟨(m2 + 1).toNat, by
        rw [instLhs2_bitSel hel' hev hx0]
        simp [Acc.lhs, Acc.lo, Acc.wid, rmN, hw]⟩
  · -- element path
    rw [instLhs2_arrayElem]
    rcases elemAcc?_cases he with ⟨i, x, rfl, hx, rfl⟩ | ⟨i, x, w, rfl, hx, rfl⟩ |
      ⟨i, j, x, y, w, rfl, hx, hy, rfl⟩
    · obtain ⟨m, hdg, hx0, hx1⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      exact ⟨1, by
        rw [arrayElemTarget_of_inRange (arrayElemWindow_1d_in hd hev hx0 hx1)]
        simp [Acc.lhs, Acc.lo]⟩
    · obtain ⟨m1, m2, hdg, hm2, hw, hx0, hx1⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      have hrow := rmN_row_toNat (W := m2 + 1) (i := x.eval σ) (by omega) hx0
      exact ⟨(m2 + 1).toNat, by
        rw [arrayElemTarget_of_inRange (arrayElemWindow_row hd hm2 hev hx0 hx1)]
        simp [Acc.lhs, Acc.lo, Acc.wid, hw, hrow]⟩
    · obtain ⟨m1, m2, hdg, hw, hx0, hx1, hy0, hy1⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, hevi⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      obtain ⟨-, hevj⟩ := affOf?_sound j y hy (hagx y (by simp [Acc.affs]))
      have hcell := rmN_eq_toNat (W := m2 + 1) (i := x.eval σ) (j := y.eval σ) (by omega) hx0 hy0
      exact ⟨1, by
        rw [arrayElemTarget_of_inRange (arrayElemWindow_cell2 hd hevi hx0 hx1 hevj hy0 hy1)]
        simp [Acc.lhs, Acc.lo, hw, hcell]⟩
  · -- part path
    rw [instLhs2_arrayPart]
    obtain ⟨rfl, hc⟩ := partAcc?_cases hp
    rcases hc with ⟨x, y, rfl, hx, hy, rfl⟩ | ⟨i, r, x, y, w, rfl, hr, hx, hy, rfl⟩
    · obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, heh⟩ := affOf?_sound hi x hx (hagx x (by simp [Acc.affs]))
      obtain ⟨-, hel⟩ := affOf?_sound lo y hy (hagx y (by simp [Acc.affs]))
      exact ⟨(x.eval σ - y.eval σ + 1).toNat, by
        rw [arrayPartTarget_part1 hd (by omega) heh hel hy0 hyx hxm]
        simp [Acc.lhs, Acc.lo, Acc.wid]⟩
    · obtain ⟨m1, m2, hdg, hw, hr0, hr1, hy0, hyx, hxm⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, hei⟩ := affOf?_sound i r hr (hagx r (by simp [Acc.affs]))
      obtain ⟨-, heh⟩ := affOf?_sound hi x hx (hagx x (by simp [Acc.affs]))
      obtain ⟨-, hel⟩ := affOf?_sound lo y hy (hagx y (by simp [Acc.affs]))
      have hcell := rmN_eq_toNat (W := m2 + 1) (i := r.eval σ) (j := y.eval σ) (by omega) hr0 hy0
      exact ⟨(x.eval σ - y.eval σ + 1).toNat, by
        rw [arrayPartTarget_part2 hd hei hr0 hr1 heh hel hy0 hyx hxm]
        simp [Acc.lhs, Acc.lo, Acc.wid, hw, hcell]⟩
  · -- legacy part select
    obtain ⟨-, hc⟩ := partAcc?_cases hp
    rcases hc with ⟨x, y, -, hx, hy, rfl⟩ | ⟨i, r, x, y, w, hnil, -⟩
    · obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hgeo
      exact ⟨(x.eval σ - y.eval σ + 1).toNat, by
        rw [instLhs_partSel C hdg hx hy hagx hy0 hyx]
        simp [Acc.lhs, Acc.lo, Acc.wid]⟩
    · exact absurd hnil (by simp)

theorem desc_mk {names : List String} {si : SiteInst} {p : Process2}
    {t : Lhs2} {x : Expr2} {rds : List Acc} (hp : p = .assign t x) (ht : si.tgt = t)
    (hrd : RdOK σ rds x) (hsi : si.rd = rds.map (Acc.rd σ))
    (hnm : ∀ r ∈ rds, r.name ∈ names) (hmore : si.more = []) : Desc names si p := by
  refine ⟨x, by rw [hp, ht], fun r hr => hsi ▸ hrd.2.1 r hr, hrd.1, fun i hi => ?_, hmore⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (hrd.2.2 i hi)
  exact hnm r hr

/-- **The per-site soundness theorem.** -/
theorem site_desc (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {names : List String}
    (hnm : ∀ n, (DW n).isSome = true → n ∈ names)
    {pos : Nat} {p : PProcess} {st : TSite} (hs : siteOf? ds pos p = .ok st)
    (hso : ∀ a ∈ st.tgt :: st.rds, AccOK σ DW DG EW ns a) (hcn : st.ConstOK σ ns) {si : SiteInst}
    (htgt : si.tgt = st.tgt.lhs σ) (hrd : si.rd = st.rds.map (Acc.rd σ)) (hmore : si.more = []) :
    Desc names si (instProcess2 E elems p) := by
  have hrdacc : ∀ rds, rds = st.rds → ∀ a ∈ rds, AccOK σ DW DG EW ns a := by
    rintro rds rfl a ha
    exact hso a (List.mem_cons_of_mem _ ha)
  have hrdn : ∀ rds, rds = st.rds → ∀ r ∈ rds, r.name ∈ names := by
    rintro rds rfl r hr
    exact hnm _ (hso r (List.mem_cons_of_mem _ hr)).1
  rcases siteOf?_cases hs with ⟨t, v, rds, rfl, hrds, rfl⟩ | ⟨l, v, tg, rds, rfl, htg, hrds, rfl⟩
  · -- `assign t = v`
    have hdt : (DW t).isSome = true := (hso _ (List.mem_cons_self ..)).1
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hdt
    have hW : E.widths.lookup t = some w := by rw [C.widths t, hw]
    rw [instProcess2_assign v hW]
    exact desc_mk rfl (by simpa [Acc.lhs] using htgt)
      (rhs_ok C hrds (hrdacc _ rfl) hcn _) hrd (hrdn _ rfl) hmore
  · obtain ⟨w, hl⟩ := instLhs_acc C htg (hso _ (List.mem_cons_self ..))
    rw [instProcess2_assignL v hl]
    exact desc_mk rfl htgt (rhs_ok C hrds (hrdacc _ rfl) hcn _) hrd (hrdn _ rfl) hmore

end sites

end CombView
end LeanModels.Sv
