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
    (∃ n i x, l = .bitSel n i ∧ affOf? i = some x ∧ a = .bit n x) ∨
    (∃ n is, l = .arrayElem n is ∧ elemAcc? ds n is = .ok a) ∨
    (∃ n is mode hi lo, l = .arrayPart n is mode hi lo ∧ partAcc? ds n is mode hi lo = .ok a) := by
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
    · simp only [hx, Except.ok.injEq] at h
      exact ⟨n, i, x, rfl, hx, h.symm⟩
  | partSel n m l => simp [tgtOf?] at h
  | concat ps => simp [tgtOf?] at h
  | arrayElem n is => right; right; left; exact ⟨n, is, rfl, h⟩
  | arrayPart n is mode hi lo => right; right; right; exact ⟨n, is, mode, hi, lo, rfl, h⟩

theorem siteOf?_cases {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOf? ds pos p = .ok st) :
    (∃ t v rds, p = .assign t v ∧ rhsRds? ds v = .ok rds ∧ st = ⟨pos, .whole t, rds, p⟩) ∨
    (∃ l v tg rds, p = .assignL l v ∧ tgtOf? ds l = .ok tg ∧ rhsRds? ds v = .ok rds ∧
      st = ⟨pos, tg, rds, p⟩) := by
  cases p with
  | assign t v =>
    left
    simp only [siteOf?] at h
    rcases hr : rhsRds? ds v with e | rds
    · simp [hr] at h
    · simp only [hr, Except.ok.injEq] at h
      exact ⟨t, v, rds, rfl, hr, h.symm⟩
  | assignL l v =>
    right
    simp only [siteOf?] at h
    rcases ht : tgtOf? ds l with e | tg
    · simp [ht] at h
    · rcases hr : rhsRds? ds v with e | rds
      · simp [ht, hr] at h
      · simp only [ht, hr, Except.ok.injEq] at h
        exact ⟨l, v, tg, rds, rfl, ht, hr, h.symm⟩
  | alwaysFF _ _ => simp [siteOf?] at h
  | alwaysPlain _ _ => simp [siteOf?] at h
  | alwaysComb _ => simp [siteOf?] at h
  | alwaysFFR _ _ _ => simp [siteOf?] at h
  | unsupported _ _ => simp [siteOf?] at h

theorem siteOf?_proc {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOf? ds pos p = .ok st) : st.proc = p := by
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

/-! ## Derived definitions on the summary -/

/-- Structural well-formedness of a summary: decidable closed data, discharged by `decide`. -/
def Summary.StructOk (s : Summary) : Prop :=
  s.declNames.Nodup ∧
  (∀ ls ∈ s.lsites, ∀ n ∈ ls.site.names, n ∈ s.declNames) ∧
  (∀ ls ∈ s.lsites, ls.site.tgt.name ∉ s.inputNames) ∧
  (∀ ls ∈ s.lsites, ∀ n ∈ ls.site.affNames, n ∈ ls.hdrs.map (·.g) ++ s.params) ∧
  (∀ p ∈ s.hdrPaths, (p.map (·.g) ++ s.params).Nodup ∧
    ∀ h ∈ p, (∀ n ∈ h.bound.names, n ∈ s.params) ∧ 0 ≤ h.c0) ∧
  (∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, n ∈ s.params) ∧
  (∀ ls ∈ s.lsites, ∀ a ∈ ls.site.tgt :: ls.site.rds, s.accOk a = true) ∧
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
  (∀ ls ∈ s.lsites, ∀ a ∈ ls.site.tgt :: ls.site.rds, s.DimNum σ a) ∧
  (∀ p ∈ s.hdrPaths, ∀ h ∈ p, (h.bound.eval σ - h.c0).toNat ≤ 4 * (args.map Int.natAbs).sum + 60)

def InRangeObl (σ : String → Int) : Prop :=
  ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' => s.InWin σ σ' ls.site

/-- The sites that drive (a window of) the signal `n`. -/
def writersOf (n : String) : List LSite := s.lsites.filter fun b => b.site.tgt.name == n

/-- **One driver per bit** for a pair of located sites: at every pair of loop valuations that are
not the same instance, the write windows are disjoint. -/
def DisjOne (σ : String → Int) (a b : LSite) : Prop :=
  Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
    a.id σ1 ≠ b.id σ2 →
      Win.overlaps (a.site.tgt.win σ1 (s.dw σ)) (b.site.tgt.win σ2 (s.dw σ)) = false

def DisjObl (σ : String → Int) : Prop :=
  s.lsites.Pairwise (s.DisjOne σ) ∧ ∀ a ∈ s.lsites, s.DisjOne σ a a

/-- **The rank decreases along every read** (design principle 13: sites by identity): whenever a
read window of `a` overlaps the window `b` writes, `b`'s identity is related to `a`'s by `R`
(writer first). -/
def RankObl' (R : SiteId → SiteId → Prop) (σ : String → Int) : Prop :=
  ∀ a ∈ s.lsites, ∀ r ∈ a.site.rds, ∀ b ∈ s.writersOf r.name,
    Loops.all a.hdrs σ fun σ1 => Loops.all b.hdrs σ fun σ2 =>
      ReadWin.overlaps (r.rd σ1) (b.site.tgt.win σ2 (s.dw σ)) = true → R (b.id σ2) (a.id σ1)

/-- … for a `Nat`-valued rank over site identities. -/
def RankObl (ρ : SiteId → Nat) (σ : String → Int) : Prop :=
  s.RankObl' (fun w r => ρ w < ρ r) σ

/-- … for a lexicographic key over site identities (row, column, phase). -/
def LexObl (κ : SiteId → Key) (σ : String → Int) : Prop :=
  s.RankObl' (fun w r => KLt (κ w) (κ r)) σ

end Summary

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

theorem sw_lnot (a : PExpr) : selfWidth2 env elems (.unary (.m0 .lnot) a) = some 1 := by
  simp [selfWidth2]

theorem sw_bnot (a : PExpr) :
    selfWidth2 env elems (.unary (.m0 .bnot) a) = selfWidth2 env elems a := by
  simp [selfWidth2]

theorem sw_land (l r : PExpr) : selfWidth2 env elems (.binary .land l r) = some 1 := by
  simp [selfWidth2]

theorem sw_lor (l r : PExpr) : selfWidth2 env elems (.binary .lor l r) = some 1 := by
  simp [selfWidth2]

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

/-- The instantiation environment's facts the site lemmas read. -/
structure Ctx (σ : String → Int) (E : IEnv) (elems : List (String × Nat))
    (DW : String → Option Nat) (DG : String → Option (List (Int × Int)))
    (EW : String → Option Nat) (ns : List String) : Prop where
  agree : Agrees σ E ns
  widths : ∀ n, E.widths.lookup n = DW n
  elems : ∀ n, EW n = some 1 → elems.lookup n = some 1
  dims : ∀ n ds, DG n = some ds → E.dims.lookup n = some ds

theorem Ctx.bindVal {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
    {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
    {EW : String → Option Nat} {ns : List String}
    (C : Ctx σ E elems DW DG EW ns) (g : String) (i : Int) :
    Ctx (bindσ g i σ) (E.bindVal g i) elems DW DG EW (g :: ns) :=
  ⟨C.agree.bindVal g i, C.widths, C.elems, C.dims⟩

/-- Everything a site lemma needs about one access. -/
def AccOK (σ : String → Int) (DW : String → Option Nat)
    (DG : String → Option (List (Int × Int))) (EW : String → Option Nat) (ns : List String)
    (a : Acc) : Prop :=
  (DW a.name).isSome = true ∧ AccGeom σ DG EW a ∧ ∀ x ∈ a.affs, ∀ n ∈ x.names, n ∈ ns

section sites

variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

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
          · simp only [hx, Except.ok.injEq] at h
            subst h
            obtain ⟨hnn, hel⟩ := hgeo
            have hel' : elems.lookup n = some 1 := C.elems n hel
            obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
            rw [instExpr2_bitSel_ident ctx hel' hev hnn]
            simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
              Acc.rd, Acc.name, Acc.lo]
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
  | .arrayElem n is, rs, h, hacc, ctx => inst_rdsLeaf C (by simpa [rdsOf?] using h) hacc ctx
  | .arrayPart n is m a b, rs, h, hacc, ctx => inst_rdsLeaf C (by simpa [rdsOf?] using h) hacc ctx
  | .partSel .., rs, h, _, _ | .repl .., rs, h, _, _
  | .paramRef .., rs, h, _, _
  | .genvarRef .., rs, h, _, _ | .enumRef .., rs, h, _, _
  | .int .., rs, h, _, _ | .fill .., rs, h, _, _
  | .resize .., rs, h, _, _ | .signedResize .., rs, h, _, _
  | .squash2 .., rs, h, _, _ | .sysCall .., rs, h, _, _
  | .cast .., rs, h, _, _ | .unsupported .., rs, h, _, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

/-- The right-hand side of a site, at the target's width. -/
theorem rhs_ok (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {v : PExpr} {rds : List Acc}
    (h : rhsRds? ds v = .ok rds) (hacc : ∀ a ∈ rds, AccOK σ DW DG EW ns a) (w : Nat) :
    RdOK σ rds (fitExpr2 E elems (some w) v) := by
  by_cases hf : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hf
    simp only [rhsRds?, Except.ok.injEq] at h
    subst h
    rw [fitExpr2_of_not_rigid w rfl]
    simp [instExpr2, RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  · have hr : rhsRds? ds v = rdsOf? ds v := by
      cases v <;> first | rfl | (exfalso; exact hf ⟨_, rfl⟩)
    rw [hr] at h
    exact RdOK.fit (signedCast_of_rds h) (inst_rd C v rds h hacc) (some w)

/-! ## One site -/

/-- The instantiated process `p` is an `assign` to the footprint's target, reading only the
footprint's reads. -/
def Desc (names : List String) (si : SiteInst) (p : Process2) : Prop :=
  ∃ e, p = .assign si.tgt e ∧ (∀ r ∈ e.reads, r ∈ si.rd) ∧ e.unsupportedFree = true ∧
    ∀ x ∈ e.idents, x ∈ names

/-- The lowering of a target access: the promised `Lhs2`, whatever the context width. -/
theorem instLhs_acc (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {l : PLhs} {a : Acc}
    (h : tgtOf? ds l = .ok a) (ha : AccOK σ DW DG EW ns a) :
    ∃ w, instLhs2 E elems l = .ok (a.lhs σ, w) := by
  obtain ⟨hdec, hgeo, hns⟩ := ha
  have hagx : ∀ x ∈ a.affs, ∀ n ∈ x.names, E.vals.lookup n = some (σ n) :=
    fun x hx n hn => C.agree n (hns x hx n hn)
  rcases tgtOf?_cases h with ⟨n, rfl, rfl⟩ | ⟨n, i, x, rfl, hx, rfl⟩ | ⟨n, is, rfl, he⟩ |
    ⟨n, is, mode, hi, lo, rfl, hp⟩
  · -- whole signal
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hdec
    have hW : E.widths.lookup n = some w := by rw [C.widths n]; simpa [Acc.name] using hw
    exact ⟨w, by rw [instLhs2_ident hW]; rfl⟩
  · -- n[i]
    obtain ⟨hnn, hel⟩ := hgeo
    have hel' : elems.lookup n = some 1 := C.elems n hel
    obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
    exact ⟨1, by rw [instLhs2_bitSel hel' hev hnn]; simp [Acc.lhs, Acc.lo]⟩
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

theorem desc_mk {names : List String} {si : SiteInst} {p : Process2}
    {t : Lhs2} {x : Expr2} {rds : List Acc} (hp : p = .assign t x) (ht : si.tgt = t)
    (hrd : RdOK σ rds x) (hsi : si.rd = rds.map (Acc.rd σ))
    (hnm : ∀ r ∈ rds, r.name ∈ names) : Desc names si p := by
  refine ⟨x, by rw [hp, ht], fun r hr => hsi ▸ hrd.2.1 r hr, hrd.1, fun i hi => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (hrd.2.2 i hi)
  exact hnm r hr

/-- **The per-site soundness theorem.** -/
theorem site_desc (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {names : List String}
    (hnm : ∀ n, (DW n).isSome = true → n ∈ names)
    {pos : Nat} {p : PProcess} {st : TSite} (hs : siteOf? ds pos p = .ok st)
    (hso : ∀ a ∈ st.tgt :: st.rds, AccOK σ DW DG EW ns a) {si : SiteInst}
    (htgt : si.tgt = st.tgt.lhs σ) (hrd : si.rd = st.rds.map (Acc.rd σ)) :
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
      (rhs_ok C hrds (hrdacc _ rfl) _) hrd (hrdn _ rfl)
  · obtain ⟨w, hl⟩ := instLhs_acc C htg (hso _ (List.mem_cons_self ..))
    rw [instProcess2_assignL v hl]
    exact desc_mk rfl htgt (rhs_ok C hrds (hrdacc _ rfl) _) hrd (hrdn _ rfl)

end sites

end CombView
end LeanModels.Sv
