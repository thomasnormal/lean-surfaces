import LeanModels.Sv.CombEqBase

/-!
# `sv_equations`, stage 2: what the instantiated right-hand side is, and its Boolean value

`CombEqBase.lean` defines the skeleton `Sk` of a right-hand side and its lowering `Sk.low`. Here the
lowering is proved to BE what `instantiate2` builds (`proc_shape`), for a site whose operands are
exactly as wide as the target (`Sk.WidthOk`), and the lowered expression is shown to lie in the x-free
fragment of `CombKnownBits.lean` with `Expr2.xfBits = Sk.bit` (`low_xfWidth`, `low_xfBits`).

The proofs follow `CombViewThm.lean` (`inst_leaf`, `inst_rd`, `site_desc`): where lane M proves
that the instantiated expression READS only the promised windows (`RdOK`), this file proves what it
IS, which the equations need.
-/

namespace LeanModels.Sv
namespace CombEq
open CombView

/-! ## Recognizer inversions -/

theorem rdsLeaf_cases {ds : List DeclT} {e : PExpr} {rs : List Acc}
    (h : rdsLeaf? ds e = .ok rs) : ∃ a, leafRd? ds e = .ok a ∧ rs = [a] := by
  unfold rdsLeaf? at h
  rcases hl : leafRd? ds e with m | a
  · simp [hl] at h
  · simp only [hl, Except.ok.injEq] at h
    exact ⟨a, rfl, h.symm⟩

theorem partRd?_of_ne {ds : List DeclT} {p : PExpr} (hp : ∀ v, p ≠ .lit v) :
    partRd? ds p = rdsLeaf? ds p := by
  cases p <;> first | rfl | exact absurd rfl (hp _)

theorem partsT_lit (v : LVec) (ps : List PExpr) (as : List Acc) :
    partsT (.lit v :: ps) as = .lit v :: partsT ps as := rfl

theorem partsT_of_ne {p : PExpr} (hp : ∀ v, p ≠ .lit v) (ps : List PExpr) (as : List Acc) :
    partsT (p :: ps) as = .rd (as.headD (.whole "")) :: partsT ps (as.drop 1) := by
  cases p <;> first | rfl | exact absurd rfl (hp _)

theorem skRhs_of_ne {v : PExpr} (h1 : ∀ b, v ≠ .fill b) (h2 : ∀ ps, v ≠ .concat ps)
    (as : List Acc) : skRhs v as = skT v as := by
  cases v <;> first | rfl | exact absurd rfl (h1 _) | exact absurd rfl (h2 _)

theorem rhsRds?_of_ne {ds : List DeclT} {v : PExpr} (h1 : ∀ b, v ≠ .fill b) :
    rhsRds? ds v = rdsOf? ds v := by
  cases v <;> first | rfl | exact absurd rfl (h1 _)

theorem fragOk_of_ne {v : PExpr} (h1 : ∀ b, v ≠ .fill b) (h2 : ∀ ps, v ≠ .concat ps) :
    fragOk v = fragG v := by
  cases v <;> first | rfl | exact absurd rfl (h1 _) | exact absurd rfl (h2 _)

/-! ## One access leaf -/

section leaf
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- **An access leaf instantiates to the slice it promises**, and has the promised self-width. -/
theorem leaf_eq (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a) :
    selfWidth2 E elems e = some (a.win σ dw).2.2 ∧ (∀ ctx, instExpr2 E elems ctx e = accExpr σ a) ∧
      rigidExpr e = true := by
  obtain ⟨hdec, hgeo, hns⟩ := ha
  have hagx : ∀ x ∈ a.affs, ∀ n ∈ x.names, E.vals.lookup n = some (σ n) :=
    fun x hx n hn => C.agree n (hns x hx n hn)
  cases e with
  | ident n =>
      simp only [leafRd?, Except.ok.injEq] at h
      subst h
      refine ⟨?_, fun ctx => by simp [accExpr], rfl⟩
      have h1 := hdw n (by simpa [Acc.name] using hdec)
      rw [selfWidth2_ident, C.widths n, h1]
      rfl
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
            refine ⟨?_, fun ctx => ?_, rfl⟩
            · rw [selfWidth2_bitSel_ident, hel']; rfl
            · rw [instExpr2_bitSel_ident ctx hel' hev hnn]
              simp [accExpr, Acc.lo, Acc.wid]
      | _ => simp [leafRd?] at h
  | arrayElem n is =>
      simp only [leafRd?] at h
      rcases elemAcc?_cases h with ⟨i, x, rfl, hx, rfl⟩ | ⟨i, x, w, rfl, hx, rfl⟩ |
        ⟨i, j, x, y, w, rfl, hx, hy, rfl⟩
      · obtain ⟨m, hdg, hx0, hx1⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
        have hwin := arrayElemWindow_1d_in hd hev hx0 hx1
        refine ⟨?_, fun ctx => ?_, rfl⟩
        · rw [selfWidth2_arrayElem_of hwin]; rfl
        · rw [instExpr2_arrayElem, arrayElemRead_of_inRange hwin]
          simp [accExpr, Acc.lo, Acc.wid]
      · obtain ⟨m1, m2, hdg, hm2, hw, hx0, hx1⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
        have hwin := arrayElemWindow_row hd hm2 hev hx0 hx1
        have hrow := rmN_row_toNat (W := m2 + 1) (i := x.eval σ) (by omega) hx0
        refine ⟨?_, fun ctx => ?_, rfl⟩
        · rw [selfWidth2_arrayElem_of hwin]; simp [Acc.win, Acc.wid, hw]
        · rw [instExpr2_arrayElem, arrayElemRead_of_inRange hwin]
          simp [accExpr, Acc.lo, Acc.wid, hw, hrow]
      · obtain ⟨m1, m2, hdg, hw, hx0, hx1, hy0, hy1⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, hevi⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
        obtain ⟨-, hevj⟩ := affOf?_sound j y hy (hagx y (by simp [Acc.affs]))
        have hwin := arrayElemWindow_cell2 hd hevi hx0 hx1 hevj hy0 hy1
        have hcell := rmN_eq_toNat (W := m2 + 1) (i := x.eval σ) (j := y.eval σ) (by omega) hx0 hy0
        refine ⟨?_, fun ctx => ?_, rfl⟩
        · rw [selfWidth2_arrayElem_of hwin]; rfl
        · rw [instExpr2_arrayElem, arrayElemRead_of_inRange hwin]
          simp [accExpr, Acc.lo, Acc.wid, hw, hcell]
  | arrayPart n is mode hi lo =>
      simp only [leafRd?] at h
      obtain ⟨rfl, hc⟩ := partAcc?_cases h
      rcases hc with ⟨x, y, rfl, hx, hy, rfl⟩ | ⟨i, r, x, y, w, rfl, hr, hx, hy, rfl⟩
      · obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, heh⟩ := affOf?_sound hi x hx (hagx x (by simp [Acc.affs]))
        obtain ⟨-, hel⟩ := affOf?_sound lo y hy (hagx y (by simp [Acc.affs]))
        have hg := arrayPartGeom_part1 hd (by omega) heh hel hyx
        refine ⟨?_, fun ctx => ?_, rfl⟩
        · rw [selfWidth2_arrayPart_of hg]; simp [Acc.win, Acc.wid]
        · rw [instExpr2_arrayPart _ (dynPartPlan_of_geom hg),
            arrayPartRead_part1 hd (by omega) heh hel hy0 hyx hxm]
          simp [accExpr, Acc.lo, Acc.wid]
      · obtain ⟨m1, m2, hdg, hw, hr0, hr1, hy0, hyx, hxm⟩ := hgeo
        have hd := C.dims n _ hdg
        obtain ⟨-, hei⟩ := affOf?_sound i r hr (hagx r (by simp [Acc.affs]))
        obtain ⟨-, heh⟩ := affOf?_sound hi x hx (hagx x (by simp [Acc.affs]))
        obtain ⟨-, hel⟩ := affOf?_sound lo y hy (hagx y (by simp [Acc.affs]))
        have hg := arrayPartGeom_part2 hd (by omega) hei hr0 hr1 heh hel hyx
        have hcell := rmN_eq_toNat (W := m2 + 1) (i := r.eval σ) (j := y.eval σ) (by omega) hr0 hy0
        refine ⟨?_, fun ctx => ?_, rfl⟩
        · rw [selfWidth2_arrayPart_of hg]; simp [Acc.win, Acc.wid]
        · rw [instExpr2_arrayPart _ (dynPartPlan_of_geom hg),
            arrayPartRead_part2 hd hei hr0 hr1 heh hel hy0 hyx hxm]
          simp [accExpr, Acc.lo, Acc.wid, hw, hcell]
  | _ => simp [leafRd?] at h

/-- A leaf operand of the right width is not resized: `fitExpr2` is the slice. -/
theorem leaf_fit (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a)
    (ha : AccOK σ DW DG EW ns a) {tw : Nat} (hw : (a.win σ dw).2.2 = tw) :
    fitExpr2 E elems (some tw) e = accExpr σ a := by
  obtain ⟨hsw, hin, hrig⟩ := leaf_eq C hdw h ha
  rw [fitExpr2_of_rigid_eq hrig (by rw [hsw, hw]), hin]

/-! ## Gate trees -/

theorem gate_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ∀ tw, (skT v rs).WidthOk σ dw tw →
        fitExpr2 E elems (some tw) v = (skT v rs).low σ tw
  | .lit lv, rs, h, _, _, tw, hw => by
      simp only [rdsOf?, Except.ok.injEq] at h
      subst h
      simp only [skT, Sk.WidthOk] at hw
      rw [fitExpr2_lit, if_pos hw]
      simp [skT, Sk.low]
  | .binary op l r, rs, h, hf, hacc, tw, hw => by
      simp only [fragG, Bool.and_eq_true] at hf
      simp only [rdsOf?] at h
      rcases hg : gateOf op with _ | b
      · simp [hg] at h
      · rcases hl : rdsOf? ds l with e1 | ra
        · simp [hg, hl] at h
        · rcases hr : rdsOf? ds r with e2 | rb
          · simp [hg, hl, hr] at h
          · simp only [hg, hl, hr, Except.ok.injEq] at h
            subst h
            obtain ⟨rfl, hb⟩ := gateOf_cases hg
            have hla := rdsOf?_len l ra hl hf.1
            have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
            have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
            have ihl := gate_shape C hdw l ra hl hf.1
              (fun a ha => hacc a (List.mem_append_left _ ha)) tw
            have ihr := gate_shape C hdw r rb hr hf.2
              (fun a ha => hacc a (List.mem_append_right _ ha)) tw
            rcases hb with rfl | rfl | rfl <;>
              simp only [skT, hg, e1, e2, mkGate, Sk.WidthOk] at hw ⊢ <;>
              simp only [fitExpr2_binary, instExpr2_and, instExpr2_or, instExpr2_xor, Sk.low,
                Gate.op, ihl hw.1, ihr hw.2]
  | .ident n, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk, Sk.low] at hw ⊢
      exact leaf_fit C hdw hl (hacc a (by simp)) hw
  | .bitSel b i, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk, Sk.low] at hw ⊢
      exact leaf_fit C hdw hl (hacc a (by simp)) hw
  | .arrayElem n is, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk, Sk.low] at hw ⊢
      exact leaf_fit C hdw hl (hacc a (by simp)) hw
  | .arrayPart n is m a b, rs, h, _, hacc, tw, hw => by
      obtain ⟨a', hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk, Sk.low] at hw ⊢
      exact leaf_fit C hdw hl (hacc a' (by simp)) hw
  | .concat _, _, _, hf, _, _, _ => by simp [fragG] at hf
  | .fill _, _, _, hf, _, _, _ => by simp [fragG] at hf
  | .paramRef .., rs, h, _, _, _, _ | .genvarRef .., rs, h, _, _, _, _
  | .enumRef .., rs, h, _, _, _, _
  | .int .., rs, h, _, _, _, _ | .unary .., rs, h, _, _, _, _ | .ternary .., rs, h, _, _, _, _
  | .resize .., rs, h, _, _, _, _ | .signedResize .., rs, h, _, _, _, _
  | .squash2 .., rs, h, _, _, _, _
  | .sysCall .., rs, h, _, _, _, _ | .partSel .., rs, h, _, _, _, _ | .repl .., rs, h, _, _, _, _
  | .reduce .., rs, h, _, _, _, _ | .cast .., rs, h, _, _, _, _
  | .unsupported .., rs, h, _, _, _, _ => by
      simp [rdsOf?, rdsLeaf?, leafRd?] at h

/-! ## Concatenations -/

theorem parts_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRd? ds ps = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) →
      selfWidthSum2 E elems ps = some ((partsT ps rs).map (Part.wid σ dw)).sum ∧
        instParts2 E elems ps = (partsT ps rs).map (Part.expr σ)
  | [], rs, h, _ => by
      simp only [partsRd?, Except.ok.injEq] at h
      subst h
      simp [partsT, selfWidthSum2_nil, instParts2_nil]
  | p :: ps, rs, h, hacc => by
      simp only [partsRd?] at h
      rcases hp : partRd? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRd? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          by_cases hpl : ∃ v, p = .lit v
          · obtain ⟨v, rfl⟩ := hpl
            have hra : ra = [] := by simpa [partRd?] using hp.symm
            subst hra
            simp only [List.nil_append] at hacc ⊢
            obtain ⟨ih1, ih2⟩ := parts_shape C hdw ps rb hq hacc
            rw [partsT_lit]
            refine ⟨?_, ?_⟩
            · simp only [List.map_cons, List.sum_cons, Part.wid]
              exact selfWidthSum2_cons_of (by simp) ih1
            · simp only [instParts2_cons, List.map_cons, Part.expr, selfWidth2_lit, instExpr2_lit]
              rw [ih2]
          · have hnl : ∀ v, p ≠ .lit v := fun v h => hpl ⟨v, h⟩
            rw [partRd?_of_ne hnl] at hp
            obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
            have hA : AccOK σ DW DG EW ns a := hacc a (by simp)
            obtain ⟨ih1, ih2⟩ := parts_shape C hdw ps rb hq
              (fun x hx => hacc x (List.mem_append_right _ hx))
            obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl hA
            have e1 : partsT (p :: ps) ([a] ++ rb) = .rd a :: partsT ps rb := by
              rw [partsT_of_ne hnl]; rfl
            rw [e1]
            refine ⟨?_, ?_⟩
            · simp only [List.map_cons, List.sum_cons, Part.wid]
              exact selfWidthSum2_cons_of hsw ih1
            · simp only [instParts2_cons, List.map_cons, Part.expr, hsw, hin]
              rw [ih2]

/-! ## A whole right-hand side -/

theorem rhs_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {v : PExpr}
    {rs : List Acc} (h : rhsRds? ds v = .ok rs) (hf : fragOk v = true)
    (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) {tw : Nat} (hw : (skRhs v rs).WidthOk σ dw tw) :
    fitExpr2 E elems (some tw) v = (skRhs v rs).low σ tw := by
  by_cases hfill : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hfill
    rw [fitExpr2_of_not_rigid tw rfl]
    simp [instExpr2, skRhs, Sk.low]
  by_cases hcat : ∃ ps, v = .concat ps
  · obtain ⟨ps, rfl⟩ := hcat
    have h' : partsRd? ds ps = .ok rs := by simpa [rhsRds?, rdsOf?] using h
    obtain ⟨h1, h2⟩ := parts_shape C hdw ps rs h' hacc
    simp only [skRhs, Sk.WidthOk] at hw
    rw [fitExpr2_concat h1, if_pos hw]
    simp only [skRhs, Sk.low, h2]
  · have hn1 : ∀ b, v ≠ .fill b := fun b h => hfill ⟨b, h⟩
    have hn2 : ∀ ps, v ≠ .concat ps := fun ps h => hcat ⟨ps, h⟩
    rw [rhsRds?_of_ne hn1] at h
    rw [fragOk_of_ne hn1 hn2] at hf
    rw [skRhs_of_ne hn1 hn2] at hw ⊢
    exact gate_shape C hdw v rs h hf hacc tw hw

end leaf

/-! ## Targets with their exact widths -/

section lhs
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- `instLhs_acc` with the context width pinned: the width of the target window. -/
theorem instLhs_acc_w (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {l : PLhs} {a : Acc}
    (h : tgtOf? ds l = .ok a) (ha : AccOK σ DW DG EW ns a) :
    instLhs2 E elems l = .ok (a.lhs σ, (a.win σ dw).2.2) := by
  obtain ⟨hdec, hgeo, hns⟩ := ha
  have hagx : ∀ x ∈ a.affs, ∀ n ∈ x.names, E.vals.lookup n = some (σ n) :=
    fun x hx n hn => C.agree n (hns x hx n hn)
  rcases tgtOf?_cases h with ⟨n, rfl, rfl⟩ | ⟨n, i, x, rfl, hx, rfl⟩ | ⟨n, is, rfl, he⟩ |
    ⟨n, is, mode, hi, lo, rfl, hp⟩
  · have hW : E.widths.lookup n = some (dw n) := by
      rw [C.widths n]; exact hdw n (by simpa [Acc.name] using hdec)
    rw [instLhs2_ident hW]; rfl
  · obtain ⟨hnn, hel⟩ := hgeo
    have hel' : elems.lookup n = some 1 := C.elems n hel
    obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
    rw [instLhs2_bitSel hel' hev hnn]
    simp [Acc.lhs, Acc.lo, Acc.win]
  · rw [instLhs2_arrayElem]
    rcases elemAcc?_cases he with ⟨i, x, rfl, hx, rfl⟩ | ⟨i, x, w, rfl, hx, rfl⟩ |
      ⟨i, j, x, y, w, rfl, hx, hy, rfl⟩
    · obtain ⟨m, hdg, hx0, hx1⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      rw [arrayElemTarget_of_inRange (arrayElemWindow_1d_in hd hev hx0 hx1)]
      simp [Acc.lhs, Acc.lo, Acc.win]
    · obtain ⟨m1, m2, hdg, hm2, hw, hx0, hx1⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      have hrow := rmN_row_toNat (W := m2 + 1) (i := x.eval σ) (by omega) hx0
      rw [arrayElemTarget_of_inRange (arrayElemWindow_row hd hm2 hev hx0 hx1)]
      simp [Acc.lhs, Acc.lo, Acc.wid, Acc.win, hw, hrow]
    · obtain ⟨m1, m2, hdg, hw, hx0, hx1, hy0, hy1⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, hevi⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      obtain ⟨-, hevj⟩ := affOf?_sound j y hy (hagx y (by simp [Acc.affs]))
      have hcell := rmN_eq_toNat (W := m2 + 1) (i := x.eval σ) (j := y.eval σ) (by omega) hx0 hy0
      rw [arrayElemTarget_of_inRange (arrayElemWindow_cell2 hd hevi hx0 hx1 hevj hy0 hy1)]
      simp [Acc.lhs, Acc.lo, Acc.win, hw, hcell]
  · rw [instLhs2_arrayPart]
    obtain ⟨rfl, hc⟩ := partAcc?_cases hp
    rcases hc with ⟨x, y, rfl, hx, hy, rfl⟩ | ⟨i, r, x, y, w, rfl, hr, hx, hy, rfl⟩
    · obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, heh⟩ := affOf?_sound hi x hx (hagx x (by simp [Acc.affs]))
      obtain ⟨-, hel⟩ := affOf?_sound lo y hy (hagx y (by simp [Acc.affs]))
      rw [arrayPartTarget_part1 hd (by omega) heh hel hy0 hyx hxm]
      simp [Acc.lhs, Acc.lo, Acc.wid, Acc.win]
    · obtain ⟨m1, m2, hdg, hw, hr0, hr1, hy0, hyx, hxm⟩ := hgeo
      have hd := C.dims n _ hdg
      obtain ⟨-, hei⟩ := affOf?_sound i r hr (hagx r (by simp [Acc.affs]))
      obtain ⟨-, heh⟩ := affOf?_sound hi x hx (hagx x (by simp [Acc.affs]))
      obtain ⟨-, hel⟩ := affOf?_sound lo y hy (hagx y (by simp [Acc.affs]))
      have hcell := rmN_eq_toNat (W := m2 + 1) (i := r.eval σ) (j := y.eval σ) (by omega) hr0 hy0
      rw [arrayPartTarget_part2 hd hei hr0 hr1 heh hel hy0 hyx hxm]
      simp [Acc.lhs, Acc.lo, Acc.wid, Acc.win, hw, hcell]

/-- **A site instantiates to the promised assign with the promised right-hand side.** -/
theorem proc_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite} (hs : siteOf? ds pos p = .ok st)
    (hso : ∀ a ∈ st.tgt :: st.rds, AccOK σ DW DG EW ns a) (hf : fragOk (rhsOf p) = true)
    (hw : (skRhs (rhsOf p) st.rds).WidthOk σ dw (st.tgt.win σ dw).2.2) :
    instProcess2 E elems p =
      .assign (st.tgt.lhs σ) ((skRhs (rhsOf p) st.rds).low σ (st.tgt.win σ dw).2.2) := by
  have hrdacc : ∀ rds, rds = st.rds → ∀ a ∈ rds, AccOK σ DW DG EW ns a := by
    rintro rds rfl a ha
    exact hso a (List.mem_cons_of_mem _ ha)
  rcases siteOf?_cases hs with ⟨t, v, rds, rfl, hrds, rfl⟩ | ⟨l, v, tg, rds, rfl, htg, hrds, rfl⟩
  · have hdt : (DW t).isSome = true := (hso _ (List.mem_cons_self ..)).1
    have hW : E.widths.lookup t = some (dw t) := by
      rw [C.widths t]; exact hdw t hdt
    rw [instProcess2_assign v hW]
    simp only [rhsOf] at hf hw ⊢
    have := rhs_shape C hdw hrds hf (hrdacc _ rfl) hw
    simpa [Acc.win, Acc.lhs] using this
  · rw [instProcess2_assignL v (instLhs_acc_w C hdw htg (hso _ (List.mem_cons_self ..)))]
    simp only [rhsOf] at hf hw ⊢
    rw [rhs_shape C hdw hrds hf (hrdacc _ rfl) hw]

end lhs

/-! ## The lowered expression is in the x-free fragment, with `Sk.bit` as its Boolean value -/

/-- The facts about the design `m` the lowered leaves need: a declared, non-empty, in-range window. -/
def LeafOk (m : Design2) (σ : String → Int) (dw : String → Nat) (a : Acc) : Prop :=
  m.declWidth a.name = some (dw a.name) ∧
    (a.win σ dw).2.1 + (a.win σ dw).2.2 ≤ dw a.name ∧ 0 < (a.win σ dw).2.2

theorem expr_xfWidth {m : Design2} {σ : String → Int} {dw : String → Nat} {a : Acc}
    (h : LeafOk m σ dw a) : (accExpr σ a).xfWidth m = some (a.win σ dw).2.2 := by
  obtain ⟨hD, hr, hp⟩ := h
  cases a <;> simp_all [accExpr, Acc.win, Acc.wid, Acc.name, Expr2.xfWidth, LeafOk]

theorem expr_xfBits {m : Design2} {σ : String → Int} (a : Acc) (env : String → Nat → Bool)
    (k : Nat) : (accExpr σ a).xfBits m env k = accBit σ env a k := by
  cases a <;> simp [accExpr, accBit, Acc.name, Acc.lo, Expr2.xfBits]

theorem partLeaves_cons_rd (a : Acc) (ps : List Part) :
    partLeaves (.rd a :: ps) = a :: partLeaves ps := rfl

/-- A concatenation of literals and accesses: its width and its bits. -/
theorem cat_low {m : Design2} {σ : String → Int} {dw : String → Nat}
    (env : String → Nat → Bool) :
    ∀ (ps : List Part), partKnown ps = true → (∀ a ∈ partLeaves ps, LeafOk m σ dw a) →
      Expr2.xfWidthSum m (ps.map (Part.expr σ)) = some (ps.map (Part.wid σ dw)).sum ∧
      ∀ k, Expr2.catBits m env (ps.map (Part.expr σ)) k = catBit σ dw env ps k
  | [], _, _ => by simp [Expr2.xfWidthSum, Expr2.catBits, catBit]
  | .lit v :: ps, hk, hL => by
      simp only [partKnown, Bool.and_eq_true] at hk
      obtain ⟨ih1, ih2⟩ := cat_low env ps hk.2 (by simpa [partLeaves] using hL)
      refine ⟨?_, fun k => ?_⟩
      · simp [Expr2.xfWidthSum, Part.expr, Part.wid, Expr2.xfWidth, hk.1, ih1, Nat.add_comm]
      · simp [Expr2.catBits, catBit, Part.expr, Part.wid, ih1, ih2, Expr2.xfBits, Part.bit]
  | .rd a :: ps, hk, hL => by
      simp only [partKnown] at hk
      have hA : LeafOk m σ dw a := hL a (by simp [partLeaves])
      obtain ⟨ih1, ih2⟩ := cat_low env ps hk (fun x hx => hL x (by simp [partLeaves, hx]))
      refine ⟨?_, fun k => ?_⟩
      · simp [Expr2.xfWidthSum, Part.expr, Part.wid, expr_xfWidth hA, ih1, Nat.add_comm]
      · simp [Expr2.catBits, catBit, Part.expr, Part.wid, ih1, ih2, expr_xfBits, Part.bit]

/-- **The lowered right-hand side is in the x-free fragment at the target width.** -/
theorem low_xfWidth {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat} :
    ∀ (sk : Sk), sk.knownB = true → sk.WidthOk σ dw tw → (∀ a ∈ sk.leaves, LeafOk m σ dw a) →
      (sk.low σ tw).xfWidth m = some tw
  | .lit v, hk, hw, _ => by
      simp only [Sk.knownB] at hk
      simp only [Sk.WidthOk] at hw
      simp [Sk.low, Expr2.xfWidth, hk, hw]
  | .rd a, _, hw, hL => by
      simp only [Sk.WidthOk] at hw
      rw [Sk.low, expr_xfWidth (hL a (by simp [Sk.leaves])), hw]
  | .gate g l r, hk, hw, hL => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      simp only [Sk.WidthOk] at hw
      have h1 := low_xfWidth l hk.1 hw.1 (fun a ha => hL a (by simp [Sk.leaves, ha]))
      have h2 := low_xfWidth r hk.2 hw.2 (fun a ha => hL a (by simp [Sk.leaves, ha]))
      cases g <;> simp [Sk.low, Gate.op, Expr2.xfWidth, h1, h2, XF.same]
  | .cat ps, hk, hw, hL => by
      simp only [Sk.WidthOk] at hw
      obtain ⟨h1, -⟩ := cat_low (m := m) (σ := σ) (dw := dw) (fun _ _ => false) ps hk hL
      simp [Sk.low, Expr2.xfWidth, h1, hw]
  | .fill b, hk, hw, _ => by
      simp only [Sk.knownB] at hk
      have hknown : (LVec.replicate tw b).knownB = true := by
        simp [LVec.knownB, LVec.replicate, hk]
      simp only [Sk.low, Expr2.xfWidth, hknown, if_true]
      simp [LVec.width, LVec.replicate]

/-- **… and its `Expr2.xfBits` is the skeleton's Boolean reading** (below the target width). -/
theorem low_xfBits {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat}
    (env : String → Nat → Bool) :
    ∀ (sk : Sk), sk.knownB = true → sk.WidthOk σ dw tw → (∀ a ∈ sk.leaves, LeafOk m σ dw a) →
      ∀ k, k < tw → (sk.low σ tw).xfBits m env k = sk.bit σ dw env k
  | .lit v, _, _, _, k, _ => by simp [Sk.low, Sk.bit, Expr2.xfBits]
  | .rd a, _, _, _, k, _ => by simp [Sk.low, Sk.bit, expr_xfBits]
  | .gate g l r, hk, hw, hL, k, hk' => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      simp only [Sk.WidthOk] at hw
      have h1 := low_xfBits env l hk.1 hw.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) k hk'
      have h2 := low_xfBits env r hk.2 hw.2 (fun a ha => hL a (by simp [Sk.leaves, ha])) k hk'
      cases g <;> simp [Sk.low, Sk.bit, Gate.op, Expr2.xfBits, h1, h2]
  | .cat ps, hk, hw, hL, k, _ => by
      obtain ⟨-, h2⟩ := cat_low (m := m) (σ := σ) (dw := dw) env ps hk hL
      simp [Sk.low, Sk.bit, Expr2.xfBits, h2]
  | .fill b, hk, hw, _, k, hk' => by
      simp [Sk.low, Sk.bit, Expr2.xfBits, LVec.boolAt, LVec.replicate, hk']

/-! ## Axiom pins -/

/-- info: 'LeanModels.Sv.CombEq.proc_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proc_shape

/-- info: 'LeanModels.Sv.CombEq.low_xfWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_xfWidth

/-- info: 'LeanModels.Sv.CombEq.low_xfBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_xfBits

end CombEq
end LeanModels.Sv
