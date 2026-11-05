import LeanModels.Sv.CombEqBase

/-!
# `sv_equations`, stage 2: what the instantiated right-hand side is, and its Boolean value

`CombEqBase.lean` defines the skeleton `Sk` of a right-hand side and its lowering `Sk.low`. Here the
lowering is proved to BE what `instantiate2` builds (`proc_shapeC`), for a site whose operands are
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

theorem skRhs_of_ne {v : PExpr} (h1 : ∀ b, v ≠ .fill b) (h2 : ∀ ps, v ≠ .concat ps)
    (as : List Acc) : skRhs v as = skT v as := by
  cases v <;> first | rfl | exact absurd rfl (h1 _) | exact absurd rfl (h2 _)

theorem rhsRds?_of_ne {ds : List DeclT} {v : PExpr} (h1 : ∀ b, v ≠ .fill b) :
    rhsRds? ds v = rdsOfW? ds v := by
  cases v <;> first | rfl | exact absurd rfl (h1 _)

theorem fragOk_of_ne {v : PExpr} (h1 : ∀ b, v ≠ .fill b) (h2 : ∀ ps, v ≠ .concat ps) :
    fragOk v = fragW v := by
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
          · simp only [hx] at h
            rcases bitAcc?_cases ds n x with hb | ⟨w, hb⟩ <;> rw [hb] at h <;>
              simp only [Except.ok.injEq] at h <;> subst h
            · obtain ⟨hnn, hel⟩ := hgeo
              have hel' : elems.lookup n = some 1 := C.elems n hel
              obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
              refine ⟨?_, fun ctx => ?_, rfl⟩
              · rw [selfWidth2_bitSel_ident, hel']; rfl
              · rw [instExpr2_bitSel_ident ctx hel' hev hnn]
                simp [accExpr, Acc.lo, Acc.wid]
            · -- a legacy select of a row of a two-dimensional declaration
              obtain ⟨m1, m2, hdg, hm2, hw, hx0, hx1⟩ := hgeo
              have hel' := ctxElemsRow C hdg hm2
              obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
              refine ⟨?_, fun ctx => ?_, rfl⟩
              · rw [selfWidth2_bitSel_ident, hel']; simp [Acc.win, Acc.wid, hw]
              · rw [instExpr2_bitSel_ident ctx hel' hev hx0]
                simp [accExpr, Acc.lo, Acc.wid, rmN, hw]
      | _ => simp [leafRd?] at h
  | partSel b msb lsb =>
      cases b with
      | ident n =>
          simp only [leafRd?] at h
          obtain ⟨-, hc⟩ := partAcc?_cases h
          rcases hc with ⟨x, y, -, hx, hy, rfl⟩ | ⟨i, r, x, y, w, hnil, -⟩
          · -- a legacy part select of a one-dimensional declaration
            obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hgeo
            refine ⟨?_, fun ctx => ?_, rfl⟩
            · rw [selfWidth_partSel C hdg hx hy hagx hy0 hyx]; simp [Acc.win, Acc.wid]
            · rw [inst_partSel C hdg hx hy hagx hy0 hyx ctx]
              simp [accExpr, Acc.lo, Acc.wid]
          · exact absurd hnil (by simp)
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

/-! ## Expressions of the fragment -/

/-- `rigidMax2` of an access leaf is its self-determined width. -/
theorem rm_leaf {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a) :
    rigidMax2 E elems e = selfWidth2 E elems e := by
  cases e <;> simp [leafRd?, rigidMax2] at h ⊢

/-- **The shape of an expression of the fragment** (WP-G S2; `cond_shape` and `skT_selfWidth` are
its corollaries): for an accepted expression `v` whose skeleton fits width `w`, the self-determined width and
`rigidMax2` are `w`, and instantiation at no context, at `w`, and the fit to `w` are all `Sk.low`. The operands of
the self-determined operators are lowered at their own width (`Sk.SelfOk`, `Sk.low_irrel`). -/
theorem skT_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v = .ok rs → fragG v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ∀ tw, (skT v rs).WidthOk σ dw tw →
        selfWidth2 E elems v = some tw ∧ rigidMax2 E elems v = some tw ∧
        instExpr2 E elems none v = (skT v rs).low σ dw tw ∧
        instExpr2 E elems (some tw) v = (skT v rs).low σ dw tw ∧
        fitExpr2 E elems (some tw) v = (skT v rs).low σ dw tw
  | .lit lv, rs, h, _, _, tw, hw => by
      simp only [rdsOf?, Except.ok.injEq] at h
      subst h
      simp only [skT, Sk.WidthOk] at hw
      refine ⟨by simp [hw], by simp [rigidMax2, hw], by simp [skT, Sk.low, instExpr2],
        by simp [skT, Sk.low, instExpr2], ?_⟩
      rw [fitExpr2_lit, if_pos hw]
      simp [skT, Sk.low]
  | .binary op l r, rs, h, hf, hacc, tw, hw => by
      simp only [fragG, Bool.and_eq_true] at hf
      obtain ⟨hb, ra, rb, hl, hr, rfl⟩ := rdsOf?_binary h
      have hla := rdsOf?_len l ra hl hf.1
      have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
      have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
      have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
      have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
      rcases hg : gateOf op with _ | b
      · -- `&&`, `||`, `==`, `!=`: 1 bit, self-determined operands
        rcases binOk_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp [gateOf] at hg
        · simp [gateOf] at hg
        · simp [gateOf] at hg
        · have hsk : skT (.binary .land l r) (ra ++ rb) = .land (skT l ra) (skT r rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr⟩ := hw
          obtain ⟨Sl, -, -, I1l, -⟩ := skT_shape C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, I1r, -⟩ := skT_shape C hdw r rb hr hf.2 hacr _ (Sk.selfOk_widthOk σ dw _ hsr)
          have key : ∀ ctx, instExpr2 E elems ctx (.binary .land l r) =
              Sk.low σ dw 1 (.land (skT l ra) (skT r rb)) := by
            intro ctx
            rw [ie_land, Sl, Sr, I1l, I1r, Sk.low_irrel σ dw (skT l ra) hsl _ 0,
              Sk.low_irrel σ dw (skT r rb) hsr _ 0]
            rfl
          exact ⟨sw_land l r, rm_land l r, key none, key _, by rw [fitExpr2_binary]; exact key _⟩
        · have hsk : skT (.binary .lor l r) (ra ++ rb) = .lor (skT l ra) (skT r rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr⟩ := hw
          obtain ⟨Sl, -, -, I1l, -⟩ := skT_shape C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, I1r, -⟩ := skT_shape C hdw r rb hr hf.2 hacr _ (Sk.selfOk_widthOk σ dw _ hsr)
          have key : ∀ ctx, instExpr2 E elems ctx (.binary .lor l r) =
              Sk.low σ dw 1 (.lor (skT l ra) (skT r rb)) := by
            intro ctx
            rw [ie_lor, Sl, Sr, I1l, I1r, Sk.low_irrel σ dw (skT l ra) hsl _ 0,
              Sk.low_irrel σ dw (skT r rb) hsr _ 0]
            rfl
          exact ⟨sw_lor l r, rm_lor l r, key none, key _, by rw [fitExpr2_binary]; exact key _⟩
        · have hsk : skT (.binary (.m0 .eq) l r) (ra ++ rb) = .cmp .eq (skT l ra) (skT r rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr, hwe⟩ := hw
          obtain ⟨Sl, -, -, -, Fl⟩ := skT_shape C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, -, Fr⟩ := skT_shape C hdw r rb hr hf.2 hacr _
            (Sk.selfOk_widthOk σ dw _ hsr)
          rw [← hwe] at Sr Fr
          have hm : max ((skT l ra).width σ dw) ((skT r rb).width σ dw) = (skT l ra).width σ dw := by
            rw [← hwe]; exact Nat.max_self _
          have key : ∀ ctx, instExpr2 E elems ctx (.binary (.m0 .eq) l r) =
              Sk.low σ dw 1 (.cmp .eq (skT l ra) (skT r rb)) := by
            intro ctx
            rw [ie_eq ctx _ l r Sl Sr, Fl, Fr]
            simp only [Sk.low, CmpOp.ex, hm]
          exact ⟨sw_eq l r, rm_eq l r, key none, key _, by rw [fitExpr2_binary]; exact key _⟩
        · have hsk : skT (.binary (.m0 .ne) l r) (ra ++ rb) = .cmp .ne (skT l ra) (skT r rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr, hwe⟩ := hw
          obtain ⟨Sl, -, -, -, Fl⟩ := skT_shape C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, -, Fr⟩ := skT_shape C hdw r rb hr hf.2 hacr _
            (Sk.selfOk_widthOk σ dw _ hsr)
          rw [← hwe] at Sr Fr
          have hm : max ((skT l ra).width σ dw) ((skT r rb).width σ dw) = (skT l ra).width σ dw := by
            rw [← hwe]; exact Nat.max_self _
          have key : ∀ ctx, instExpr2 E elems ctx (.binary (.m0 .ne) l r) =
              Sk.low σ dw 1 (.cmp .ne (skT l ra) (skT r rb)) := by
            intro ctx
            rw [ie_ne ctx _ l r Sl Sr, Fl, Fr]
            simp only [Sk.low, CmpOp.ex, hm]
          exact ⟨sw_ne l r, rm_ne l r, key none, key _, by rw [fitExpr2_binary]; exact key _⟩
      · -- a bitwise gate
        obtain ⟨rfl, hbb⟩ := gateOf_cases hg
        have ihl := skT_shape C hdw l ra hl hf.1 hacl tw
        have ihr := skT_shape C hdw r rb hr hf.2 hacr tw
        rcases hbb with rfl | rfl | rfl <;>
          (simp only [skT, hg, e1, e2, mkGate, Sk.WidthOk] at hw ⊢
           obtain ⟨Sl, Rl, I0l, I1l, Fl⟩ := ihl hw.1
           obtain ⟨Sr, Rr, I0r, I1r, Fr⟩ := ihr hw.2
           refine ⟨by simp [selfWidth2, Sl, Sr], by simp [rigidMax2, Rl, Rr],
             by simp [instExpr2, Sl, Sr, Fl, Fr, Sk.low, Gate.op],
             by simp only [instExpr2_and, instExpr2_or, instExpr2_xor, Sk.low, Gate.op, Fl, Fr],
             ?_⟩
           rw [fitExpr2_binary]
           simp only [instExpr2_and, instExpr2_or, instExpr2_xor, Sk.low, Gate.op, Fl, Fr])
  | .unary op a, rs, h, hf, hacc, tw, hw => by
      obtain ⟨hop, ha⟩ := rdsOf?_unary h
      simp only [fragG] at hf
      rcases hop with rfl | rfl
      · have hsk : skT (.unary (.m0 .bnot) a) rs = .bnot (skT a rs) := by simp [skT]
        rw [hsk] at hw ⊢
        simp only [Sk.WidthOk] at hw
        obtain ⟨Sa, Ra, I0a, I1a, Fa⟩ := skT_shape C hdw a rs ha hf hacc tw hw
        have hrm : (rigidMax2 E elems a).getD tw ≤ tw := by rw [Ra]; simp
        have I1 : instExpr2 E elems (some tw) (.unary (.m0 .bnot) a) = Sk.low σ dw tw (.bnot (skT a rs)) := by
          rw [ie_bnot_some tw a hrm, Fa]; rfl
        refine ⟨by rw [sw_bnot]; exact Sa, by rw [rm_bnot]; exact Ra, ?_, I1, ?_⟩
        · rw [ie_bnot_none, Sa, I1a]; rfl
        · rw [fitExpr2_of_not_rigid tw (rigidExpr_unary _ _)]; exact I1
      · have hsk : skT (.unary (.m0 .lnot) a) rs = .lnot (skT a rs) := by simp [skT]
        rw [hsk] at hw ⊢
        obtain ⟨rfl, hsa⟩ := hw
        obtain ⟨-, -, I0a, -, -⟩ := skT_shape C hdw a rs ha hf hacc _ (Sk.selfOk_widthOk σ dw _ hsa)
        have key : ∀ ctx, instExpr2 E elems ctx (.unary (.m0 .lnot) a) = Sk.low σ dw 1 (.lnot (skT a rs)) := by
          intro ctx
          rw [ie_lnot, I0a, Sk.low_irrel σ dw (skT a rs) hsa _ 0]
          rfl
        exact ⟨sw_lnot a, rm_lnot a, key none, key _, by rw [fitExpr2_of_not_rigid 1 (rigidExpr_unary _ _)]; exact key _⟩
  | .ternary c t f, rs, h, hf, hacc, tw, hw => by
      obtain ⟨rc, rt, rf, hc, ht, hfe, rfl⟩ := rdsOf?_ternary h
      simp only [fragG, Bool.and_eq_true] at hf
      have hc' := rdsOf?_len c rc hc hf.1.1
      have ht' := rdsOf?_len t rt ht hf.1.2
      have e1 : (rc ++ rt ++ rf).take (cnt c) = rc := by
        rw [List.append_assoc]; exact List.take_left' hc'
      have e2 : (rc ++ rt ++ rf).drop (cnt c) = rt ++ rf := by
        rw [List.append_assoc]; exact List.drop_left' hc'
      have e3 : (rt ++ rf).take (cnt t) = rt := List.take_left' ht'
      have e4 : (rt ++ rf).drop (cnt t) = rf := List.drop_left' ht'
      have hsk : skT (.ternary c t f) (rc ++ rt ++ rf) = .tern (skT c rc) (skT t rt) (skT f rf) := by
        simp only [skT, e1, e2, e3, e4]
      rw [hsk] at hw ⊢
      obtain ⟨hsc, hwc, hwt, hwf⟩ := hw
      have hc1 : (skT c rc).WidthOk σ dw 1 := by
        have := Sk.selfOk_widthOk σ dw _ hsc
        rwa [hwc] at this
      obtain ⟨-, -, I0c, -, -⟩ := skT_shape C hdw c rc hc hf.1.1
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_left _ hx))) 1 hc1
      obtain ⟨St, Rt, -, -, Ft⟩ := skT_shape C hdw t rt ht hf.1.2
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx))) tw hwt
      obtain ⟨Sf, Rf, -, -, Ff⟩ := skT_shape C hdw f rf hfe hf.2
        (fun x hx => hacc x (List.mem_append_right _ hx)) tw hwf
      have I1 : instExpr2 E elems (some tw) (.ternary c t f) =
          Sk.low σ dw tw (.tern (skT c rc) (skT t rt) (skT f rf)) := by
        rw [ie_ternary_some, I0c, Ft, Ff]
        simp only [Sk.low, Sk.low_irrel σ dw _ hsc 1 0]
      refine ⟨sw_ternary tw c t f St Sf, rm_ternary tw c t f Rt Rf, ?_, I1, ?_⟩
      · rw [ie_ternary_none tw c t f St Sf, I0c, Ft, Ff]
        simp only [Sk.low, Sk.low_irrel σ dw _ hsc 1 0]
      · rw [fitExpr2_of_not_rigid tw (rigidExpr_ternary _ _ _)]; exact I1
  | .reduce op a, rs, h, hf, hacc, tw, hw => by
      simp only [fragG] at hf
      have ha := rdsOf?_reduce h
      have hsk : skT (.reduce op a) rs = .red op (skT a rs) := by simp [skT]
      rw [hsk] at hw ⊢
      obtain ⟨rfl, hsa⟩ := hw
      obtain ⟨Sa, -, -, I1a, -⟩ := skT_shape C hdw a rs ha hf hacc _ (Sk.selfOk_widthOk σ dw _ hsa)
      have key : ∀ ctx, instExpr2 E elems ctx (.reduce op a) = Sk.low σ dw 1 (.red op (skT a rs)) := by
        intro ctx
        rw [ie_reduce, Sa, I1a, Sk.low_irrel σ dw (skT a rs) hsa _ 0]
        rfl
      exact ⟨sw_reduce op a, rm_reduce op a, key none, key _, by
        rw [fitExpr2_of_rigid_eq (rigidExpr_reduce op a) (sw_reduce op a)]; exact key _⟩
  | .ident n, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk, Sk.low] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨by rw [hsw, hw], by rw [rm_leaf hl, hsw, hw], hin none, hin _, leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .bitSel b i, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk, Sk.low] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨by rw [hsw, hw], by rw [rm_leaf hl, hsw, hw], hin none, hin _, leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .partSel b pm pl, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk, Sk.low] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨by rw [hsw, hw], by rw [rm_leaf hl, hsw, hw], hin none, hin _, leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .arrayElem n is, rs, h, _, hacc, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk, Sk.low] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨by rw [hsw, hw], by rw [rm_leaf hl, hsw, hw], hin none, hin _, leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .arrayPart n is m a b, rs, h, _, hacc, tw, hw => by
      obtain ⟨a', hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOf?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOk, Sk.low] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a' (by simp))
      exact ⟨by rw [hsw, hw], by rw [rm_leaf hl, hsw, hw], hin none, hin _, leaf_fit C hdw hl (hacc a' (by simp)) hw⟩
  | .concat _, _, _, hf, _, _, _ => by simp [fragG] at hf
  | .fill _, _, _, hf, _, _, _ => by simp [fragG] at hf
  | .paramRef .., rs, h, _, _, _, _ | .genvarRef .., rs, h, _, _, _, _
  | .enumRef .., rs, h, _, _, _, _
  | .int .., rs, h, _, _, _, _
  | .resize .., rs, h, _, _, _, _ | .signedResize .., rs, h, _, _, _, _
  | .squash2 .., rs, h, _, _, _, _
  | .sysCall .., rs, h, _, _, _, _ | .repl .., rs, h, _, _, _, _
  | .cast .., rs, h, _, _, _, _
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
              rw [partsT_of_ne hnl (rdsLeaf_ne_repl hp)]; rfl
            rw [e1]
            refine ⟨?_, ?_⟩
            · simp only [List.map_cons, List.sum_cons, Part.wid]
              exact selfWidthSum2_cons_of hsw ih1
            · simp only [instParts2_cons, List.map_cons, Part.expr, hsw, hin]
              rw [ih2]

/-! ## Replication (WP-B2 gate 4c) -/

theorem win_wid_of_ne_whole {σ : String → Int} {dw : String → Nat} {x : Acc} (hx : ∀ n, x ≠ .whole n) :
    (x.win σ dw).2.2 = Acc.wid σ x := by
  cases x <;> first | rfl | exact absurd rfl (hx _)

/-- **A replication of a literal or one access** (the operand is the one-part concatenation slang makes of the
braces): its self-width and its lowering are those of its `Part`. -/
theorem repl_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {c a : PExpr} {rs : List Acc}
    (h : repRd? ds c a = .ok rs) (hacc : ∀ x ∈ rs, AccOK σ DW DG EW ns x) (hco : ConstOK σ ns (.repl c a)) :
    (∃ v, a = .concat [.lit v] ∧ rs = [] ∧
        selfWidth2 E elems (.repl c a) = some ((Part.replit (repAff c) v).wid σ dw) ∧
        ∀ ctx, instExpr2 E elems ctx (.repl c a) = (Part.replit (repAff c) v).expr σ) ∨
    (∃ x e, (∀ v, e ≠ .lit v) ∧ a = .concat [e] ∧ rs = [x] ∧
        selfWidth2 E elems (.repl c a) = some ((Part.reprd (repAff c) x).wid σ dw) ∧
        ∀ ctx, instExpr2 E elems ctx (.repl c a) = (Part.reprd (repAff c) x).expr σ) := by
  obtain ⟨k, hk, harg⟩ := repRd?_cases h
  have hrc : repAff c = k := by simp [repAff, hk]
  rw [hrc]
  rcases repArgRd?_cases harg with ⟨v, rfl, rfl⟩ | ⟨e, rfl, hl, hnl, hnw⟩
  · left
    have hw : selfWidth2 E elems (.concat [.lit v]) = some v.width := by
      rw [selfWidth2_concat]
      simpa using selfWidthSum2_cons_of (env := E) (elems := elems) (p := .lit v) (ps := []) (a := v.width) (b := 0)
        (by simp) selfWidthSum2_nil
    refine ⟨v, rfl, rfl, ?_, fun ctx => ?_⟩
    · rw [selfWidth_repl C hk hco hw]; rfl
    · rw [inst_repl C hk hco ctx, hw]; simp [Part.expr]
  · right
    obtain ⟨x, hl', rfl⟩ := rdsLeaf_cases hl
    obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl' (hacc x (by simp))
    have hx : ∀ n, x ≠ .whole n := fun n hxn => hnw n (by rw [hxn])
    have hw : selfWidth2 E elems (.concat [e]) = some (x.win σ dw).2.2 := by
      rw [selfWidth2_concat]
      simpa using selfWidthSum2_cons_of (env := E) (elems := elems) (p := e) (ps := []) hsw selfWidthSum2_nil
    refine ⟨x, e, hnl, rfl, rfl, ?_, fun ctx => ?_⟩
    · rw [selfWidth_repl C hk hco hw, Part.wid, win_wid_of_ne_whole hx]
    · rw [inst_repl C hk hco ctx]
      simp only [instExpr2_concat, instParts2_cons, instParts2_nil, hin]
      rfl

/-- The parts of a word-level concatenation (literals, accesses, replications). -/
theorem parts_shapeW (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRdW? ds ps = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → PartsCO σ ns ps →
      selfWidthSum2 E elems ps = some ((partsT ps rs).map (Part.wid σ dw)).sum ∧
        instParts2 E elems ps = (partsT ps rs).map (Part.expr σ)
  | [], rs, h, _, _ => by
      simp only [partsRdW?, Except.ok.injEq] at h
      subst h
      simp [partsT, selfWidthSum2_nil, instParts2_nil]
  | p :: ps, rs, h, hacc, hco => by
      simp only [partsRdW?] at h
      rcases hp : partRdW? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRdW? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          obtain ⟨hco', hn, hc⟩ := partsCO_cons hco
          by_cases hpl : ∃ v, p = .lit v
          · obtain ⟨v, rfl⟩ := hpl
            have hra : ra = [] := by simpa [partRdW?] using hp.symm
            subst hra
            simp only [List.nil_append] at hacc ⊢
            obtain ⟨ih1, ih2⟩ := parts_shapeW C hdw ps rb hq hacc hco'
            rw [partsT_lit]
            refine ⟨?_, ?_⟩
            · simp only [List.map_cons, List.sum_cons, Part.wid]
              exact selfWidthSum2_cons_of (by simp) ih1
            · simp only [instParts2_cons, List.map_cons, Part.expr, selfWidth2_lit, instExpr2_lit]
              rw [ih2]
          · have hnl : ∀ v, p ≠ .lit v := fun v h => hpl ⟨v, h⟩
            by_cases hpr : ∃ c a, p = .repl c a
            · obtain ⟨c, a, rfl⟩ := hpr
              have hco1 : ConstOK σ ns (.repl c a) :=
                ⟨fun n hn' => hn n hn', fun k hk => hc k hk⟩
              rcases repl_shape C hdw hp (fun x hx => hacc x (List.mem_append_left _ hx)) hco1 with
                ⟨v, rfl, rfl, hS, hI⟩ | ⟨x, e, hnl', rfl, rfl, hS, hI⟩
              · simp only [List.nil_append] at hacc ⊢
                obtain ⟨ih1, ih2⟩ := parts_shapeW C hdw ps rb hq hacc hco'
                rw [partsT_repl_lit]
                refine ⟨?_, ?_⟩
                · simp only [List.map_cons, List.sum_cons]
                  exact selfWidthSum2_cons_of hS ih1
                · simp only [instParts2_cons, List.map_cons]
                  rw [hI, ih2]
              · obtain ⟨ih1, ih2⟩ := parts_shapeW C hdw ps rb hq
                  (fun y hy => hacc y (List.mem_append_right _ hy)) hco'
                have e1 : partsT (.repl c (.concat [e]) :: ps) ([x] ++ rb) = .reprd (repAff c) x :: partsT ps rb := by
                  rw [partsT_repl_ne c hnl']; rfl
                rw [e1]
                refine ⟨?_, ?_⟩
                · simp only [List.map_cons, List.sum_cons]
                  exact selfWidthSum2_cons_of hS ih1
                · simp only [instParts2_cons, List.map_cons]
                  rw [hI, ih2]
            · have hnr : ∀ c a, p ≠ .repl c a := fun c a h => hpr ⟨c, a, h⟩
              rw [partRdW?_of_ne hnl hnr] at hp
              obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
              have hA : AccOK σ DW DG EW ns a := hacc a (by simp)
              obtain ⟨ih1, ih2⟩ := parts_shapeW C hdw ps rb hq
                (fun x hx => hacc x (List.mem_append_right _ hx)) hco'
              obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl hA
              have e1 : partsT (p :: ps) ([a] ++ rb) = .rd a :: partsT ps rb := by
                rw [partsT_of_ne hnl hnr]; rfl
              rw [e1]
              refine ⟨?_, ?_⟩
              · simp only [List.map_cons, List.sum_cons, Part.wid]
                exact selfWidthSum2_cons_of hsw ih1
              · simp only [instParts2_cons, List.map_cons, Part.expr, hsw, hin]
                rw [ih2]

/-- The bundle `skT_shapeC` owes a replication, from the facts of its `Part`. -/
theorem rep_bundle {σ : String → Int} {E : IEnv} {elems : List (String × Nat)} {dw : String → Nat} {tw : Nat}
    {c a : PExpr} {p : Part}
    (hS : selfWidth2 E elems (.repl c a) = some (p.wid σ dw))
    (hI : ∀ ctx, instExpr2 E elems ctx (.repl c a) = p.expr σ) (hw : p.wid σ dw = tw) :
    selfWidth2 E elems (.repl c a) = some ((Sk.rep p).width σ dw) ∧
    rigidMax2 E elems (.repl c a) = (Sk.rep p).rmax σ dw ∧
    ((Sk.rep p).isExt = false → (Sk.rep p).width σ dw ≤ tw →
      instExpr2 E elems none (.repl c a) = (Sk.rep p).low σ dw ((Sk.rep p).width σ dw)) ∧
    instExpr2 E elems (some tw) (.repl c a) = (Sk.rep p).low σ dw tw ∧
    fitExpr2 E elems (some tw) (.repl c a) = (Sk.rep p).low σ dw tw := by
  have hRg : rigidMax2 E elems (.repl c a) = selfWidth2 E elems (.repl c a) := by
    first | rfl | simp [rigidMax2]
  refine ⟨by simpa [Sk.width] using hS, ?_, fun _ _ => ?_, ?_, ?_⟩
  · rw [hRg, hS]; simp [Sk.rmax]
  · rw [hI]; simp [Sk.low]
  · rw [hI]; simp [Sk.low]
  · rw [fitExpr2_of_rigid_eq (rigidExpr_repl c a) (by rw [hS, hw]), hI]; simp [Sk.low]

/-! ## WP-B2: the word-level shape theorem (`+`, `-`, the `Resize` marker)

The five facts of `skT_shape` for the CONTEXT-determined expressions of `rdsOfW?`. A marker makes an operand
narrower than its context, so the self-determined reading is the NATURAL width `Sk.width` (a max over the
operands), not the context: `selfWidth2 = rigidMax2 = width`, the lowering at no context is `low width` (not
for a root marker, whose `instExpr2 none` keeps the envelope's default-point width), and at the context `tw`
(plain and under `fitExpr2`) it is `low tw`. The self-determined operands are v1 expressions: their facts are the
v1 theorem `skT_shape`. -/

/-- The instance fact for a marker over a leaf: `.resize cw (accExpr σ a)` at every context and every leaf
width. -/
theorem ie_resize_leaf (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a)
    (m cw : Nat) :
    instExpr2 E elems (some cw) (.resize m e) = .resize cw (accExpr σ a) := by
  obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw h ha
  obtain ⟨hcp, hcl, hng⟩ := leaf_flags h
  simp [instExpr2, hsw, hcp, hcl, hng, hin]

/-- … and over a literal. -/
theorem ie_resize_lit (m cw : Nat) (v : LVec) :
    instExpr2 E elems (some cw) (.resize m (.lit v)) = .resize cw (.lit v) := by
  simp [instExpr2, PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, selfWidth2]

theorem ie_bin_none (b : BinOp) (hb : b = .and ∨ b = .or ∨ b = .xor ∨ b = .add ∨ b = .sub)
    (l r : PExpr) {a c : Nat} (hl : selfWidth2 E elems l = some a) (hr : selfWidth2 E elems r = some c) :
    instExpr2 E elems none (.binary (.m0 b) l r) =
      .binary b (fitExpr2 E elems (some (max a c)) l) (fitExpr2 E elems (some (max a c)) r) := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [instExpr2, hl, hr]

theorem ie_ternary_none' (c t e : PExpr) {a b : Nat} (ht : selfWidth2 E elems t = some a)
    (he : selfWidth2 E elems e = some b) :
    instExpr2 E elems none (.ternary c t e) =
      .ternary (instExpr2 E elems none c) (fitExpr2 E elems (some (max a b)) t)
        (fitExpr2 E elems (some (max a b)) e) := by
  simp [instExpr2, ht, he]

/-! ### Run-time shifts (WP-B2 gate 3) -/

/-- A shift at a context: `ctxTrunc2` over the shift of the left operand extended to the context (at least its own
width) and the amount at its own width. The left operand's `divOperandWidth2` is `wl`. -/
theorem ie_shl_some (s : Bool) (tw wl : Nat) (l r : PExpr) (hl : divOperandWidth2 E elems l = some wl) :
    instExpr2 E elems (some tw) (.binary (.m0 (.shl s)) l r) =
      ctxTrunc2 (some tw) (some (max tw wl)) (.binary (.shl s)
        (instDivOperand2 E elems s (some (max tw wl)) l)
        (instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r)) := by
  simp [instExpr2, hl]

theorem ie_shr_some (tw wl : Nat) (l r : PExpr) (hl : divOperandWidth2 E elems l = some wl) :
    instExpr2 E elems (some tw) (.binary (.m0 (.shr false)) l r) =
      ctxTrunc2 (some tw) (some (max tw wl)) (.binary (.shr false)
        (instDivOperand2 E elems false (some (max tw wl)) l)
        (instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r)) := by
  simp [instExpr2, hl]

/-- … at no context (a self-determined position): no truncation, the left operand at its own width. -/
theorem ie_shl_none (s : Bool) (wl : Nat) (l r : PExpr) (hl : divOperandWidth2 E elems l = some wl) :
    instExpr2 E elems none (.binary (.m0 (.shl s)) l r) =
      .binary (.shl s) (instDivOperand2 E elems s (some wl) l)
        (instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r) := by
  unfold instExpr2
  simp only [hl]
  rfl

theorem ie_shr_none (wl : Nat) (l r : PExpr) (hl : divOperandWidth2 E elems l = some wl) :
    instExpr2 E elems none (.binary (.m0 (.shr false)) l r) =
      .binary (.shr false) (instDivOperand2 E elems false (some wl) l)
        (instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r) := by
  unfold instExpr2
  simp only [hl]
  rfl

/-- `divOperandWidth2` of a signal access is its `selfWidth2`. -/
theorem divW_eq_selfW (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a) :
    divOperandWidth2 E elems e = selfWidth2 E elems e := by
  cases e with
  | ident n => simp [divOperandWidth2, selfWidth2]
  | bitSel b i =>
      cases b with
      | ident n => simp [divOperandWidth2, elemOf]
      | _ => simp [leafRd?] at h
  | partSel b msb lsb =>
      cases b with
      | ident n =>
          obtain ⟨hdec, hgeo, hns⟩ := ha
          simp only [leafRd?] at h
          obtain ⟨-, hc⟩ := partAcc?_cases h
          rcases hc with ⟨x, y, -, hx, hy, rfl⟩ | ⟨i, r, x, y, w, hnil, -⟩
          · obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hgeo
            have hagx : ∀ x' ∈ [x, y], ∀ v ∈ x'.names, E.vals.lookup v = some (σ v) :=
              fun x' hx' v hv => C.agree v (hns x' hx' v hv)
            obtain ⟨-, heh⟩ := affOf?_sound msb x hx (hagx x (by simp))
            obtain ⟨-, hel⟩ := affOf?_sound lsb y hy (hagx y (by simp))
            have hel1 := ctxElemsOne C hdg
            have h1 : 0 ≤ y.eval σ ∧ y.eval σ ≤ x.eval σ := ⟨hy0, hyx⟩
            simp [divOperandWidth2, selfWidth2, elemOf, hel1, heh, hel, h1.1, h1.2]
          · exact absurd hnil (by simp)
      | _ => simp [leafRd?] at h
  | arrayElem n is => simp [divOperandWidth2, selfWidth2]
  | arrayPart n is m a' b => simp [divOperandWidth2, selfWidth2]
  | _ => simp [leafRd?] at h

/-- **A shift operand** (the amount, or the left operand without its marker): its `divOperandWidth2` is the width of its
skeleton, and `instDivOperand2` at any context is `fitDivOperand2` over the lowering at that width. -/
theorem shOpd_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {x : PExpr} {rs : List Acc}
    (h : shOpdRd? ds x = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (s : Bool) (c : Option Nat) :
    divOperandWidth2 E elems x = some ((skT x rs).width σ dw) ∧
    instDivOperand2 E elems s c x =
      fitDivOperand2 s c (some ((skT x rs).width σ dw)) ((skT x rs).low σ dw ((skT x rs).width σ dw)) := by
  rw [instDiv_default s c x (shOpdKind h)]
  rcases shOpdRd?_cases h with ⟨v, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨a, hl, rfl⟩
  · simp [divOperandWidth2, skT, Sk.width, Sk.low, instExpr2]
  · simp [divOperandWidth2, skT, Sk.width, Sk.low, instExpr2]
  · obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
    have hdv := divW_eq_selfW C hl (hacc a (by simp))
    rcases leafKind_of_leafRd hl with ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ | ⟨n, is, m, a', b, rfl⟩ | ⟨b, pm, pl, rfl⟩ <;>
      (rw [hsw] at hdv; simp only [skT, List.headD_cons, Sk.width, Sk.low, hdv, Option.orElse_some, hin]; simp)

/-- **The amount of a shift** (WP-B2 gate 4b): as `shOpd_shape`, or a genvar bound in the instance, a constant of the
instance (`Sk.cref`) lowered at its own width, 32 bits. -/
theorem shAmt_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {x : PExpr} {rs : List Acc}
    (h : shAmtRd? ds x = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a)
    (hg : ∀ g, x = .genvarRef g → g ∈ ns)
    (hp : ∀ n, x = .paramRef n none → n ∈ ns) (s : Bool) (c : Option Nat) :
    shiftAmtWidth2 E elems x = some ((skT x rs).width σ dw) ∧
    instDivOperand2 E elems s c x =
      fitDivOperand2 s c (some ((skT x rs).width σ dw)) ((skT x rs).low σ dw ((skT x rs).width σ dw)) := by
  rcases shAmtRd?_cases h with ⟨g, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | h'
  · have hb : E.vals.lookup g = some (σ g) := C.agree g (hg g rfl)
    have e1 : instDivOperand2 E elems s c (.genvarRef g) =
        fitDivOperand2 s c (some 32) (.lit (LVec.ofInt 32 (σ g))) := by
      simp [instDivOperand2, instExpr2, hb, divOperandWidth2] <;> first | done | rfl
    have e2 : (skT (.genvarRef g) ([] : List Acc)).width σ dw = 32 := by simp [skT, Sk.width]
    have e3 : (skT (.genvarRef g) ([] : List Acc)).low σ dw 32 = .lit (LVec.ofInt 32 (σ g)) := by
      simp [skT, Sk.low, Aff.eval_var]
    refine ⟨by simp [shiftAmtWidth2, divOperandWidth2, e2], ?_⟩
    rw [e1, e2, e3]
  · have hb : E.vals.lookup n = some (σ n) := C.agree n (hp n rfl)
    · have e1 : instDivOperand2 E elems s c (.paramRef n none) =
          fitDivOperand2 s c (some 32) (.lit (LVec.ofInt 32 (σ n))) := by
          simp [instDivOperand2, instExpr2, hb, divOperandWidth2] <;> first | done | rfl
      have e2 : (skT (.paramRef n none) ([] : List Acc)).width σ dw = 32 := by simp [skT, Sk.width]
      have e3 : (skT (.paramRef n none) ([] : List Acc)).low σ dw 32 = .lit (LVec.ofInt 32 (σ n)) := by
        simp [skT, Sk.low, Aff.eval_var]
      refine ⟨by simp [shiftAmtWidth2, divOperandWidth2, e2], ?_⟩
      rw [e1, e2, e3]
  · have hx : shiftAmtWidth2 E elems x = divOperandWidth2 E elems x := by
      cases x <;> simp_all [shiftAmtWidth2, shOpdRd?]
    rw [hx]
    exact shOpd_shape C hdw h' hacc s c

/-- **The shape of a context-determined expression of the word-level fragment.** -/
theorem skT_shapeC (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOfW? ds v = .ok rs → fragW v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ConstOK σ ns v → ∀ tw, (skT v rs).WidthOkC σ dw tw →
        selfWidth2 E elems v = some ((skT v rs).width σ dw) ∧
        rigidMax2 E elems v = (skT v rs).rmax σ dw ∧
        ((skT v rs).isExt = false → (skT v rs).width σ dw ≤ tw →
          instExpr2 E elems none v = (skT v rs).low σ dw ((skT v rs).width σ dw)) ∧
        instExpr2 E elems (some tw) v = (skT v rs).low σ dw tw ∧
        fitExpr2 E elems (some tw) v = (skT v rs).low σ dw tw
  | .lit lv, rs, h, _, _, hcn, tw, hw => by
      simp only [rdsOfW?, Except.ok.injEq] at h
      subst h
      simp only [skT, Sk.WidthOkC] at hw
      refine ⟨by simp [skT, Sk.width, selfWidth2], by simp [skT, Sk.rmax, rigidMax2, selfWidth2],
        fun _ _ => by simp [skT, Sk.low, instExpr2], by simp [skT, Sk.low, instExpr2], ?_⟩
      rw [fitExpr2_lit, if_pos hw]
      simp [skT, Sk.low]
  | .binary op l r, rs, h, hf, hacc, hcn, tw, hw => by
      rcases rdsOfW?_binary h with ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨hb, ra, rb, hl, hr, rfl⟩ |
        ⟨hb, ra, rb, hl, hr, rfl⟩
      · -- `& | ^ + -`: context-determined operands
        replace hf := fragW_bin_ctx (selfOpW_false_of_ctx hb) hf
        have hla := rdsOfW?_len l ra hl hf.1
        have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
        have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
        have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
        have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
        have ihl := skT_shapeC C hdw l ra hl hf.1 hacl (cok_binary_l hcn)
        have ihr := skT_shapeC C hdw r rb hr hf.2 hacr (cok_binary_r hcn)
        by_cases hcm : ∃ cm : CmpOp, op = .m0 cm.ex
        · -- a comparison: one bit, the operands context-determined at the wider natural width
          obtain ⟨cm, rfl⟩ := hcm
          have hsk : skT (.binary (.m0 cm.ex) l r) (ra ++ rb) = .cmp cm (skT l ra) (skT r rb) := by
            cases cm <;> simp [skT, gateOf, CmpOp.ex, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hwl, hwr⟩ := hw
          obtain ⟨Sl, -, -, -, Fl⟩ := ihl _ hwl
          obtain ⟨Sr, -, -, -, Fr⟩ := ihr _ hwr
          have key : ∀ ctx, instExpr2 E elems ctx (.binary (.m0 cm.ex) l r) =
              Sk.low σ dw 1 (.cmp cm (skT l ra) (skT r rb)) := by
            intro ctx
            rw [ie_cmp cm ctx _ _ l r Sl Sr, Fl, Fr]
            simp only [Sk.low]
          exact ⟨sw_cmp cm l r, rm_cmp cm l r, fun _ _ => key none, key _, by
            rw [fitExpr2_binary]; exact key _⟩
        by_cases hmul : op = .mul
        · -- `*`: the shape of `+`, a factor being a signal access (`instExpr2` does not fold the product)
          subst hmul
          have hm := rdsOfW?_mul h
          have hsk : skT (.binary .mul l r) (ra ++ rb) = .mul (skT l ra) (skT r rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨Sl, Rl, -, -, Fl⟩ := ihl tw hw.1
          obtain ⟨Sr, Rr, -, -, Fr⟩ := ihr tw hw.2.1
          have hI1 : instExpr2 E elems (some tw) (.binary .mul l r) = (Sk.mul (skT l ra) (skT r rb)).low σ dw tw := by
            rw [instExpr2_mul (env := E) (elems := elems) hm tw (by
              rw [ctxOpWidth2_eq, Rl, Rr]
              exact Sk.maxO_getD_le (Sk.rmax_le _ tw hw.1 hw.2.2.1) (Sk.rmax_le _ tw hw.2.1 hw.2.2.2)), Fl, Fr]
            rfl
          refine ⟨by simp [selfWidth2, Sk.width, Sl, Sr], by
              rw [show rigidMax2 E elems (.binary .mul l r) = ctxOpWidth2 E elems l r from rfl, ctxOpWidth2_eq, Rl, Rr]
              rfl,
            fun _ hle => ?_, hI1, by rw [fitExpr2_binary]; exact hI1⟩
          obtain ⟨-, -, -, -, FlW⟩ := ihl _ (Sk.WidthOkC.mono _ _ _ hw.1 (Nat.le_max_left _ _) hle)
          obtain ⟨-, -, -, -, FrW⟩ := ihr _ (Sk.WidthOkC.mono _ _ _ hw.2.1 (Nat.le_max_right _ _) hle)
          rw [ie_mul_none hm Sl Sr, FlW, FrW]
          rfl
        obtain ⟨b, rfl, hbb⟩ : ∃ b, op = .m0 b ∧
            (b = .and ∨ b = .or ∨ b = .xor ∨ b = .add ∨ b = .sub) := by
          rcases ctxOpW_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | ⟨cm, rfl⟩ <;>
            first | exact ⟨_, rfl, by simp⟩ | exact absurd rfl hmul | exact absurd ⟨cm, rfl⟩ hcm
        have hsk : skT (.binary (.m0 b) l r) (ra ++ rb) = mkOpW b (skT l ra) (skT r rb) := by
          rcases hbb with rfl | rfl | rfl | rfl | rfl <;>
            simp [skT, gateOf, mkGate, mkOpW, e1, e2]
        rw [hsk] at hw ⊢
        have hwk : (skT l ra).WidthOkC σ dw tw ∧ (skT r rb).WidthOkC σ dw tw := by
          rcases hbb with rfl | rfl | rfl | rfl | rfl
          · exact hw
          · exact hw
          · exact hw
          · exact ⟨hw.1, hw.2.1⟩
          · exact ⟨hw.1, hw.2.1⟩
        obtain ⟨Sl, Rl, I0l, I1l, Fl⟩ := ihl tw hwk.1
        obtain ⟨Sr, Rr, I0r, I1r, Fr⟩ := ihr tw hwk.2
        have hS : selfWidth2 E elems (.binary (.m0 b) l r) =
            some (max ((skT l ra).width σ dw) ((skT r rb).width σ dw)) := by
          rcases hbb with rfl | rfl | rfl | rfl | rfl <;> simp [selfWidth2, Sl, Sr]
        have hR : rigidMax2 E elems (.binary (.m0 b) l r) =
            (mkOpW b (skT l ra) (skT r rb)).rmax σ dw := by
          rw [rm_ctx E elems b hbb l r, ctxOpWidth2_eq, Rl, Rr]
          rcases hbb with rfl | rfl | rfl | rfl | rfl <;> rfl
        have hI0 : max ((skT l ra).width σ dw) ((skT r rb).width σ dw) ≤ tw →
            instExpr2 E elems none (.binary (.m0 b) l r) =
              (mkOpW b (skT l ra) (skT r rb)).low σ dw
                (max ((skT l ra).width σ dw) ((skT r rb).width σ dw)) := by
          intro hle
          have hWl := Sk.WidthOkC.mono _ _ (max ((skT l ra).width σ dw) ((skT r rb).width σ dw)) hwk.1
            (Nat.le_max_left _ _) hle
          have hWr := Sk.WidthOkC.mono _ _ (max ((skT l ra).width σ dw) ((skT r rb).width σ dw)) hwk.2
            (Nat.le_max_right _ _) hle
          obtain ⟨-, -, -, -, FlW⟩ := ihl _ hWl
          obtain ⟨-, -, -, -, FrW⟩ := ihr _ hWr
          have hI0 := ie_bin_none b hbb l r Sl Sr
          rw [FlW, FrW] at hI0
          rcases hbb with rfl | rfl | rfl | rfl | rfl <;> exact hI0
        have hI1 : instExpr2 E elems (some tw) (.binary (.m0 b) l r) =
            .binary b (fitExpr2 E elems (some tw) l) (fitExpr2 E elems (some tw) r) := by
          rcases hbb with rfl | rfl | rfl | rfl | rfl
          · simp [instExpr2]
          · simp [instExpr2]
          · simp [instExpr2]
          · exact instExpr2_add tw l r (by
              rw [ctxOpWidth2_eq, Rl, Rr]
              exact Sk.maxO_getD_le (Sk.rmax_le _ tw hwk.1 hw.2.2.1) (Sk.rmax_le _ tw hwk.2 hw.2.2.2))
          · exact instExpr2_sub tw l r (by
              rw [ctxOpWidth2_eq, Rl, Rr]
              exact Sk.maxO_getD_le (Sk.rmax_le _ tw hwk.1 hw.2.2.1) (Sk.rmax_le _ tw hwk.2 hw.2.2.2))
        rw [Fl, Fr] at hI1
        rcases hbb with rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨hS, hR, fun _ hwt => hI0 hwt, hI1, by rw [fitExpr2_binary]; exact hI1⟩
      · -- `&&`, `||`, `==`, `!=`: one bit, self-determined v1 operands
        replace hf := fragW_bin_self hb hf
        have hla := rdsOf?_len l ra hl hf.1
        have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
        have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
        have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
        have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
        rcases selfOpW_cases hb with rfl | rfl
        · have hsk : skT (.binary .land l r) (ra ++ rb) = .land (skT l ra) (skT r rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr⟩ := hw
          obtain ⟨Sl, -, -, I1l, -⟩ := skT_shape C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, I1r, -⟩ := skT_shape C hdw r rb hr hf.2 hacr _ (Sk.selfOk_widthOk σ dw _ hsr)
          have key : ∀ ctx, instExpr2 E elems ctx (.binary .land l r) =
              Sk.low σ dw 1 (.land (skT l ra) (skT r rb)) := by
            intro ctx
            rw [ie_land, Sl, Sr, I1l, I1r, Sk.low_irrel σ dw (skT l ra) hsl _ 0,
              Sk.low_irrel σ dw (skT r rb) hsr _ 0]
            rfl
          exact ⟨sw_land l r, rm_land l r, fun _ _ => key none, key _, by rw [fitExpr2_binary]; exact key _⟩
        · have hsk : skT (.binary .lor l r) (ra ++ rb) = .lor (skT l ra) (skT r rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr⟩ := hw
          obtain ⟨Sl, -, -, I1l, -⟩ := skT_shape C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, I1r, -⟩ := skT_shape C hdw r rb hr hf.2 hacr _ (Sk.selfOk_widthOk σ dw _ hsr)
          have key : ∀ ctx, instExpr2 E elems ctx (.binary .lor l r) =
              Sk.low σ dw 1 (.lor (skT l ra) (skT r rb)) := by
            intro ctx
            rw [ie_lor, Sl, Sr, I1l, I1r, Sk.low_irrel σ dw (skT l ra) hsl _ 0,
              Sk.low_irrel σ dw (skT r rb) hsr _ 0]
            rfl
          exact ⟨sw_lor l r, rm_lor l r, fun _ _ => key none, key _, by rw [fitExpr2_binary]; exact key _⟩
      · -- a run-time shift (WP-B2 gate 3)
        obtain ⟨d, sg, x, hd, hxo, hxl, hsk⟩ := skT_sh hb hl hr
        have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
        have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
        rw [hsk] at hw ⊢
        have hL := shOpd_shape C hdw hxo hacl sg
        have hR := shAmt_shape C hdw hr hacr (fun g hgr => hcn.1 g (cnames_amount hb hgr))
          (fun n hnr => hcn.1 n (cnames_amount_param hb hnr)) false
        have hlsw : divOperandWidth2 E elems l = some ((skT x ra).width σ dw) := by
          rcases hxl with rfl | ⟨-, m, rfl⟩ | ⟨-, m, rfl⟩
          · exact (hL none).1
          · simpa [divOperandWidth2] using (hL none).1
          · simpa [divOperandWidth2] using (hL none).1
        have hLexp : ∀ c : Nat, instDivOperand2 E elems sg (some c) l =
            fitDivOperand2 sg (some c) (some ((skT x ra).width σ dw))
              ((skT x ra).low σ dw ((skT x ra).width σ dw)) := by
          intro c
          rcases hxl with rfl | ⟨rfl, m, rfl⟩ | ⟨rfl, m, rfl⟩
          · exact (hL _).2
          · rw [instDiv_resize false (some c) m x (shOpdKind hxo)]; exact (hL _).2
          · rw [instDiv_sresize true (some c) m x]; exact (hL _).2
        have hRexp : instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r =
            (skT r rb).low σ dw ((skT r rb).width σ dw) := by
          rw [(hR none).1]
          rw [(hR _).2]
          simp [fitDivOperand2]
        rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · refine ⟨by simp [selfWidth2, Sk.width, hlsw], by simp [rigidMax2, selfWidth2, Sk.rmax, hlsw],
            fun _ _ => ?_, ?_, ?_⟩
          · rw [ie_shl_none sg _ l r hlsw, hLexp, hRexp]
            cases sg <;> simp [Sk.low, Sk.width, fitDivOperand2]
          · rw [ie_shl_some sg tw _ l r hlsw, hLexp, hRexp]
            cases sg <;> simp [Sk.low, fitDivOperand2, ctxTrunc2]
          · rw [fitExpr2_binary, ie_shl_some sg tw _ l r hlsw, hLexp, hRexp]
            cases sg <;> simp [Sk.low, fitDivOperand2, ctxTrunc2]
        · refine ⟨by simp [selfWidth2, Sk.width, hlsw], by simp [rigidMax2, selfWidth2, Sk.rmax, hlsw],
            fun _ _ => ?_, ?_, ?_⟩
          · rw [ie_shr_none _ l r hlsw, hLexp, hRexp]
            simp [Sk.low, Sk.width, fitDivOperand2]
          · rw [ie_shr_some tw _ l r hlsw, hLexp, hRexp]
            simp [Sk.low, fitDivOperand2, ctxTrunc2]
          · rw [fitExpr2_binary, ie_shr_some tw _ l r hlsw, hLexp, hRexp]
            simp [Sk.low, fitDivOperand2, ctxTrunc2]
  | .unary op a, rs, h, hf, hacc, hcn, tw, hw => by
      rcases rdsOfW?_unary h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · replace hf : fragW a = true := by simpa [fragW] using hf
        have hsk : skT (.unary (.m0 .bnot) a) rs = .bnot (skT a rs) := by simp [skT]
        rw [hsk] at hw ⊢
        simp only [Sk.WidthOkC] at hw
        obtain ⟨Sa, Ra, I0a, I1a, Fa⟩ := skT_shapeC C hdw a rs ha hf hacc (cok_unary hcn) tw hw.1
        have hrm : (rigidMax2 E elems a).getD tw ≤ tw := by
          rw [Ra]; exact Sk.getD_le (Sk.rmax_le _ tw hw.1 hw.2)
        have I1 : instExpr2 E elems (some tw) (.unary (.m0 .bnot) a) =
            (Sk.bnot (skT a rs)).low σ dw tw := by
          rw [ie_bnot_some tw a hrm, Fa]; rfl
        refine ⟨by rw [sw_bnot]; exact Sa, by rw [rm_bnot]; exact Ra, fun _ hle => ?_, I1, ?_⟩
        · have hW := Sk.WidthOkC.mono _ _ ((skT a rs).width σ dw) hw.1 (Nat.le_refl _) hle
          obtain ⟨-, -, -, I1aW, -⟩ := skT_shapeC C hdw a rs ha hf hacc (cok_unary hcn) _ hW
          rw [ie_bnot_none, Sa, I1aW]; rfl
        · rw [fitExpr2_of_not_rigid tw (rigidExpr_unary _ _)]; exact I1
      · replace hf : fragG a = true := by simpa [fragW] using hf
        have hsk : skT (.unary (.m0 .lnot) a) rs = .lnot (skT a rs) := by simp [skT]
        rw [hsk] at hw ⊢
        obtain ⟨rfl, hsa⟩ := hw
        obtain ⟨-, -, I0a, -, -⟩ := skT_shape C hdw a rs ha hf hacc _ (Sk.selfOk_widthOk σ dw _ hsa)
        have key : ∀ ctx, instExpr2 E elems ctx (.unary (.m0 .lnot) a) = Sk.low σ dw 1 (.lnot (skT a rs)) := by
          intro ctx
          rw [ie_lnot, I0a, Sk.low_irrel σ dw (skT a rs) hsa _ 0]
          rfl
        exact ⟨sw_lnot a, rm_lnot a, fun _ _ => key none, key _, by
          rw [fitExpr2_of_not_rigid 1 (rigidExpr_unary _ _)]; exact key _⟩
  | .ternary c t f, rs, h, hf, hacc, hcn, tw, hw => by
      obtain ⟨rc, rt, rf, hc, ht, hfe, rfl⟩ := rdsOfW?_ternary h
      simp only [fragW, Bool.and_eq_true] at hf
      have hc' := rdsOf?_len c rc hc hf.1.1
      have ht' := rdsOfW?_len t rt ht hf.1.2
      have e1 : (rc ++ rt ++ rf).take (cnt c) = rc := by
        rw [List.append_assoc]; exact List.take_left' hc'
      have e2 : (rc ++ rt ++ rf).drop (cnt c) = rt ++ rf := by
        rw [List.append_assoc]; exact List.drop_left' hc'
      have e3 : (rt ++ rf).take (cnt t) = rt := List.take_left' ht'
      have e4 : (rt ++ rf).drop (cnt t) = rf := List.drop_left' ht'
      have hsk : skT (.ternary c t f) (rc ++ rt ++ rf) = .tern (skT c rc) (skT t rt) (skT f rf) := by
        simp only [skT, e1, e2, e3, e4]
      rw [hsk] at hw ⊢
      obtain ⟨hsc, hwc, hwt, hwf⟩ := hw
      have hc1 : (skT c rc).WidthOk σ dw 1 := by
        have := Sk.selfOk_widthOk σ dw _ hsc
        rwa [hwc] at this
      obtain ⟨-, -, I0c, -, -⟩ := skT_shape C hdw c rc hc hf.1.1
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_left _ hx))) 1 hc1
      obtain ⟨St, Rt, -, -, Ft⟩ := skT_shapeC C hdw t rt ht hf.1.2
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx)))
        (cok_ternary_t hcn) tw hwt
      obtain ⟨Sf, Rf, -, -, Ff⟩ := skT_shapeC C hdw f rf hfe hf.2
        (fun x hx => hacc x (List.mem_append_right _ hx))
        (cok_ternary_e hcn) tw hwf
      have I1 : instExpr2 E elems (some tw) (.ternary c t f) =
          Sk.low σ dw tw (.tern (skT c rc) (skT t rt) (skT f rf)) := by
        rw [ie_ternary_some, I0c, Ft, Ff]
        simp only [Sk.low, Sk.low_irrel σ dw _ hsc 1 0]
      refine ⟨by simp [selfWidth2, St, Sf, Sk.width],
        by rw [rm_tern_maxO, Rt, Rf]; rfl, fun _ hle => ?_, I1, ?_⟩
      · have hle' : max ((skT t rt).width σ dw) ((skT f rf).width σ dw) ≤ tw := hle
        have hWt := Sk.WidthOkC.mono _ _ (max ((skT t rt).width σ dw) ((skT f rf).width σ dw)) hwt
          (Nat.le_max_left _ _) hle'
        have hWf := Sk.WidthOkC.mono _ _ (max ((skT t rt).width σ dw) ((skT f rf).width σ dw)) hwf
          (Nat.le_max_right _ _) hle'
        obtain ⟨-, -, -, -, FtW⟩ := skT_shapeC C hdw t rt ht hf.1.2
          (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx)))
          (cok_ternary_t hcn) _ hWt
        obtain ⟨-, -, -, -, FfW⟩ := skT_shapeC C hdw f rf hfe hf.2
          (fun x hx => hacc x (List.mem_append_right _ hx))
          (cok_ternary_e hcn) _ hWf
        rw [ie_ternary_none' c t f St Sf, I0c, FtW, FfW]
        simp only [Sk.low, Sk.width, Sk.low_irrel σ dw _ hsc 1 0]
      · rw [fitExpr2_of_not_rigid tw (rigidExpr_ternary _ _ _)]; exact I1
  | .reduce op a, rs, h, hf, hacc, hcn, tw, hw => by
      simp only [fragW] at hf
      have ha := rdsOfW?_reduce h
      have hsk : skT (.reduce op a) rs = .red op (skT a rs) := by simp [skT]
      rw [hsk] at hw ⊢
      obtain ⟨rfl, hsa⟩ := hw
      obtain ⟨Sa, -, -, I1a, -⟩ := skT_shape C hdw a rs ha hf hacc _ (Sk.selfOk_widthOk σ dw _ hsa)
      have key : ∀ ctx, instExpr2 E elems ctx (.reduce op a) = Sk.low σ dw 1 (.red op (skT a rs)) := by
        intro ctx
        rw [ie_reduce, Sa, I1a, Sk.low_irrel σ dw (skT a rs) hsa _ 0]
        rfl
      exact ⟨sw_reduce op a, rm_reduce op a, fun _ _ => key none, key _, by
        rw [fitExpr2_of_rigid_eq (rigidExpr_reduce op a) (sw_reduce op a)]; exact key _⟩
  | .resize m e, rs, h, hf, hacc, hcn, tw, hw => by
      rcases rdsOfW?_resize h with ⟨v, rfl, rfl⟩ | ⟨hn, a, hl, rfl⟩ | ⟨hop, hr⟩
      · simp only [skT, Sk.WidthOkC, Sk.width, Part.wid] at hw ⊢
        refine ⟨by simp [selfWidth2], by simp [rigidMax2, selfWidth2, Sk.rmax, Part.wid],
          fun h => by simp [Sk.isExt] at h, ?_, ?_⟩
        · rw [ie_resize_lit]; simp [Sk.low, Part.expr]
        · rw [fitExpr2_of_not_rigid tw rfl, ie_resize_lit]; simp [Sk.low, Part.expr]
      · have hsk : skT (.resize m e) [a] = .ext (.rd a) := by
          cases e <;> first | exact absurd rfl (hn _) | (simp [leafRd?] at hl; done) | rfl
        rw [hsk] at hw ⊢
        obtain ⟨hsw, -, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
        have I1 : instExpr2 E elems (some tw) (.resize m e) = (Sk.ext (.rd a)).low σ dw tw := by
          rw [ie_resize_leaf C hdw hl (hacc a (by simp)) m tw]; rfl
        refine ⟨by simp [selfWidth2, hsw, Sk.width, Part.wid],
          by simp [rigidMax2, Sk.rmax, Part.wid, rm_leaf hl, hsw],
          fun h => by simp [Sk.isExt] at h, I1, ?_⟩
        rw [fitExpr2_of_not_rigid tw rfl]; exact I1
      · -- a marker around an operation: a truncation, or a zero extension of a result that does not follow the context
        have hf' : fragW e = true := by simpa [fragW] using hf
        have hsk : skT (.resize m e) rs = .rsz e.ctxPropagates (skT e rs) := skT_resize_op m rs hr hop
        rw [hsk] at hw ⊢
        have ihe := skT_shapeC C hdw e rs hr hf' hacc (cok_resize hcn)
        -- the bundle of the operand at the context its contract holds at
        have hkey : selfWidth2 E elems e = some ((skT e rs).width σ dw) ∧
            rigidMax2 E elems e = (skT e rs).rmax σ dw ∧
            instExpr2 E elems (some tw) (.resize m e) = (Sk.rsz e.ctxPropagates (skT e rs)).low σ dw tw := by
          have hbundle : ∀ c, (skT e rs).WidthOkC σ dw c →
              selfWidth2 E elems e = some ((skT e rs).width σ dw) ∧
                rigidMax2 E elems e = (skT e rs).rmax σ dw ∧
                  instExpr2 E elems (some c) e = (skT e rs).low σ dw c := by
            intro c hc
            obtain ⟨Se, Re, -, I1e, -⟩ := ihe c hc
            exact ⟨Se, Re, I1e⟩
          cases hpr : e.ctxPropagates
          · rw [hpr] at hw
            simp only [Sk.WidthOkC] at hw
            obtain ⟨Se, Re, I1e⟩ := hbundle _ hw
            refine ⟨Se, Re, ?_⟩
            rw [ie_resize_op_eq hop Se, hpr]
            simp [Sk.low, I1e]
          · rw [hpr] at hw
            simp only [Sk.WidthOkC] at hw
            by_cases hc : (skT e rs).width σ dw < tw
            · rw [if_pos hc] at hw
              obtain ⟨Se, Re, I1e⟩ := hbundle _ hw
              refine ⟨Se, Re, ?_⟩
              rw [ie_resize_op_eq hop Se, hpr]
              simp [Sk.low, hc, I1e]
            · rw [if_neg hc] at hw
              obtain ⟨Se, Re, I1e⟩ := hbundle _ hw
              refine ⟨Se, Re, ?_⟩
              rw [ie_resize_op_eq hop Se, hpr]
              simp [Sk.low, hc, I1e]
        obtain ⟨Se, Re, I1⟩ := hkey
        refine ⟨by simp [selfWidth2, Se, Sk.width], by simpa [rigidMax2, Sk.rmax] using Re,
          fun h => by simp [Sk.isExt] at h, I1, ?_⟩
        rw [fitExpr2_of_not_rigid tw rfl]; exact I1
  | .int v, rs, h, _, _, hcn, tw, _ => by
      simp only [rdsOfW?, Except.ok.injEq] at h
      subst h
      refine ⟨by simp [selfWidth2, skT, Sk.width], by simp [rigidMax2, skT, Sk.rmax], fun _ _ => ?_, ?_, ?_⟩
      · rw [ie_int]; rfl
      · rw [ie_int]; rfl
      · rw [fitExpr2_of_not_rigid tw rfl, ie_int]; rfl
  | .ident n, rs, h, _, hacc, hcn, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOfW?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOkC, Sk.low, Sk.width, Sk.rmax] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨hsw, by rw [rm_leaf hl, hsw], fun _ _ => hin none, hin _,
        leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .bitSel b i, rs, h, _, hacc, hcn, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOfW?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOkC, Sk.low, Sk.width, Sk.rmax] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨hsw, by rw [rm_leaf hl, hsw], fun _ _ => hin none, hin _,
        leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .partSel b pm pl, rs, h, _, hacc, hcn, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOfW?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOkC, Sk.low, Sk.width, Sk.rmax] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨hsw, by rw [rm_leaf hl, hsw], fun _ _ => hin none, hin _,
        leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .arrayElem n is, rs, h, _, hacc, hcn, tw, hw => by
      obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOfW?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOkC, Sk.low, Sk.width, Sk.rmax] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a (by simp))
      exact ⟨hsw, by rw [rm_leaf hl, hsw], fun _ _ => hin none, hin _,
        leaf_fit C hdw hl (hacc a (by simp)) hw⟩
  | .arrayPart n is m a b, rs, h, _, hacc, hcn, tw, hw => by
      obtain ⟨a', hl, rfl⟩ := rdsLeaf_cases (by simpa [rdsOfW?] using h)
      simp only [skT, List.headD_cons, Sk.WidthOkC, Sk.low, Sk.width, Sk.rmax] at hw ⊢
      obtain ⟨hsw, hin, -⟩ := leaf_eq C hdw hl (hacc a' (by simp))
      exact ⟨hsw, by rw [rm_leaf hl, hsw], fun _ _ => hin none, hin _,
        leaf_fit C hdw hl (hacc a' (by simp)) hw⟩
  | .concat ps, rs, h, _, hacc, hcn, tw, hw => by
      -- a concatenation operand (WP-B2 gate 3b): the same node as the top-level concatenation
      have h' : partsRdW? ds ps = .ok rs := by simpa [rdsOfW?] using h
      obtain ⟨h1, h2⟩ := parts_shapeW C hdw ps rs h' hacc hcn
      simp only [skT, Sk.WidthOkC] at hw
      have hS : selfWidth2 E elems (.concat ps) = some ((skT (.concat ps) rs).width σ dw) := by
        simpa [skT, Sk.width] using h1
      have hI : ∀ (ctx : Option Nat) (tw' : Nat), instExpr2 E elems ctx (.concat ps) =
          (skT (.concat ps) rs).low σ dw tw' := by
        intro ctx tw'
        simp only [instExpr2_concat, skT, Sk.low, h2]
      have hRg : rigidMax2 E elems (.concat ps) = selfWidth2 E elems (.concat ps) := by
        first | rfl | simp [rigidMax2]
      refine ⟨hS, ?_, fun _ _ => hI none _, hI _ _, ?_⟩
      · rw [hRg, hS]; simp [skT, Sk.rmax, Sk.width]
      · rw [fitExpr2_concat h1, if_pos hw]
        simp only [skT, Sk.low, h2]
  | .repl c a, rs, h, _, hacc, hcn, tw, hw => by
      have h' : repRd? ds c a = .ok rs := by simpa [rdsOfW?] using h
      rcases repl_shape C hdw h' hacc hcn with ⟨v, rfl, rfl, hS, hI⟩ | ⟨x, e, hnl, rfl, rfl, hS, hI⟩
      · simp only [skT, Sk.WidthOkC] at hw ⊢
        exact rep_bundle hS hI hw
      · have hsk : skT (.repl c (.concat [e])) [x] = .rep (.reprd (repAff c) x) := by
          cases e <;> first | rfl | exact absurd rfl (hnl _)
        rw [hsk] at hw ⊢
        simp only [Sk.WidthOkC] at hw
        exact rep_bundle hS hI hw
  | .fill _, _, _, hf, _, _, _, _ => by simp [fragW] at hf
  | .paramRef .., rs, h, _, _, _, _, _ | .genvarRef .., rs, h, _, _, _, _, _
  | .enumRef .., rs, h, _, _, _, _, _
  | .signedResize .., rs, h, _, _, _, _, _
  | .squash2 .., rs, h, _, _, _, _, _
  | .sysCall .., rs, h, _, _, _, _, _
  | .cast .., rs, h, _, _, _, _, _
  | .unsupported .., rs, h, _, _, _, _, _ => by
      simp [rdsOfW?, rdsLeaf?, leafRd?] at h

theorem gate_shapeC (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOfW? ds v = .ok rs → fragW v = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ConstOK σ ns v → ∀ tw, (skT v rs).WidthOkC σ dw tw →
        fitExpr2 E elems (some tw) v = (skT v rs).low σ dw tw :=
  fun v rs h hf hacc hcn tw hw => (skT_shapeC C hdw v rs h hf hacc hcn tw hw).2.2.2.2

/-- **A whole right-hand side of the word-level fragment** (a fill, a concatenation, or an expression). -/
theorem rhs_shapeC (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {v : PExpr}
    {rs : List Acc} (h : rhsRds? ds v = .ok rs) (hf : fragOk v = true)
    (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (hcn : ConstOK σ ns v) {tw : Nat}
    (hw : (skRhs v rs).WidthOkC σ dw tw) :
    fitExpr2 E elems (some tw) v = (skRhs v rs).low σ dw tw := by
  by_cases hfill : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hfill
    rw [fitExpr2_of_not_rigid tw rfl]
    simp [instExpr2, skRhs, Sk.low]
  by_cases hcat : ∃ ps, v = .concat ps
  · obtain ⟨ps, rfl⟩ := hcat
    have h' : partsRdW? ds ps = .ok rs := by simpa [rhsRds?, rdsOfW?] using h
    obtain ⟨h1, h2⟩ := parts_shapeW C hdw ps rs h' hacc hcn
    simp only [skRhs, Sk.WidthOkC] at hw
    rw [fitExpr2_concat h1, if_pos hw]
    simp only [skRhs, Sk.low, h2]
  · have hn1 : ∀ b, v ≠ .fill b := fun b h => hfill ⟨b, h⟩
    have hn2 : ∀ ps, v ≠ .concat ps := fun ps h => hcat ⟨ps, h⟩
    have h2 : rhsRds? ds v = rdsOfW? ds v := by
      cases v <;> first | rfl | exact absurd rfl (hn1 _)
    rw [h2] at h
    rw [fragOk_of_ne hn1 hn2] at hf
    rw [skRhs_of_ne hn1 hn2] at hw ⊢
    exact gate_shapeC C hdw v rs h hf hacc hcn tw hw

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
  rcases tgtOf?_cases h with ⟨n, rfl, rfl⟩ | ⟨n, i, x, rfl, hx, hba⟩ | ⟨n, is, rfl, he⟩ |
    ⟨n, is, mode, hi, lo, rfl, hp⟩ | ⟨n, msb, lsb, rfl, hp⟩
  · have hW : E.widths.lookup n = some (dw n) := by
      rw [C.widths n]; exact hdw n (by simpa [Acc.name] using hdec)
    rw [instLhs2_ident hW]; rfl
  · rcases bitAcc?_cases ds n x with hb | ⟨w, hb⟩ <;> rw [hb] at hba <;> simp only [Except.ok.injEq] at hba <;>
      subst hba
    · obtain ⟨hnn, hel⟩ := hgeo
      have hel' : elems.lookup n = some 1 := C.elems n hel
      obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      rw [instLhs2_bitSel hel' hev hnn]
      simp [Acc.lhs, Acc.lo, Acc.win]
    · -- a legacy select of a row
      obtain ⟨m1, m2, hdg, hm2, hw, hx0, hx1⟩ := hgeo
      have hel' := ctxElemsRow C hdg hm2
      obtain ⟨-, hev⟩ := affOf?_sound i x hx (hagx x (by simp [Acc.affs]))
      rw [instLhs2_bitSel hel' hev hx0]
      simp [Acc.lhs, Acc.lo, Acc.wid, Acc.win, rmN, hw]
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
  · -- legacy part select
    obtain ⟨-, hc⟩ := partAcc?_cases hp
    rcases hc with ⟨x, y, -, hx, hy, rfl⟩ | ⟨i, r, x, y, w, hnil, -⟩
    · obtain ⟨m, hdg, hy0, hyx, hxm⟩ := hgeo
      rw [instLhs_partSel C hdg hx hy hagx hy0 hyx]
      simp [Acc.lhs, Acc.lo, Acc.wid, Acc.win]
    · exact absurd hnil (by simp)

/-- **A site instantiates to the promised assign with the promised right-hand side** (the word-level reading of
its width contract). -/
theorem proc_shapeC (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite} (hs : siteOf? ds pos p = .ok st)
    (hso : ∀ a ∈ st.tgt :: st.rds, AccOK σ DW DG EW ns a) (hcn : st.ConstOK σ ns)
    (hf : fragOk (rhsOf p) = true)
    (hw : (skRhs (rhsOf p) st.rds).WidthOkC σ dw (st.tgt.win σ dw).2.2) :
    instProcess2 E elems p =
      .assign (st.tgt.lhs σ) ((skRhs (rhsOf p) st.rds).low σ dw (st.tgt.win σ dw).2.2) := by
  have hrdacc : ∀ rds, rds = st.rds → ∀ a ∈ rds, AccOK σ DW DG EW ns a := by
    rintro rds rfl a ha
    exact hso a (List.mem_cons_of_mem _ ha)
  rcases siteOf?_cases hs with ⟨t, v, rds, rfl, hrds, rfl⟩ | ⟨l, v, tg, rds, rfl, htg, hrds, rfl⟩
  · have hdt : (DW t).isSome = true := (hso _ (List.mem_cons_self ..)).1
    have hW : E.widths.lookup t = some (dw t) := by
      rw [C.widths t]; exact hdw t hdt
    rw [instProcess2_assign v hW]
    simp only [rhsOf] at hf hw ⊢
    have := rhs_shapeC C hdw hrds hf (hrdacc _ rfl) hcn hw
    simpa [Acc.win, Acc.lhs] using this
  · rw [instProcess2_assignL v (instLhs_acc_w C hdw htg (hso _ (List.mem_cons_self ..)))]
    simp only [rhsOf] at hf hw ⊢
    rw [rhs_shapeC C hdw hrds hf (hrdacc _ rfl) hcn hw]


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

/-! ### Boolean reductions respect agreement below the width -/

theorem _root_.LeanModels.Sv.XF.any_one (f : Nat → Bool) : XF.any 1 f = f 0 := by
  simp only [XF.any]
  cases h : f 0 <;> simp [h]

theorem _root_.LeanModels.Sv.XF.any_congr {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) :
    XF.any w f = XF.any w g := by
  simp only [XF.any]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨k, hk, hf⟩; exact ⟨k, hk, by rw [← h k hk]; exact hf⟩
  · rintro ⟨k, hk, hf⟩; exact ⟨k, hk, by rw [h k hk]; exact hf⟩

theorem _root_.LeanModels.Sv.XF.eqv_one (f g : Nat → Bool) : XF.eqv 1 f g = decide (f 0 = g 0) := by
  simp only [XF.eqv]
  apply decide_eq_decide.mpr
  constructor
  · intro h; exact h 0 (by omega)
  · intro h k hk
    obtain rfl : k = 0 := by omega
    exact h

theorem _root_.LeanModels.Sv.XF.all_congr {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) :
    XF.all w f = XF.all w g := by
  simp only [XF.all]
  apply decide_eq_decide.mpr
  constructor
  · intro hf k hk; rw [← h k hk]; exact hf k hk
  · intro hf k hk; rw [h k hk]; exact hf k hk

theorem _root_.LeanModels.Sv.XF.parity_congr {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) :
    XF.parity w f = XF.parity w g := by
  have : (fun i : Fin w => f i.val) = fun i => g i.val := funext fun i => h i.val i.isLt
  simp only [XF.parity, this]

theorem _root_.LeanModels.Sv.XF.red_congr (op : RedOp) {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) :
    XF.red op w f = XF.red op w g := by
  cases op <;> simp [XF.red, XF.any_congr h, XF.all_congr h, XF.parity_congr h]

theorem _root_.LeanModels.Sv.XF.eqv_congr {w : Nat} {f g f' g' : Nat → Bool} (h : ∀ k, k < w → f k = f' k)
    (h' : ∀ k, k < w → g k = g' k) : XF.eqv w f g = XF.eqv w f' g' := by
  simp only [XF.eqv]
  apply decide_eq_decide.mpr
  constructor
  · intro hf k hk; rw [← h k hk, ← h' k hk]; exact hf k hk
  · intro hf k hk; rw [h k hk, h' k hk]; exact hf k hk

theorem partLeaves_cons_rd (a : Acc) (ps : List Part) :
    partLeaves (.rd a :: ps) = a :: partLeaves ps := rfl

theorem acc_ne_whole_of_known {a : Acc} (h : a.isWhole = false) : ∀ n, a ≠ .whole n := by
  intro n hn
  subst hn
  simp [Acc.isWhole] at h

/-- One part of a concatenation: its expression is in the x-free fragment at the part's width, with the part's
bits. -/
theorem part_low {m : Design2} {σ : String → Int} {dw : String → Nat} (env : String → Nat → Bool) :
    ∀ (p : Part), partKnown [p] = true → (∀ a ∈ partLeaves [p], LeafOk m σ dw a) →
      (p.expr σ).xfWidth m = some (p.wid σ dw) ∧ ∀ k, (p.expr σ).xfBits m env k = p.bit σ env k
  | .lit v, hk, _ => by
      simp only [partKnown, Bool.and_true] at hk
      exact ⟨by simp [Part.expr, Part.wid, Expr2.xfWidth, hk], fun k => by
        simp [Part.expr, Part.bit, Expr2.xfBits]⟩
  | .rd a, _, hL => by
      have hA : LeafOk m σ dw a := hL a (by simp [partLeaves])
      exact ⟨by simp [Part.expr, Part.wid, expr_xfWidth hA], fun k => by
        simp [Part.expr, Part.bit, expr_xfBits]⟩
  | .replit c v, hk, _ => by
      simp only [partKnown, Bool.and_true] at hk
      refine ⟨?_, fun k => ?_⟩
      · simp [Part.expr, Part.wid, Expr2.xfWidth, Expr2.xfWidthSum, hk, Nat.mul_comm]
      · simp [Part.expr, Part.bit, Expr2.xfBits, Expr2.xfWidth, Expr2.xfWidthSum, Expr2.catBits, hk]
  | .reprd c a, hk, hL => by
      simp only [partKnown, Bool.and_true, Bool.not_eq_true'] at hk
      have hA : LeafOk m σ dw a := hL a (by simp [partLeaves])
      have hw := win_wid_of_ne_whole (σ := σ) (dw := dw) (acc_ne_whole_of_known hk)
      refine ⟨?_, fun k => ?_⟩
      · simp [Part.expr, Part.wid, Expr2.xfWidth, Expr2.xfWidthSum, expr_xfWidth hA, hw, Nat.mul_comm]
      · simp [Part.expr, Part.bit, Expr2.xfBits, Expr2.xfWidth, Expr2.xfWidthSum, Expr2.catBits, expr_xfWidth hA,
          expr_xfBits, hw]

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
  | .replit c v :: ps, hk, hL => by
      simp only [partKnown, Bool.and_eq_true] at hk
      obtain ⟨ih1, ih2⟩ := cat_low env ps hk.2 (by simpa [partLeaves] using hL)
      obtain ⟨w1, b1⟩ := part_low (m := m) (σ := σ) (dw := dw) env (.replit c v) (by simpa [partKnown] using hk.1)
        (by simp [partLeaves])
      refine ⟨?_, fun k => ?_⟩
      · simp [Expr2.xfWidthSum, w1, ih1, Nat.add_comm]
      · simp [Expr2.catBits, catBit, ih1, ih2, b1, Part.wid]
  | .reprd c a :: ps, hk, hL => by
      simp only [partKnown, Bool.and_eq_true] at hk
      obtain ⟨ih1, ih2⟩ := cat_low env ps hk.2 (fun x hx => hL x (by simp [partLeaves, hx]))
      obtain ⟨w1, b1⟩ := part_low (m := m) (σ := σ) (dw := dw) env (.reprd c a) (by simpa [partKnown] using hk.1)
        (fun x hx => hL x (by simp [partLeaves] at hx ⊢; simp [hx]))
      refine ⟨?_, fun k => ?_⟩
      · simp [Expr2.xfWidthSum, w1, ih1, Nat.add_comm]
      · simp [Expr2.catBits, catBit, ih1, ih2, b1, Part.wid]

/-! ### x-free width and bits of the new `Expr2` nodes -/

section xfops
variable {m : Design2}

theorem xf_lnot {e : Expr2} {w : Nat} (h : e.xfWidth m = some w) :
    (Expr2.unary .lnot e).xfWidth m = some 1 := by
  simp [Expr2.xfWidth, h]

theorem xfb_lnot {e : Expr2} {w : Nat} (h : e.xfWidth m = some w) (env : String → Nat → Bool)
    (k : Nat) : (Expr2.unary .lnot e).xfBits m env k = !XF.any w (e.xfBits m env) := by
  simp [Expr2.xfBits, h]

theorem xf_red {e : Expr2} {w : Nat} (op : RedOp) (h : e.xfWidth m = some w) :
    (Expr2.reduce op e).xfWidth m = some 1 := by
  simp [Expr2.xfWidth, h]

theorem xfb_red {e : Expr2} {w : Nat} (op : RedOp) (h : e.xfWidth m = some w)
    (env : String → Nat → Bool) (k : Nat) :
    (Expr2.reduce op e).xfBits m env k = XF.red op w (e.xfBits m env) := by
  simp [Expr2.xfBits, h]

theorem xf_logical {l r : Expr2} {wl wr : Nat} (b : Bool) (hl : l.xfWidth m = some wl)
    (hr : r.xfWidth m = some wr) : (Expr2.logical b l r).xfWidth m = some 1 := by
  simp [Expr2.xfWidth, hl, hr]

theorem xfb_land {l r : Expr2} {wl wr : Nat} (hl : l.xfWidth m = some wl)
    (hr : r.xfWidth m = some wr) (env : String → Nat → Bool) (k : Nat) :
    (Expr2.logical true l r).xfBits m env k =
      (XF.any wl (l.xfBits m env) && XF.any wr (r.xfBits m env)) := by
  simp [Expr2.xfBits, hl, hr]

theorem xfb_lor {l r : Expr2} {wl wr : Nat} (hl : l.xfWidth m = some wl)
    (hr : r.xfWidth m = some wr) (env : String → Nat → Bool) (k : Nat) :
    (Expr2.logical false l r).xfBits m env k =
      (XF.any wl (l.xfBits m env) || XF.any wr (r.xfBits m env)) := by
  simp [Expr2.xfBits, hl, hr]

theorem xf_tern {c t f : Expr2} {w : Nat} (hc : c.xfWidth m = some 1) (ht : t.xfWidth m = some w)
    (hf : f.xfWidth m = some w) : (Expr2.ternary c t f).xfWidth m = some w := by
  simp [Expr2.xfWidth, hc, ht, hf, XF.same]

theorem xfb_tern {c t f : Expr2} (hc : c.xfWidth m = some 1) (env : String → Nat → Bool)
    (k : Nat) : (Expr2.ternary c t f).xfBits m env k =
      if c.xfBits m env 0 = true then t.xfBits m env k else f.xfBits m env k := by
  simp [Expr2.xfBits, hc, XF.any_one]

theorem xf_eq {l r : Expr2} {w : Nat} (hl : l.xfWidth m = some w) (hr : r.xfWidth m = some w) :
    (Expr2.binary .eq l r).xfWidth m = some 1 := by
  simp [Expr2.xfWidth, hl, hr, XF.same]

theorem xf_ne {l r : Expr2} {w : Nat} (hl : l.xfWidth m = some w) (hr : r.xfWidth m = some w) :
    (Expr2.binary .ne l r).xfWidth m = some 1 := by
  simp [Expr2.xfWidth, hl, hr, XF.same]

theorem xfb_eq {l r : Expr2} {w : Nat} (hl : l.xfWidth m = some w) (env : String → Nat → Bool)
    (k : Nat) : (Expr2.binary .eq l r).xfBits m env k = XF.eqv w (l.xfBits m env) (r.xfBits m env) := by
  simp [Expr2.xfBits, hl]

theorem xfb_ne {l r : Expr2} {w : Nat} (hl : l.xfWidth m = some w) (env : String → Nat → Bool)
    (k : Nat) : (Expr2.binary .ne l r).xfBits m env k = !XF.eqv w (l.xfBits m env) (r.xfBits m env) := by
  simp [Expr2.xfBits, hl]

/-- Any comparison of two operands of one width is in the x-free fragment, one bit wide. -/
theorem xf_cmp (c : CmpOp) {l r : Expr2} {w : Nat} (hl : l.xfWidth m = some w) (hr : r.xfWidth m = some w) :
    (Expr2.binary c.ex l r).xfWidth m = some 1 := by
  cases c <;> simp [CmpOp.ex, Expr2.xfWidth, hl, hr, XF.same, XF.comb]

theorem xfb_lt {l r : Expr2} {w : Nat} (hl : l.xfWidth m = some w) (hr : r.xfWidth m = some w)
    (env : String → Nat → Bool) (k : Nat) :
    (Expr2.binary .lt l r).xfBits m env k = decide (XF.val (l.xfBits m env) w < XF.val (r.xfBits m env) w) := by
  simp [Expr2.xfBits, hl, hr]

theorem xfb_le {l r : Expr2} {w : Nat} (hl : l.xfWidth m = some w) (hr : r.xfWidth m = some w)
    (env : String → Nat → Bool) (k : Nat) :
    (Expr2.binary .le l r).xfBits m env k = decide (XF.val (l.xfBits m env) w ≤ XF.val (r.xfBits m env) w) := by
  simp [Expr2.xfBits, hl, hr]

theorem xfb_gt {l r : Expr2} {w : Nat} (hl : l.xfWidth m = some w) (hr : r.xfWidth m = some w)
    (env : String → Nat → Bool) (k : Nat) :
    (Expr2.binary .gt l r).xfBits m env k = decide (XF.val (l.xfBits m env) w > XF.val (r.xfBits m env) w) := by
  simp [Expr2.xfBits, hl, hr]

theorem xfb_ge {l r : Expr2} {w : Nat} (hl : l.xfWidth m = some w) (hr : r.xfWidth m = some w)
    (env : String → Nat → Bool) (k : Nat) :
    (Expr2.binary .ge l r).xfBits m env k = decide (XF.val (l.xfBits m env) w ≥ XF.val (r.xfBits m env) w) := by
  simp [Expr2.xfBits, hl, hr]

theorem sext_congr {wl : Nat} {f g : Nat → Bool} (h : ∀ j, j < wl → f j = g j) (k : Nat) :
    XF.sext wl f k = XF.sext wl g k := by
  unfold XF.sext
  by_cases hk : k < wl
  · simp [hk, h k hk]
  · by_cases h0 : 0 < wl
    · simp [hk, h0, h (wl - 1) (by omega)]
    · simp [hk, h0]

theorem shrBits_zext {wl lc wr : Nat} (hwl : wl ≤ lc) (f g : Nat → Bool) (k : Nat) :
    XF.shrBits lc (XF.zext wl f) wr g k = XF.shrBits wl f wr g k := by
  simp only [XF.shrBits, XF.zext]
  by_cases h : k + XF.val g wr < wl
  · have : k + XF.val g wr < lc := by omega
    simp [h, this]
  · simp [h]

/-- The left operand of a shift, extended to the context `lc ≥ wl` (`fitDivOperand2`): width `lc`, the zero extension
(`sg = false`) or the sign extension (`sg = true`). -/
theorem xf_shLeft (sg : Bool) {L0 : Expr2} {wl lc : Nat} {lbits : Nat → Bool} (env : String → Nat → Bool)
    (hlc : wl ≤ lc) (hw : L0.xfWidth m = some wl) (hb : ∀ k, k < wl → L0.xfBits m env k = lbits k) :
    (if lc = wl then L0 else if sg then Expr2.resizeSigned lc L0 else Expr2.resize lc L0).xfWidth m = some lc ∧
      ∀ k, k < lc → (if lc = wl then L0 else if sg then Expr2.resizeSigned lc L0 else Expr2.resize lc L0).xfBits m env k =
        (if sg then XF.sext wl lbits k else XF.zext wl lbits k) := by
  by_cases h : lc = wl
  · subst h
    simp only [if_true]
    refine ⟨hw, fun k hk => ?_⟩
    cases sg <;> simp [XF.zext, XF.sext, hk, hb k hk]
  · rw [if_neg h]
    cases sg
    · simp only [Bool.false_eq_true, if_false]
      refine ⟨by simp [Expr2.xfWidth, hw], fun k hk => ?_⟩
      by_cases hkl : k < wl
      · simp [Expr2.xfBits, hw, XF.zext, hkl, hb k hkl]
      · simp [Expr2.xfBits, hw, XF.zext, hkl]
    · simp only [if_true]
      refine ⟨by simp [Expr2.xfWidth, hw], fun k hk => ?_⟩
      simp only [Expr2.xfBits, hw, Option.getD_some, if_true]
      exact sext_congr hb k

/-- The shift itself, over an operand already extended to `lc` (bit function `lb`) and an amount of width `wr`. -/
theorem xf_shCore (d sg : Bool) {Lx R0 : Expr2} {wr lc : Nat} {lb rbits : Nat → Bool}
    (env : String → Nat → Bool) (hLw : Lx.xfWidth m = some lc)
    (hLb : ∀ k, k < lc → Lx.xfBits m env k = lb k)
    (hRw : R0.xfWidth m = some wr) (hRb : ∀ k, k < wr → R0.xfBits m env k = rbits k) :
    (Expr2.binary (if d then BinOp.shl sg else BinOp.shr sg) Lx R0).xfWidth m = some lc ∧
      ∀ k, k < lc → (Expr2.binary (if d then BinOp.shl sg else BinOp.shr sg) Lx R0).xfBits m env k =
        (if d then XF.shlBits lb wr rbits k else XF.shrBits lc lb wr rbits k) := by
  have hv : XF.val (R0.xfBits m env) wr = XF.val rbits wr := XF.val_congr_lt hRb
  cases d
  · refine ⟨by simp [Expr2.xfWidth, hLw, hRw, XF.comb], fun k hk => ?_⟩
    simp only [Bool.false_eq_true, if_false, Expr2.xfBits, hLw, hRw, Option.getD_some, XF.shrBits, hv]
    by_cases h1 : k + XF.val rbits wr < lc
    · rw [hLb _ h1]
    · simp [h1]
  · refine ⟨by simp [Expr2.xfWidth, hLw, hRw, XF.comb], fun k hk => ?_⟩
    simp only [if_true, Expr2.xfBits, hLw, hRw, Option.getD_some, XF.shlBits, hv]
    by_cases h1 : XF.val rbits wr ≤ k
    · rw [hLb _ (by omega)]
    · simp [h1]

/-- The context truncation `ctxTrunc2` of a shift (`lc = max tw wl ≥ tw`). -/
theorem xf_shFin {E : Expr2} {lc tw : Nat} {T : Nat → Bool} (env : String → Nat → Bool)
    (hlc : tw ≤ lc) (hEw : E.xfWidth m = some lc) (hEb : ∀ k, k < lc → E.xfBits m env k = T k) :
    (if lc ≤ tw then E else Expr2.resize tw E).xfWidth m = some tw ∧
      ∀ k, k < tw → (if lc ≤ tw then E else Expr2.resize tw E).xfBits m env k = T k := by
  by_cases h : lc ≤ tw
  · rw [if_pos h]
    have h2 : lc = tw := Nat.le_antisymm h hlc
    subst h2
    exact ⟨hEw, hEb⟩
  · rw [if_neg h]
    refine ⟨by simp [Expr2.xfWidth, hEw], fun k hk => ?_⟩
    simp [Expr2.xfBits, hEw, hEb k (by omega), show k < lc by omega]

end xfops

/-- **The lowered expression is in the x-free fragment at its width, and its Boolean bits are the skeleton's**
(both statements in one induction: the operands of the self-determined operators are lowered at their own
width, so the width is an argument of the recursion). -/
theorem low_xf_gen {m : Design2} {σ : String → Int} {dw : String → Nat} :
    ∀ (sk : Sk) (tw : Nat), sk.knownB = true → sk.WidthOk σ dw tw →
      (∀ a ∈ sk.leaves, LeafOk m σ dw a) → ∀ env : String → Nat → Bool,
      (sk.low σ dw tw).xfWidth m = some tw ∧
        ∀ k, k < tw → (sk.low σ dw tw).xfBits m env k = sk.bit σ dw env k
  | .lit v, tw, hk, hw, _, env => by
      simp only [Sk.knownB] at hk
      simp only [Sk.WidthOk] at hw
      exact ⟨by simp [Sk.low, Expr2.xfWidth, hk, hw], fun k _ => by simp [Sk.low, Sk.bit, Expr2.xfBits]⟩
  | .rd a, tw, _, hw, hL, env => by
      simp only [Sk.WidthOk] at hw
      exact ⟨by rw [Sk.low, expr_xfWidth (hL a (by simp [Sk.leaves])), hw],
        fun k _ => by simp [Sk.low, Sk.bit, expr_xfBits]⟩
  | .gate g l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      simp only [Sk.WidthOk] at hw
      obtain ⟨h1, b1⟩ := low_xf_gen l tw hk.1 hw.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      obtain ⟨h2, b2⟩ := low_xf_gen r tw hk.2 hw.2 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      refine ⟨by cases g <;> simp [Sk.low, Gate.op, Expr2.xfWidth, h1, h2, XF.same], fun k hk' => ?_⟩
      cases g <;> simp [Sk.low, Sk.bit, Gate.op, Expr2.xfBits, b1 k hk', b2 k hk']
  | .cat ps, tw, hk, hw, hL, env => by
      simp only [Sk.WidthOk] at hw
      obtain ⟨h1, h2⟩ := cat_low (m := m) (σ := σ) (dw := dw) env ps hk hL
      exact ⟨by simp [Sk.low, Expr2.xfWidth, h1, hw], fun k _ => by simp [Sk.low, Sk.bit, Expr2.xfBits, h2]⟩
  | .rep p, tw, hk, hw, hL, env => by
      simp only [Sk.WidthOk] at hw
      obtain ⟨h1, h2⟩ := part_low (m := m) (σ := σ) (dw := dw) env p hk (by simpa [Sk.leaves] using hL)
      exact ⟨by simp [Sk.low, h1, hw], fun k _ => by simp [Sk.low, Sk.bit, h2]⟩
  | .fill b, tw, hk, hw, _, env => by
      simp only [Sk.knownB] at hk
      have hknown : (LVec.replicate tw b).knownB = true := by
        simp [LVec.knownB, LVec.replicate, hk]
      refine ⟨?_, fun k hk' => by simp [Sk.low, Sk.bit, Expr2.xfBits, LVec.boolAt, LVec.replicate, hk']⟩
      simp only [Sk.low, Expr2.xfWidth, hknown, if_true]
      simp [LVec.width, LVec.replicate]
  | .bnot a, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      simp only [Sk.WidthOk] at hw
      obtain ⟨h1, b1⟩ := low_xf_gen a tw hk hw (fun x hx => hL x (by simpa [Sk.leaves] using hx)) env
      exact ⟨by simp [Sk.low, Expr2.xfWidth, h1], fun k hk' => by
        simp [Sk.low, Sk.bit, Expr2.xfBits, b1 k hk']⟩
  | .lnot a, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      obtain ⟨rfl, hsa⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_gen a _ hk (Sk.selfOk_widthOk σ dw a hsa)
        (fun x hx => hL x (by simpa [Sk.leaves] using hx)) env
      rw [Sk.low_irrel σ dw a hsa _ 0] at h1 b1
      refine ⟨xf_lnot h1, fun k _ => ?_⟩
      simp only [Sk.low, Sk.bit]
      rw [xfb_lnot h1, XF.any_congr b1]
  | .red op a, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      obtain ⟨rfl, hsa⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_gen a _ hk (Sk.selfOk_widthOk σ dw a hsa)
        (fun x hx => hL x (by simpa [Sk.leaves] using hx)) env
      rw [Sk.low_irrel σ dw a hsa _ 0] at h1 b1
      refine ⟨xf_red op h1, fun k _ => ?_⟩
      simp only [Sk.low, Sk.bit]
      rw [xfb_red op h1, XF.red_congr op b1]
  | .land l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      obtain ⟨rfl, hsl, hsr⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_gen l _ hk.1 (Sk.selfOk_widthOk σ dw l hsl)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := low_xf_gen r _ hk.2 (Sk.selfOk_widthOk σ dw r hsr)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      rw [Sk.low_irrel σ dw l hsl _ 0] at h1 b1
      rw [Sk.low_irrel σ dw r hsr _ 0] at h2 b2
      refine ⟨xf_logical true h1 h2, fun k _ => ?_⟩
      simp only [Sk.low, Sk.bit]
      rw [xfb_land h1 h2, XF.any_congr b1, XF.any_congr b2]
  | .lor l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      obtain ⟨rfl, hsl, hsr⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_gen l _ hk.1 (Sk.selfOk_widthOk σ dw l hsl)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := low_xf_gen r _ hk.2 (Sk.selfOk_widthOk σ dw r hsr)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      rw [Sk.low_irrel σ dw l hsl _ 0] at h1 b1
      rw [Sk.low_irrel σ dw r hsr _ 0] at h2 b2
      refine ⟨xf_logical false h1 h2, fun k _ => ?_⟩
      simp only [Sk.low, Sk.bit]
      rw [xfb_lor h1 h2, XF.any_congr b1, XF.any_congr b2]
  | .tern c a b, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      obtain ⟨hsc, hwc, hwa, hwb⟩ := hw
      have hc1 : c.WidthOk σ dw 1 := by
        have := Sk.selfOk_widthOk σ dw c hsc
        rwa [hwc] at this
      obtain ⟨h1, b1⟩ := low_xf_gen c 1 hk.1.1 hc1
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := low_xf_gen a tw hk.1.2 hwa (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h3, b3⟩ := low_xf_gen b tw hk.2 hwb (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      rw [Sk.low_irrel σ dw c hsc 1 0] at h1 b1
      refine ⟨xf_tern h1 h2 h3, fun k hk' => ?_⟩
      simp only [Sk.low, Sk.bit]
      rw [xfb_tern h1, b1 0 (by omega), b2 k hk', b3 k hk']
  | .cmp op l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      obtain ⟨rfl, hsl, hsr, hwe⟩ := hw
      have hm : max (l.width σ dw) (r.width σ dw) = l.width σ dw := by
        rw [← hwe]; exact Nat.max_self _
      obtain ⟨h1, b1⟩ := low_xf_gen l _ hk.1 (Sk.selfOk_widthOk σ dw l hsl)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := low_xf_gen r _ hk.2 (Sk.selfOk_widthOk σ dw r hsr)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      rw [← hwe] at h2 b2
      refine ⟨by simp only [Sk.low, hm]; exact xf_cmp op h1 h2, fun k _ => ?_⟩
      cases op <;> simp only [Sk.low, Sk.bit, hm, CmpOp.ex]
      · rw [xfb_eq h1, XF.eqv_congr b1 b2]
      · rw [xfb_ne h1, XF.eqv_congr b1 b2]
      · rw [xfb_lt h1 h2, XF.val_congr_lt b1, XF.val_congr_lt b2]
      · rw [xfb_le h1 h2, XF.val_congr_lt b1, XF.val_congr_lt b2]
      · rw [xfb_gt h1 h2, XF.val_congr_lt b1, XF.val_congr_lt b2]
      · rw [xfb_ge h1 h2, XF.val_congr_lt b1, XF.val_congr_lt b2]
  -- the word-level nodes are outside the v1 width contract (`low_xf_genC` reads them)
  | .ext _, _, _, hw, _, _ => by simp [Sk.WidthOk] at hw
  | .add _ _, _, _, hw, _, _ => by simp [Sk.WidthOk] at hw
  | .sub _ _, _, _, hw, _, _ => by simp [Sk.WidthOk] at hw
  | .mul _ _, _, _, hw, _, _ => by simp [Sk.WidthOk] at hw

/-- **The lowered right-hand side is in the x-free fragment at the target width.** -/
theorem low_xfWidth {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat} :
    ∀ (sk : Sk), sk.knownB = true → sk.WidthOk σ dw tw → (∀ a ∈ sk.leaves, LeafOk m σ dw a) →
      (sk.low σ dw tw).xfWidth m = some tw :=
  fun sk hk hw hL => (low_xf_gen sk tw hk hw hL (fun _ _ => false)).1

/-- **… and its `Expr2.xfBits` is the skeleton's Boolean reading** (below the target width). -/
theorem low_xfBits {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat}
    (env : String → Nat → Bool) :
    ∀ (sk : Sk), sk.knownB = true → sk.WidthOk σ dw tw → (∀ a ∈ sk.leaves, LeafOk m σ dw a) →
      ∀ k, k < tw → (sk.low σ dw tw).xfBits m env k = sk.bit σ dw env k :=
  fun sk hk hw hL => (low_xf_gen sk tw hk hw hL env).2

/-! ### WP-B2: the word-level nodes in the x-free fragment -/

/-- An unsized constant lowers to an x-free literal of the context width. -/
theorem xf_lit_ofInt (m : Design2) (tw : Nat) (v : Int) :
    (Expr2.lit (LVec.ofInt tw v)).xfWidth m = some tw ∧
      ∀ (env : String → Nat → Bool) (k : Nat), k < tw →
        (Expr2.lit (LVec.ofInt tw v)).xfBits m env k = XF.constBit v tw k := by
  have hk : (LVec.ofInt tw v).knownB = true := by
    rw [LVec.knownB_eq_allKnown]; unfold LVec.ofInt; exact LVec.allKnown_ofNat _ _
  refine ⟨?_, fun env k hk' => ?_⟩
  · rw [Expr2.xfWidth, if_pos hk]
    congr 1
    unfold LVec.ofInt
    exact LVec.width_ofNat _ _
  simp only [Expr2.xfBits]
  unfold LVec.ofInt XF.constBit
  rw [LVec.ofNat_eq_ofBoolFn, LVec.boolAt_ofBoolFn _ hk']

/-- The part under a marker (a literal or one access) at its own width, for every bit. -/
theorem part_xf {m : Design2} {σ : String → Int} {dw : String → Nat} (p : Part)
    (hk : partKnown [p] = true) (hL : ∀ x ∈ partLeaves [p], LeafOk m σ dw x)
    (env : String → Nat → Bool) :
    (p.expr σ).xfWidth m = some (p.wid σ dw) ∧ ∀ k, (p.expr σ).xfBits m env k = p.bit σ env k :=
  part_low env p hk hL

/-- **The lowered expression is in the x-free fragment at the context width, and its Boolean bits are the
word-level reading** (`Sk.bitC`): markers are zero extensions, `+ -` read the context width. The self-determined
operands are v1 skeletons: the v1 theorem `low_xf_gen`. -/
theorem low_xf_genC {m : Design2} {σ : String → Int} {dw : String → Nat} :
    ∀ (sk : Sk) (tw : Nat), sk.knownB = true → sk.WidthOkC σ dw tw →
      (∀ a ∈ sk.leaves, LeafOk m σ dw a) → ∀ env : String → Nat → Bool,
      (sk.low σ dw tw).xfWidth m = some tw ∧
        ∀ k, k < tw → (sk.low σ dw tw).xfBits m env k = sk.bitC σ dw tw env k
  | .lit v, tw, hk, hw, _, env => by
      simp only [Sk.knownB] at hk
      simp only [Sk.WidthOkC] at hw
      exact ⟨by simp [Sk.low, Expr2.xfWidth, hk, hw], fun k _ => by simp [Sk.low, Sk.bitC, Expr2.xfBits]⟩
  | .rd a, tw, _, hw, hL, env => by
      simp only [Sk.WidthOkC] at hw
      exact ⟨by rw [Sk.low, expr_xfWidth (hL a (by simp [Sk.leaves])), hw],
        fun k _ => by simp [Sk.low, Sk.bitC, expr_xfBits]⟩
  | .gate g l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, b1⟩ := low_xf_genC l tw hk.1 hw.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      obtain ⟨h2, b2⟩ := low_xf_genC r tw hk.2 hw.2 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      refine ⟨by cases g <;> simp [Sk.low, Gate.op, Expr2.xfWidth, h1, h2, XF.same], fun k hk' => ?_⟩
      cases g <;> simp [Sk.low, Sk.bitC, Gate.op, Expr2.xfBits, b1 k hk', b2 k hk']
  | .cat ps, tw, hk, hw, hL, env => by
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, h2⟩ := cat_low (m := m) (σ := σ) (dw := dw) env ps hk hL
      exact ⟨by simp [Sk.low, Expr2.xfWidth, h1, hw], fun k _ => by simp [Sk.low, Sk.bitC, Expr2.xfBits, h2]⟩
  | .rep p, tw, hk, hw, hL, env => by
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, h2⟩ := part_low (m := m) (σ := σ) (dw := dw) env p hk (by simpa [Sk.leaves] using hL)
      exact ⟨by simp [Sk.low, h1, hw], fun k _ => by simp [Sk.low, Sk.bitC, h2]⟩
  | .fill b, tw, hk, hw, _, env => by
      simp only [Sk.knownB] at hk
      have hknown : (LVec.replicate tw b).knownB = true := by
        simp [LVec.knownB, LVec.replicate, hk]
      refine ⟨?_, fun k hk' => by simp [Sk.low, Sk.bitC, Expr2.xfBits, LVec.boolAt, LVec.replicate, hk']⟩
      simp only [Sk.low, Expr2.xfWidth, hknown, if_true]
      simp [LVec.width, LVec.replicate]
  | .bnot a, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, b1⟩ := low_xf_genC a tw hk hw.1 (fun x hx => hL x (by simpa [Sk.leaves] using hx)) env
      exact ⟨by simp [Sk.low, Expr2.xfWidth, h1], fun k hk' => by
        simp [Sk.low, Sk.bitC, Expr2.xfBits, b1 k hk']⟩
  | .lnot a, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      obtain ⟨rfl, hsa⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_gen a _ hk (Sk.selfOk_widthOk σ dw a hsa)
        (fun x hx => hL x (by simpa [Sk.leaves] using hx)) env
      rw [Sk.low_irrel σ dw a hsa _ 0] at h1 b1
      refine ⟨xf_lnot h1, fun k _ => ?_⟩
      simp only [Sk.low, Sk.bitC]
      rw [funext (Sk.bitC_of_selfOk σ dw env a hsa (a.width σ dw))]
      rw [xfb_lnot h1, XF.any_congr b1]
  | .red op a, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      obtain ⟨rfl, hsa⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_gen a _ hk (Sk.selfOk_widthOk σ dw a hsa)
        (fun x hx => hL x (by simpa [Sk.leaves] using hx)) env
      rw [Sk.low_irrel σ dw a hsa _ 0] at h1 b1
      refine ⟨xf_red op h1, fun k _ => ?_⟩
      simp only [Sk.low, Sk.bitC]
      rw [funext (Sk.bitC_of_selfOk σ dw env a hsa (a.width σ dw))]
      rw [xfb_red op h1, XF.red_congr op b1]
  | .land l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      obtain ⟨rfl, hsl, hsr⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_gen l _ hk.1 (Sk.selfOk_widthOk σ dw l hsl)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := low_xf_gen r _ hk.2 (Sk.selfOk_widthOk σ dw r hsr)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      rw [Sk.low_irrel σ dw l hsl _ 0] at h1 b1
      rw [Sk.low_irrel σ dw r hsr _ 0] at h2 b2
      refine ⟨xf_logical true h1 h2, fun k _ => ?_⟩
      simp only [Sk.low, Sk.bitC]
      rw [funext (Sk.bitC_of_selfOk σ dw env l hsl (l.width σ dw)),
        funext (Sk.bitC_of_selfOk σ dw env r hsr (r.width σ dw))]
      rw [xfb_land h1 h2, XF.any_congr b1, XF.any_congr b2]
  | .lor l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      obtain ⟨rfl, hsl, hsr⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_gen l _ hk.1 (Sk.selfOk_widthOk σ dw l hsl)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := low_xf_gen r _ hk.2 (Sk.selfOk_widthOk σ dw r hsr)
        (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      rw [Sk.low_irrel σ dw l hsl _ 0] at h1 b1
      rw [Sk.low_irrel σ dw r hsr _ 0] at h2 b2
      refine ⟨xf_logical false h1 h2, fun k _ => ?_⟩
      simp only [Sk.low, Sk.bitC]
      rw [funext (Sk.bitC_of_selfOk σ dw env l hsl (l.width σ dw)),
        funext (Sk.bitC_of_selfOk σ dw env r hsr (r.width σ dw))]
      rw [xfb_lor h1 h2, XF.any_congr b1, XF.any_congr b2]
  | .tern c a b, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      obtain ⟨hsc, hwc, hwa, hwb⟩ := hw
      have hc1 : c.WidthOk σ dw 1 := by
        have := Sk.selfOk_widthOk σ dw c hsc
        rwa [hwc] at this
      obtain ⟨h1, b1⟩ := low_xf_gen c 1 hk.1.1 hc1 (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := low_xf_genC a tw hk.1.2 hwa (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h3, b3⟩ := low_xf_genC b tw hk.2 hwb (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      rw [Sk.low_irrel σ dw c hsc 1 0] at h1 b1
      refine ⟨xf_tern h1 h2 h3, fun k hk' => ?_⟩
      simp only [Sk.low, Sk.bitC]
      rw [Sk.bitC_of_selfOk σ dw env c hsc 1 0]
      rw [xfb_tern h1, b1 0 (by omega), b2 k hk', b3 k hk']
  | .cmp op l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      obtain ⟨rfl, hwl, hwr⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_genC l _ hk.1 hwl (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := low_xf_genC r _ hk.2 hwr (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      refine ⟨by simp only [Sk.low]; exact xf_cmp op h1 h2, fun k _ => ?_⟩
      cases op <;> simp only [Sk.low, Sk.bitC, CmpOp.ex]
      · rw [xfb_eq h1, XF.eqv_congr b1 b2]
      · rw [xfb_ne h1, XF.eqv_congr b1 b2]
      · rw [xfb_lt h1 h2, XF.val_congr_lt b1, XF.val_congr_lt b2]
      · rw [xfb_le h1 h2, XF.val_congr_lt b1, XF.val_congr_lt b2]
      · rw [xfb_gt h1 h2, XF.val_congr_lt b1, XF.val_congr_lt b2]
      · rw [xfb_ge h1 h2, XF.val_congr_lt b1, XF.val_congr_lt b2]
  | .ext p, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, h2⟩ := part_xf p hk hL env
      refine ⟨by simp [Sk.low, Expr2.xfWidth, h1], fun k _ => ?_⟩
      simp [Sk.low, Sk.bitC, Expr2.xfBits, h1, h2, XF.zext]
  | .add l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, b1⟩ := low_xf_genC l tw hk.1 hw.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      obtain ⟨h2, b2⟩ := low_xf_genC r tw hk.2 hw.2.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      refine ⟨by simp [Sk.low, Expr2.xfWidth, h1, h2, XF.comb], fun k _ => ?_⟩
      simp only [Sk.low, Sk.bitC, Expr2.xfBits, h1, h2, Option.getD_some]
      exact XF.addBits_congr b1 b2 k
  | .sub l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, b1⟩ := low_xf_genC l tw hk.1 hw.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      obtain ⟨h2, b2⟩ := low_xf_genC r tw hk.2 hw.2.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      refine ⟨by simp [Sk.low, Expr2.xfWidth, h1, h2, XF.comb], fun k _ => ?_⟩
      simp only [Sk.low, Sk.bitC, Expr2.xfBits, h1, h2, Option.getD_some]
      exact XF.subBits_congr b1 b2 k
  | .mul l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, b1⟩ := low_xf_genC l tw hk.1 hw.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      obtain ⟨h2, b2⟩ := low_xf_genC r tw hk.2 hw.2.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      refine ⟨by simp [Sk.low, Expr2.xfWidth, h1, h2, XF.comb], fun k _ => ?_⟩
      simp only [Sk.low, Sk.bitC, Expr2.xfBits, h1, h2, Option.getD_some]
      exact XF.mulBits_congr b1 b2 k

  | .const v, tw, hk, hw, hL, env => by
      obtain ⟨h1, b1⟩ := xf_lit_ofInt m tw v
      exact ⟨by simpa [Sk.low] using h1, fun k hk' => by simpa [Sk.low, Sk.bitC] using b1 env k hk'⟩
  | .cref a, tw, hk, hw, hL, env => by
      obtain ⟨h1, b1⟩ := xf_lit_ofInt m tw (a.eval σ)
      exact ⟨by simpa [Sk.low] using h1, fun k hk' => by simpa [Sk.low, Sk.bitC] using b1 env k hk'⟩
  | .sh d sg l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      simp only [Sk.WidthOkC] at hw
      obtain ⟨hlw, hlb⟩ := low_xf_genC l (l.width σ dw) hk.1 hw.1 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      obtain ⟨hrw, hrb⟩ := low_xf_genC r (r.width σ dw) hk.2 hw.2 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      have hlc : l.width σ dw ≤ max tw (l.width σ dw) := Nat.le_max_right _ _
      obtain ⟨hLw, hLb⟩ := xf_shLeft sg (lc := max tw (l.width σ dw)) env hlc hlw hlb
      obtain ⟨hEw, hEb⟩ := xf_shCore d sg env hLw hLb hrw hrb
      have h := xf_shFin (tw := tw) env (Nat.le_max_left _ _) hEw hEb
      simp only [Sk.low]
      refine ⟨h.1, fun k hk' => ?_⟩
      rw [h.2 k hk']
      cases d <;> cases sg <;> simp [Sk.bitC, shrBits_zext hlc]
  | .rsz pr p, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      have hLp : ∀ x ∈ p.leaves, LeafOk m σ dw x := fun x hx => hL x (by simpa [Sk.leaves] using hx)
      have trunc : p.WidthOkC σ dw (p.width σ dw) →
          ((Sk.rsz false p).low σ dw tw).xfWidth m = some tw ∧
            ∀ k, k < tw → ((Sk.rsz false p).low σ dw tw).xfBits m env k =
              (Sk.rsz false p).bitC σ dw tw env k := by
        intro hwp
        obtain ⟨h1, b1⟩ := low_xf_genC p (p.width σ dw) hk hwp hLp env
        simp only [Sk.low, Sk.bitC]
        refine ⟨by simp [Expr2.xfWidth, h1], fun k hk' => ?_⟩
        by_cases hkp : k < p.width σ dw
        · simp [Expr2.xfBits, h1, XF.zext, hkp, b1 k hkp]
        · simp [Expr2.xfBits, h1, XF.zext, hkp]
      cases pr
      · simp only [Sk.WidthOkC] at hw
        exact trunc hw
      · simp only [Sk.WidthOkC] at hw
        by_cases hc : p.width σ dw < tw
        · rw [if_pos hc] at hw
          have := low_xf_genC p tw hk hw hLp env
          simp only [Sk.low, Sk.bitC, if_pos hc]
          exact this
        · rw [if_neg hc] at hw
          have := trunc hw
          simp only [Sk.low, Sk.bitC, if_neg hc]
          simpa [Sk.low, Sk.bitC] using this

/-- **The lowered right-hand side is in the x-free fragment at the target width** (word-level contract). -/
theorem low_xfWidthC {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat} :
    ∀ (sk : Sk), sk.knownB = true → sk.WidthOkC σ dw tw → (∀ a ∈ sk.leaves, LeafOk m σ dw a) →
      (sk.low σ dw tw).xfWidth m = some tw :=
  fun sk hk hw hL => (low_xf_genC sk tw hk hw hL (fun _ _ => false)).1

/-- … and its `Expr2.xfBits` is the word-level reading (below the target width). -/
theorem low_xfBitsC {m : Design2} {σ : String → Int} {dw : String → Nat} {tw : Nat}
    (env : String → Nat → Bool) :
    ∀ (sk : Sk), sk.knownB = true → sk.WidthOkC σ dw tw → (∀ a ∈ sk.leaves, LeafOk m σ dw a) →
      ∀ k, k < tw → (sk.low σ dw tw).xfBits m env k = sk.bitC σ dw tw env k :=
  fun sk hk hw hL => (low_xf_genC sk tw hk hw hL env).2

/-! ## Axiom pins -/

/-- info: 'LeanModels.Sv.CombEq.low_xfWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_xfWidth

/-- info: 'LeanModels.Sv.CombEq.low_xfBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_xfBits

/-- info: 'LeanModels.Sv.CombEq.skT_shapeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms skT_shapeC

/-- info: 'LeanModels.Sv.CombEq.proc_shapeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proc_shapeC

/-- info: 'LeanModels.Sv.CombEq.low_xfWidthC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_xfWidthC

/-- info: 'LeanModels.Sv.CombEq.low_xfBitsC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_xfBitsC

/-- info: 'LeanModels.Sv.CombEq.ie_resize_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ie_resize_leaf

end CombEq
end LeanModels.Sv
