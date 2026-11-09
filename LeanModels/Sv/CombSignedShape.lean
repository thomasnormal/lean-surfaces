import LeanModels.Sv.CombEqShape

/-!
# Signed reads in the shape theorems of `sv_equations`

A signed read is the envelope's cast marker around the identifier, `PExpr.cast true (.ident n)` (`CombView.lean`,
"Signed reads: the unsigned twin of a design"). The marker is transparent to every width function and to `instExpr2`
(its cast arm is the identity), and it changes `fitExpr2` in one case only: an operand narrower than its context
(`Resize:signed`, loud). Under the width contract of `sv_equations` (`Sk.WidthOkC`: a bare access is EXACTLY as wide
as its context) that case never arises. So the shape theorems of `CombEqShape.lean` hold for an expression `v` whose
unsigned twin `v.unsign` the recognizer accepts, with the skeleton of the twin, word for word: this file restates them
for such `v` (suffix `U`) and proves them by the same induction, the recognizer and the skeleton read on `v.unsign`,
the instantiation on `v`. The originals are the special case `v.unsign = v` (`unsign_of_rdsOfW`).

`proc_shapeCU` is the result the bridge to the design as written uses (`CombSigned.lean`): a process and its
unsigned twin instantiate to the same assign.
-/

namespace LeanModels.Sv
namespace CombEq
open CombView

/-! ## The cast marker is transparent -/

section cast
variable {E : IEnv} {elems : List (String × Nat)}

theorem selfWidth2_castU (s : Bool) (a : PExpr) : selfWidth2 E elems (.cast s a) = selfWidth2 E elems a := by
  simp [selfWidth2]

theorem rigidMax2_castU (s : Bool) (a : PExpr) : rigidMax2 E elems (.cast s a) = rigidMax2 E elems a := by
  simp [rigidMax2]

theorem instExpr2_castU (ctx : Option Nat) (s : Bool) (a : PExpr) :
    instExpr2 E elems ctx (.cast s a) = instExpr2 E elems ctx a := by
  simp [instExpr2]

end cast

/-! ## Recognizer inversions through `PExpr.unsign` -/

theorem unsign_unary (op : SymUnaryOp) (a : PExpr) : (PExpr.unary op a).unsign = .unary op a.unsign := by
  simp [PExpr.unsign]

theorem unsign_ternary (c t e : PExpr) : (PExpr.ternary c t e).unsign = .ternary c.unsign t.unsign e.unsign := by
  simp [PExpr.unsign]

theorem unsign_reduce (op : RedOp) (a : PExpr) : (PExpr.reduce op a).unsign = .reduce op a.unsign := by
  simp [PExpr.unsign]

theorem unsign_concat (ps : List PExpr) : (PExpr.concat ps).unsign = .concat (PExpr.unsignL ps) := by
  simp [PExpr.unsign]

theorem unsign_repl (c a : PExpr) : (PExpr.repl c a).unsign = .repl c a.unsign := by
  simp [PExpr.unsign]

theorem unsign_resize (m : Nat) (a : PExpr) : (PExpr.resize m a).unsign = .resize m a.unsign := by
  simp [PExpr.unsign]

theorem unsignL_cons (p : PExpr) (ps : List PExpr) : PExpr.unsignL (p :: ps) = p.unsign :: PExpr.unsignL ps := by
  simp [PExpr.unsignL]

/-- A leaf whose unsigned twin the leaf recognizer accepts: the leaf itself, or a signed read of an identifier. -/
theorem leafRd_unsign {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e.unsign = .ok a) :
    leafRd? ds e = .ok a ∨ ∃ n, e = .cast true (.ident n) ∧ leafRd? ds (.ident n) = .ok a := by
  cases e with
  | cast s x =>
      cases s with
      | true =>
          cases x with
          | ident n => exact Or.inr ⟨n, rfl, h⟩
          | _ => simp [PExpr.unsign, leafRd?] at h
      | false => simp [PExpr.unsign, leafRd?] at h
  | binary op l r =>
      cases hu : unsignOp op
      · rw [unsign_binary_f hu] at h; simp [leafRd?] at h
      · rw [unsign_binary_t hu] at h; simp [leafRd?] at h
  | unary op x => rw [unsign_unary] at h; simp [leafRd?] at h
  | ternary c t x => rw [unsign_ternary] at h; simp [leafRd?] at h
  | reduce op x => rw [unsign_reduce] at h; simp [leafRd?] at h
  | concat ps => rw [unsign_concat] at h; simp [leafRd?] at h
  | repl c x => rw [unsign_repl] at h; simp [leafRd?] at h
  | resize m x => rw [unsign_resize] at h; simp [leafRd?] at h
  | _ => exact Or.inl h

theorem rdsLeaf_unsign {ds : List DeclT} {e : PExpr} {rs : List Acc} (h : rdsLeaf? ds e.unsign = .ok rs) :
    ∃ a, leafRd? ds e.unsign = .ok a ∧ rs = [a] :=
  rdsLeaf_cases h

theorem leaf_flagsU {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e.unsign = .ok a) :
    e.ctxPropagates = false ∧ e.constLeaf = false ∧
      ∀ (env : IEnv) (m w : Nat), (PExpr.resize m e).negGenvarWidened env w = none := by
  rcases leafRd_unsign h with h' | ⟨n, rfl, -⟩
  · exact leaf_flags h'
  · exact ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem leafU_ne_lit {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e.unsign = .ok a) :
    ∀ v, e ≠ .lit v := by
  rintro v rfl; simp [PExpr.unsign, leafRd?] at h

theorem leafU_ne_repl {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e.unsign = .ok a) :
    ∀ c x, e ≠ .repl c x := by
  rintro c x rfl; rw [unsign_repl] at h; simp [leafRd?] at h


/-! ## Inversions of `PExpr.unsign` -/

theorem unsign_lit (v : LVec) : (PExpr.lit v).unsign = .lit v := by simp [PExpr.unsign]

theorem unsign_int (k : Int) : (PExpr.int k).unsign = .int k := by simp [PExpr.unsign]

theorem unsign_eq_lit {e : PExpr} {v : LVec} (h : e.unsign = .lit v) : e = .lit v := by
  cases e with
  | lit w => simpa [PExpr.unsign] using h
  | cast s x =>
      cases s <;> cases x <;> simp [PExpr.unsign] at h
  | binary op l r =>
      cases hu : unsignOp op
      · rw [unsign_binary_f hu] at h; cases h
      · rw [unsign_binary_t hu] at h; cases h
  | unary => simp [PExpr.unsign] at h
  | ternary => simp [PExpr.unsign] at h
  | reduce => simp [PExpr.unsign] at h
  | concat => simp [PExpr.unsign] at h
  | repl => simp [PExpr.unsign] at h
  | resize => simp [PExpr.unsign] at h
  | _ => simp [PExpr.unsign] at h

theorem unsign_eq_fill {e : PExpr} {b : Logic} (h : e.unsign = .fill b) : e = .fill b := by
  cases e with
  | fill c => simpa [PExpr.unsign] using h
  | cast s x =>
      cases s <;> cases x <;> simp [PExpr.unsign] at h
  | binary op l r =>
      cases hu : unsignOp op
      · rw [unsign_binary_f hu] at h; cases h
      · rw [unsign_binary_t hu] at h; cases h
  | unary => simp [PExpr.unsign] at h
  | ternary => simp [PExpr.unsign] at h
  | reduce => simp [PExpr.unsign] at h
  | concat => simp [PExpr.unsign] at h
  | repl => simp [PExpr.unsign] at h
  | resize => simp [PExpr.unsign] at h
  | _ => simp [PExpr.unsign] at h

theorem unsign_eq_concat1 {e x : PExpr} (h : e.unsign = .concat [x]) :
    ∃ e', e = .concat [e'] ∧ e'.unsign = x := by
  cases e with
  | concat ps =>
      rw [unsign_concat] at h
      cases ps with
      | nil => simp [PExpr.unsignL] at h
      | cons p ps =>
          cases ps with
          | nil => exact ⟨p, rfl, by simpa [PExpr.unsignL] using h⟩
          | cons q qs => simp [PExpr.unsignL] at h
  | cast s y =>
      cases s <;> cases y <;> simp [PExpr.unsign] at h
  | binary op l r =>
      cases hu : unsignOp op
      · rw [unsign_binary_f hu] at h; cases h
      · rw [unsign_binary_t hu] at h; cases h
  | unary => simp [PExpr.unsign] at h
  | ternary => simp [PExpr.unsign] at h
  | reduce => simp [PExpr.unsign] at h
  | repl => simp [PExpr.unsign] at h
  | resize => simp [PExpr.unsign] at h
  | _ => simp [PExpr.unsign] at h

theorem unsign_eq_repl {e c a : PExpr} (h : e.unsign = .repl c a) : ∃ a', e = .repl c a' ∧ a'.unsign = a := by
  cases e with
  | repl c' a' =>
      rw [unsign_repl] at h
      cases h
      exact ⟨a', rfl, rfl⟩
  | cast s y =>
      cases s <;> cases y <;> simp [PExpr.unsign] at h
  | binary op l r =>
      cases hu : unsignOp op
      · rw [unsign_binary_f hu] at h; cases h
      · rw [unsign_binary_t hu] at h; cases h
  | unary => simp [PExpr.unsign] at h
  | ternary => simp [PExpr.unsign] at h
  | reduce => simp [PExpr.unsign] at h
  | concat => simp [PExpr.unsign] at h
  | resize => simp [PExpr.unsign] at h
  | _ => simp [PExpr.unsign] at h

theorem unsign_isOpW (e : PExpr) : e.unsign.isOpW = e.isOpW := by
  cases e with
  | cast s y => cases s <;> cases y <;> rfl
  | binary op l r =>
      cases hu : unsignOp op
      · rw [unsign_binary_f hu]
      · rw [unsign_binary_t hu]; rfl
  | unary => rfl
  | ternary => rfl
  | reduce => rfl
  | concat => rfl
  | repl => rfl
  | resize => rfl
  | _ => rfl

theorem unsign_ctxPropagates {e : PExpr} (h : e.isOpW = true) : e.unsign.ctxPropagates = e.ctxPropagates := by
  cases e with
  | binary op l r =>
      cases hu : unsignOp op
      · rw [unsign_binary_f hu]
      · rw [unsign_binary_t hu]; rfl
  | unary op a =>
      rw [unsign_unary]
      cases op with
      | m0 u => cases u <;> rfl
      | _ => rfl
  | ternary c t x => rw [unsign_ternary]; rfl
  | reduce op a => rw [unsign_reduce]; rfl
  | concat ps => rw [unsign_concat]; rfl
  | int k => rw [unsign_int]
  | _ => simp [PExpr.isOpW] at h

theorem sigOpd_of_unsign {e : PExpr} (h : sigOpd e.unsign = true) : sigOpd e = true := by
  cases e with
  | cast s y => cases s <;> cases y <;> simp_all [PExpr.unsign, sigOpd]
  | resize m a =>
      rw [unsign_resize] at h
      cases a with
      | cast s y => cases s <;> cases y <;> simp_all [PExpr.unsign, sigOpd]
      | binary op l r =>
          cases hu : unsignOp op
          · rw [unsign_binary_f hu] at h; simp [sigOpd] at h
          · rw [unsign_binary_t hu] at h; simp [sigOpd] at h
      | _ => simp_all [PExpr.unsign, sigOpd]
  | binary op l r =>
      cases hu : unsignOp op
      · rw [unsign_binary_f hu] at h; simp [sigOpd] at h
      · rw [unsign_binary_t hu] at h; simp [sigOpd] at h
  | _ => simp_all [PExpr.unsign, sigOpd]

theorem sigOpd_or_of_unsign {l r : PExpr} (h : (sigOpd l.unsign || sigOpd r.unsign) = true) :
    (sigOpd l || sigOpd r) = true := by
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · simp [sigOpd_of_unsign h']
  · simp [sigOpd_of_unsign h']

section leaf
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- `leaf_eq` for a leaf whose unsigned twin is accepted. -/
theorem leaf_eqU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e.unsign = .ok a) (ha : AccOK σ DW DG EW ns a) :
    selfWidth2 E elems e = some (a.win σ dw).2.2 ∧ (∀ ctx, instExpr2 E elems ctx e = accExpr σ a) ∧
      rigidExpr e = true := by
  rcases leafRd_unsign h with h' | ⟨n, rfl, h'⟩
  · exact leaf_eq C hdw h' ha
  · obtain ⟨h1, h2, h3⟩ := leaf_eq C hdw h' ha
    exact ⟨by rw [selfWidth2_castU]; exact h1, fun ctx => by rw [instExpr2_castU]; exact h2 ctx, h3⟩

/-- `leaf_fit` for a leaf whose unsigned twin is accepted: at its own width the marker of a signed read is no
widening. -/
theorem leaf_fitU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e.unsign = .ok a)
    (ha : AccOK σ DW DG EW ns a) {tw : Nat} (hw : (a.win σ dw).2.2 = tw) :
    fitExpr2 E elems (some tw) e = accExpr σ a := by
  obtain ⟨hsw, hin, hrig⟩ := leaf_eqU C hdw h ha
  rw [fitExpr2_of_rigid_eq hrig (by rw [hsw, hw]), hin]

theorem rm_leafU {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e.unsign = .ok a) :
    rigidMax2 E elems e = selfWidth2 E elems e := by
  rcases leafRd_unsign h with h' | ⟨n, rfl, h'⟩
  · exact rm_leaf h'
  · rw [rigidMax2_castU, selfWidth2_castU]; exact rm_leaf h'

theorem ie_resize_leafU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e.unsign = .ok a) (ha : AccOK σ DW DG EW ns a)
    (m cw : Nat) :
    instExpr2 E elems (some cw) (.resize m e) = .resize cw (accExpr σ a) := by
  obtain ⟨hsw, hin, -⟩ := leaf_eqU C hdw h ha
  obtain ⟨hcp, hcl, hng⟩ := leaf_flagsU h
  simp [instExpr2, hsw, hcp, hcl, hng, hin]

/-! ## The self-determined (v1) shape theorem -/

/-- The skeleton of an accepted leaf is the access. -/
theorem skT_leafU {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e.unsign = .ok a) :
    skT e.unsign [a] = .rd a := by
  generalize e.unsign = x at h
  cases x <;> first | rfl | (simp [leafRd?] at h)

/-- The leaf case of the shape theorems: an access, or a signed read of an identifier. -/
theorem leaf_caseU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {v : PExpr} {rs : List Acc}
    (h : rdsLeaf? ds v.unsign = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (tw : Nat)
    (hw : (skT v.unsign rs).WidthOk σ dw tw) :
    selfWidth2 E elems v = some tw ∧ rigidMax2 E elems v = some tw ∧
      instExpr2 E elems none v = (skT v.unsign rs).low σ dw tw ∧
      instExpr2 E elems (some tw) v = (skT v.unsign rs).low σ dw tw ∧
      fitExpr2 E elems (some tw) v = (skT v.unsign rs).low σ dw tw := by
  obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases h
  rw [skT_leafU hl] at hw ⊢
  simp only [Sk.WidthOk, Sk.low] at hw ⊢
  obtain ⟨hsw, hin, -⟩ := leaf_eqU C hdw hl (hacc a (by simp))
  exact ⟨by rw [hsw, hw], by rw [rm_leafU hl, hsw, hw], hin none, hin _,
    leaf_fitU C hdw hl (hacc a (by simp)) hw⟩


/-- `skT_shape` for an expression whose unsigned twin is accepted. -/
theorem skT_shapeU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOf? ds v.unsign = .ok rs → fragG v.unsign = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ∀ tw, (skT v.unsign rs).WidthOk σ dw tw →
        selfWidth2 E elems v = some tw ∧ rigidMax2 E elems v = some tw ∧
        instExpr2 E elems none v = (skT v.unsign rs).low σ dw tw ∧
        instExpr2 E elems (some tw) v = (skT v.unsign rs).low σ dw tw ∧
        fitExpr2 E elems (some tw) v = (skT v.unsign rs).low σ dw tw
  | .lit lv, rs, h, _, _, tw, hw => by
      simp only [PExpr.unsign, rdsOf?, Except.ok.injEq] at h
      subst h
      simp only [PExpr.unsign, skT, Sk.WidthOk] at hw ⊢
      refine ⟨by simp [hw], by simp [rigidMax2, hw], by simp [Sk.low, instExpr2],
        by simp [Sk.low, instExpr2], ?_⟩
      rw [fitExpr2_lit, if_pos hw]
      simp [Sk.low]
  | .binary op l r, rs, h, hf, hacc, tw, hw => by
      cases hu : unsignOp op with
      | false =>
          rw [unsign_binary_f hu] at h
          obtain ⟨hb, -⟩ := rdsOf?_binary h
          rw [unsignOp_of_binOk hb] at hu; cases hu
      | true =>
      rw [unsign_binary_t hu] at h hf hw ⊢
      simp only [fragG, Bool.and_eq_true] at hf
      obtain ⟨hb, ra, rb, hl, hr, rfl⟩ := rdsOf?_binary h
      have hla := rdsOf?_len l.unsign ra hl hf.1
      have e1 : (ra ++ rb).take (cnt l.unsign) = ra := List.take_left' hla
      have e2 : (ra ++ rb).drop (cnt l.unsign) = rb := List.drop_left' hla
      have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
      have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
      rcases hg : gateOf op with _ | b
      · rcases binOk_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simp [gateOf] at hg
        · simp [gateOf] at hg
        · simp [gateOf] at hg
        · have hsk : skT (.binary .land l.unsign r.unsign) (ra ++ rb) =
              .land (skT l.unsign ra) (skT r.unsign rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr⟩ := hw
          obtain ⟨Sl, -, -, I1l, -⟩ := skT_shapeU C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, I1r, -⟩ := skT_shapeU C hdw r rb hr hf.2 hacr _ (Sk.selfOk_widthOk σ dw _ hsr)
          have key : ∀ ctx, instExpr2 E elems ctx (.binary .land l r) =
              Sk.low σ dw 1 (.land (skT l.unsign ra) (skT r.unsign rb)) := by
            intro ctx
            rw [ie_land, Sl, Sr, I1l, I1r, Sk.low_irrel σ dw (skT l.unsign ra) hsl _ 0,
              Sk.low_irrel σ dw (skT r.unsign rb) hsr _ 0]
            rfl
          exact ⟨sw_land l r, rm_land l r, key none, key _, by rw [fitExpr2_binary]; exact key _⟩
        · have hsk : skT (.binary .lor l.unsign r.unsign) (ra ++ rb) =
              .lor (skT l.unsign ra) (skT r.unsign rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr⟩ := hw
          obtain ⟨Sl, -, -, I1l, -⟩ := skT_shapeU C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, I1r, -⟩ := skT_shapeU C hdw r rb hr hf.2 hacr _ (Sk.selfOk_widthOk σ dw _ hsr)
          have key : ∀ ctx, instExpr2 E elems ctx (.binary .lor l r) =
              Sk.low σ dw 1 (.lor (skT l.unsign ra) (skT r.unsign rb)) := by
            intro ctx
            rw [ie_lor, Sl, Sr, I1l, I1r, Sk.low_irrel σ dw (skT l.unsign ra) hsl _ 0,
              Sk.low_irrel σ dw (skT r.unsign rb) hsr _ 0]
            rfl
          exact ⟨sw_lor l r, rm_lor l r, key none, key _, by rw [fitExpr2_binary]; exact key _⟩
        · have hsk : skT (.binary (.m0 .eq) l.unsign r.unsign) (ra ++ rb) =
              .cmp .eq (skT l.unsign ra) (skT r.unsign rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr, hwe⟩ := hw
          obtain ⟨Sl, -, -, -, Fl⟩ := skT_shapeU C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, -, Fr⟩ := skT_shapeU C hdw r rb hr hf.2 hacr _
            (Sk.selfOk_widthOk σ dw _ hsr)
          rw [← hwe] at Sr Fr
          have hm : max ((skT l.unsign ra).width σ dw) ((skT r.unsign rb).width σ dw) =
              (skT l.unsign ra).width σ dw := by
            rw [← hwe]; exact Nat.max_self _
          have key : ∀ ctx, instExpr2 E elems ctx (.binary (.m0 .eq) l r) =
              Sk.low σ dw 1 (.cmp .eq (skT l.unsign ra) (skT r.unsign rb)) := by
            intro ctx
            rw [ie_eq ctx _ l r Sl Sr, Fl, Fr]
            simp only [Sk.low, CmpOp.ex, hm]
          exact ⟨sw_eq l r, rm_eq l r, key none, key _, by rw [fitExpr2_binary]; exact key _⟩
        · have hsk : skT (.binary (.m0 .ne) l.unsign r.unsign) (ra ++ rb) =
              .cmp .ne (skT l.unsign ra) (skT r.unsign rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr, hwe⟩ := hw
          obtain ⟨Sl, -, -, -, Fl⟩ := skT_shapeU C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, -, Fr⟩ := skT_shapeU C hdw r rb hr hf.2 hacr _
            (Sk.selfOk_widthOk σ dw _ hsr)
          rw [← hwe] at Sr Fr
          have hm : max ((skT l.unsign ra).width σ dw) ((skT r.unsign rb).width σ dw) =
              (skT l.unsign ra).width σ dw := by
            rw [← hwe]; exact Nat.max_self _
          have key : ∀ ctx, instExpr2 E elems ctx (.binary (.m0 .ne) l r) =
              Sk.low σ dw 1 (.cmp .ne (skT l.unsign ra) (skT r.unsign rb)) := by
            intro ctx
            rw [ie_ne ctx _ l r Sl Sr, Fl, Fr]
            simp only [Sk.low, CmpOp.ex, hm]
          exact ⟨sw_ne l r, rm_ne l r, key none, key _, by rw [fitExpr2_binary]; exact key _⟩
      · -- a bitwise gate
        obtain ⟨rfl, hbb⟩ := gateOf_cases hg
        have ihl := skT_shapeU C hdw l ra hl hf.1 hacl tw
        have ihr := skT_shapeU C hdw r rb hr hf.2 hacr tw
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
      rw [unsign_unary] at h hf hw ⊢
      obtain ⟨hop, ha⟩ := rdsOf?_unary h
      simp only [fragG] at hf
      rcases hop with rfl | rfl
      · have hsk : skT (.unary (.m0 .bnot) a.unsign) rs = .bnot (skT a.unsign rs) := by simp [skT]
        rw [hsk] at hw ⊢
        simp only [Sk.WidthOk] at hw
        obtain ⟨Sa, Ra, I0a, I1a, Fa⟩ := skT_shapeU C hdw a rs ha hf hacc tw hw
        have hrm : (rigidMax2 E elems a).getD tw ≤ tw := by rw [Ra]; simp
        have I1 : instExpr2 E elems (some tw) (.unary (.m0 .bnot) a) = Sk.low σ dw tw (.bnot (skT a.unsign rs)) := by
          rw [ie_bnot_some tw a hrm, Fa]; rfl
        refine ⟨by rw [sw_bnot]; exact Sa, by rw [rm_bnot]; exact Ra, ?_, I1, ?_⟩
        · rw [ie_bnot_none, Sa, I1a]; rfl
        · rw [fitExpr2_of_not_rigid tw (rigidExpr_unary _ _)]; exact I1
      · have hsk : skT (.unary (.m0 .lnot) a.unsign) rs = .lnot (skT a.unsign rs) := by simp [skT]
        rw [hsk] at hw ⊢
        obtain ⟨rfl, hsa⟩ := hw
        obtain ⟨-, -, I0a, -, -⟩ := skT_shapeU C hdw a rs ha hf hacc _ (Sk.selfOk_widthOk σ dw _ hsa)
        have key : ∀ ctx, instExpr2 E elems ctx (.unary (.m0 .lnot) a) = Sk.low σ dw 1 (.lnot (skT a.unsign rs)) := by
          intro ctx
          rw [ie_lnot, I0a, Sk.low_irrel σ dw (skT a.unsign rs) hsa _ 0]
          rfl
        exact ⟨sw_lnot a, rm_lnot a, key none, key _, by rw [fitExpr2_of_not_rigid 1 (rigidExpr_unary _ _)]; exact key _⟩
  | .ternary c t f, rs, h, hf, hacc, tw, hw => by
      rw [unsign_ternary] at h hf hw ⊢
      obtain ⟨rc, rt, rf, hc, ht, hfe, rfl⟩ := rdsOf?_ternary h
      simp only [fragG, Bool.and_eq_true] at hf
      have hc' := rdsOf?_len c.unsign rc hc hf.1.1
      have ht' := rdsOf?_len t.unsign rt ht hf.1.2
      have e1 : (rc ++ rt ++ rf).take (cnt c.unsign) = rc := by
        rw [List.append_assoc]; exact List.take_left' hc'
      have e2 : (rc ++ rt ++ rf).drop (cnt c.unsign) = rt ++ rf := by
        rw [List.append_assoc]; exact List.drop_left' hc'
      have e3 : (rt ++ rf).take (cnt t.unsign) = rt := List.take_left' ht'
      have e4 : (rt ++ rf).drop (cnt t.unsign) = rf := List.drop_left' ht'
      have hsk : skT (.ternary c.unsign t.unsign f.unsign) (rc ++ rt ++ rf) =
          .tern (skT c.unsign rc) (skT t.unsign rt) (skT f.unsign rf) := by
        simp only [skT, e1, e2, e3, e4]
      rw [hsk] at hw ⊢
      obtain ⟨hsc, hwc, hwt, hwf⟩ := hw
      have hc1 : (skT c.unsign rc).WidthOk σ dw 1 := by
        have := Sk.selfOk_widthOk σ dw _ hsc
        rwa [hwc] at this
      obtain ⟨-, -, I0c, -, -⟩ := skT_shapeU C hdw c rc hc hf.1.1
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_left _ hx))) 1 hc1
      obtain ⟨St, Rt, -, -, Ft⟩ := skT_shapeU C hdw t rt ht hf.1.2
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx))) tw hwt
      obtain ⟨Sf, Rf, -, -, Ff⟩ := skT_shapeU C hdw f rf hfe hf.2
        (fun x hx => hacc x (List.mem_append_right _ hx)) tw hwf
      have I1 : instExpr2 E elems (some tw) (.ternary c t f) =
          Sk.low σ dw tw (.tern (skT c.unsign rc) (skT t.unsign rt) (skT f.unsign rf)) := by
        rw [ie_ternary_some, I0c, Ft, Ff]
        simp only [Sk.low, Sk.low_irrel σ dw _ hsc 1 0]
      refine ⟨sw_ternary tw c t f St Sf, rm_ternary tw c t f Rt Rf, ?_, I1, ?_⟩
      · rw [ie_ternary_none tw c t f St Sf, I0c, Ft, Ff]
        simp only [Sk.low, Sk.low_irrel σ dw _ hsc 1 0]
      · rw [fitExpr2_of_not_rigid tw (rigidExpr_ternary _ _ _)]; exact I1
  | .reduce op a, rs, h, hf, hacc, tw, hw => by
      rw [unsign_reduce] at h hf hw ⊢
      simp only [fragG] at hf
      have ha := rdsOf?_reduce h
      have hsk : skT (.reduce op a.unsign) rs = .red op (skT a.unsign rs) := by simp [skT]
      rw [hsk] at hw ⊢
      obtain ⟨rfl, hsa⟩ := hw
      obtain ⟨Sa, -, -, I1a, -⟩ := skT_shapeU C hdw a rs ha hf hacc _ (Sk.selfOk_widthOk σ dw _ hsa)
      have key : ∀ ctx, instExpr2 E elems ctx (.reduce op a) = Sk.low σ dw 1 (.red op (skT a.unsign rs)) := by
        intro ctx
        rw [ie_reduce, Sa, I1a, Sk.low_irrel σ dw (skT a.unsign rs) hsa _ 0]
        rfl
      exact ⟨sw_reduce op a, rm_reduce op a, key none, key _, by
        rw [fitExpr2_of_rigid_eq (rigidExpr_reduce op a) (sw_reduce op a)]; exact key _⟩
  | .concat ps, _, _, hf, _, _, _ => by rw [unsign_concat] at hf; simp [fragG] at hf
  | .fill b, _, _, hf, _, _, _ => by simp [PExpr.unsign, fragG] at hf
  | .ident n, rs, h, _, hacc, tw, hw =>
      leaf_caseU C hdw (by simpa [PExpr.unsign, rdsOf?] using h) hacc tw hw
  | .bitSel b i, rs, h, _, hacc, tw, hw =>
      leaf_caseU C hdw (by simpa [PExpr.unsign, rdsOf?] using h) hacc tw hw
  | .partSel b m l, rs, h, _, hacc, tw, hw =>
      leaf_caseU C hdw (by simpa [PExpr.unsign, rdsOf?] using h) hacc tw hw
  | .arrayElem n is, rs, h, _, hacc, tw, hw =>
      leaf_caseU C hdw (by simpa [PExpr.unsign, rdsOf?] using h) hacc tw hw
  | .arrayPart n is m a b, rs, h, _, hacc, tw, hw =>
      leaf_caseU C hdw (by simpa [PExpr.unsign, rdsOf?] using h) hacc tw hw
  | .cast s x, rs, h, _, hacc, tw, hw =>
      leaf_caseU C hdw (by
        cases s <;> cases x <;> first
          | exact (by simpa [PExpr.unsign, rdsOf?] using h)
          | (exfalso; simp [PExpr.unsign, rdsOf?, rdsLeaf?, leafRd?] at h)) hacc tw hw
  | .paramRef .., rs, h, _, _, _, _ | .genvarRef .., rs, h, _, _, _, _
  | .enumRef .., rs, h, _, _, _, _
  | .int .., rs, h, _, _, _, _
  | .signedResize .., rs, h, _, _, _, _
  | .squash2 .., rs, h, _, _, _, _
  | .sysCall .., rs, h, _, _, _, _
  | .unsupported .., rs, h, _, _, _, _ => by
      simp [PExpr.unsign, rdsOf?, rdsLeaf?, leafRd?] at h
  | .repl c a, rs, h, _, _, _, _ => by
      rw [unsign_repl] at h; simp [rdsOf?, rdsLeaf?, leafRd?] at h
  | .resize m a, rs, h, _, _, _, _ => by
      rw [unsign_resize] at h; simp [rdsOf?, rdsLeaf?, leafRd?] at h


/-! ## Concatenations and replications -/

/-- `repl_shape` for a replication whose argument's unsigned twin is accepted, stated through its skeleton part. -/
theorem repl_shapeU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {c a : PExpr} {rs : List Acc}
    (h : repRd? ds c a.unsign = .ok rs) (hacc : ∀ x ∈ rs, AccOK σ DW DG EW ns x) (hco : ConstOK σ ns (.repl c a)) :
    ∃ p : Part, skT (.repl c a.unsign) rs = .rep p ∧
      selfWidth2 E elems (.repl c a) = some (p.wid σ dw) ∧
      ∀ ctx, instExpr2 E elems ctx (.repl c a) = p.expr σ := by
  obtain ⟨k, hk, harg⟩ := repRd?_cases h
  have hrc : repAff c = k := by simp [repAff, hk]
  rcases repArgRd?_cases harg with ⟨v, hv, rfl⟩ | ⟨e', hv, hl, hnl, hnw⟩
  · obtain ⟨e, rfl, he⟩ := unsign_eq_concat1 hv
    obtain rfl := unsign_eq_lit he
    have hw : selfWidth2 E elems (.concat [.lit v]) = some v.width := by
      rw [selfWidth2_concat]
      simpa using selfWidthSum2_cons_of (env := E) (elems := elems) (p := .lit v) (ps := []) (a := v.width) (b := 0)
        (by simp) selfWidthSum2_nil
    refine ⟨.replit (repAff c) v, by rw [hv]; rfl, ?_, fun ctx => ?_⟩
    · rw [selfWidth_repl C hk hco hw, hrc]; rfl
    · rw [inst_repl C hk hco ctx, hw, hrc]; simp [Part.expr]
  · obtain ⟨e, rfl, he⟩ := unsign_eq_concat1 hv
    subst he
    obtain ⟨x, hl', rfl⟩ := rdsLeaf_cases hl
    obtain ⟨hsw, hin, -⟩ := leaf_eqU C hdw hl' (hacc x (by simp))
    have hx : ∀ n, x ≠ .whole n := fun n hxn => hnw n (by rw [hxn])
    have hw : selfWidth2 E elems (.concat [e]) = some (x.win σ dw).2.2 := by
      rw [selfWidth2_concat]
      simpa using selfWidthSum2_cons_of (env := E) (elems := elems) (p := e) (ps := []) hsw selfWidthSum2_nil
    refine ⟨.reprd (repAff c) x, ?_, ?_, fun ctx => ?_⟩
    · rw [unsign_concat, unsignL_cons]
      simp only [PExpr.unsignL]
      generalize e.unsign = y at hnl
      cases y <;> first | rfl | exact absurd rfl (hnl _)
    · rw [selfWidth_repl C hk hco hw, Part.wid, win_wid_of_ne_whole hx, hrc]
    · rw [inst_repl C hk hco ctx]
      simp only [instExpr2_concat, instParts2_cons, instParts2_nil, hin]
      rw [hrc]
      rfl

/-- `parts_shapeW` for parts whose unsigned twins are accepted. -/
theorem parts_shapeWU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRdW? ds (PExpr.unsignL ps) = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → PartsCO σ ns (PExpr.unsignL ps) →
      selfWidthSum2 E elems ps = some ((partsT (PExpr.unsignL ps) rs).map (Part.wid σ dw)).sum ∧
        instParts2 E elems ps = (partsT (PExpr.unsignL ps) rs).map (Part.expr σ)
  | [], rs, h, _, _ => by
      simp only [PExpr.unsignL, partsRdW?, Except.ok.injEq] at h
      subst h
      simp [PExpr.unsignL, partsT, selfWidthSum2_nil, instParts2_nil]
  | p :: ps, rs, h, hacc, hco => by
      rw [unsignL_cons] at h hco ⊢
      simp only [partsRdW?] at h
      rcases hp : partRdW? ds p.unsign with e | ra
      · simp [hp] at h
      · rcases hq : partsRdW? ds (PExpr.unsignL ps) with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          obtain ⟨hco', hn, hc⟩ := partsCO_cons hco
          by_cases hpl : ∃ v, p.unsign = .lit v
          · obtain ⟨v, hv⟩ := hpl
            obtain rfl := unsign_eq_lit hv
            rw [unsign_lit] at hp ⊢
            have hra : ra = [] := by simpa [partRdW?] using hp.symm
            subst hra
            simp only [List.nil_append] at hacc ⊢
            obtain ⟨ih1, ih2⟩ := parts_shapeWU C hdw ps rb hq hacc hco'
            rw [partsT_lit]
            refine ⟨?_, ?_⟩
            · simp only [List.map_cons, List.sum_cons, Part.wid]
              exact selfWidthSum2_cons_of (by simp) ih1
            · simp only [instParts2_cons, List.map_cons, Part.expr, selfWidth2_lit, instExpr2_lit]
              rw [ih2]
          · have hnl : ∀ v, p.unsign ≠ .lit v := fun v h => hpl ⟨v, h⟩
            by_cases hpr : ∃ c a, p.unsign = .repl c a
            · obtain ⟨c, a, hca⟩ := hpr
              obtain ⟨a', rfl, rfl⟩ := unsign_eq_repl hca
              rw [unsign_repl] at hp hn hc ⊢
              have hrep : repRd? ds c a'.unsign = .ok ra := by simpa [partRdW?] using hp
              have hco1 : ConstOK σ ns (.repl c a') :=
                ⟨fun n hn' => hn n hn', fun k hk => hc k hk⟩
              obtain ⟨q, hsk, hS, hI⟩ :=
                repl_shapeU C hdw hrep (fun x hx => hacc x (List.mem_append_left _ hx)) hco1
              obtain ⟨ih1, ih2⟩ := parts_shapeWU C hdw ps rb hq
                (fun y hy => hacc y (List.mem_append_right _ hy)) hco'
              have e1 : partsT (PExpr.repl c a'.unsign :: PExpr.unsignL ps) (ra ++ rb) = q :: partsT (PExpr.unsignL ps) rb := by
                have hskp : skT (.repl c a'.unsign) ra = .rep q := hsk
                obtain ⟨k, -, harg⟩ := repRd?_cases hrep
                rcases repArgRd?_cases harg with ⟨v, hv, rfl⟩ | ⟨e', hv, hl, hnl', hnw⟩
                · rw [hv] at hskp ⊢
                  simp only [skT] at hskp
                  cases hskp
                  rfl
                · rw [hv] at hskp ⊢
                  obtain ⟨x, -, rfl⟩ := rdsLeaf_cases hl
                  rw [partsT_repl_ne c hnl']
                  have : skT (.repl c (.concat [e'])) [x] = .rep (.reprd (repAff c) x) := by
                    cases e' <;> first | rfl | exact absurd rfl (hnl' _)
                  rw [this] at hskp
                  cases hskp
                  rfl
              rw [e1]
              refine ⟨?_, ?_⟩
              · simp only [List.map_cons, List.sum_cons]
                exact selfWidthSum2_cons_of hS ih1
              · simp only [instParts2_cons, List.map_cons]
                rw [hI, ih2]
            · have hnr : ∀ c a, p.unsign ≠ .repl c a := fun c a h => hpr ⟨c, a, h⟩
              rw [partRdW?_of_ne hnl hnr] at hp
              obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
              have hA : AccOK σ DW DG EW ns a := hacc a (by simp)
              obtain ⟨ih1, ih2⟩ := parts_shapeWU C hdw ps rb hq
                (fun x hx => hacc x (List.mem_append_right _ hx)) hco'
              obtain ⟨hsw, hin, -⟩ := leaf_eqU C hdw hl hA
              have e1 : partsT (p.unsign :: PExpr.unsignL ps) ([a] ++ rb) = .rd a :: partsT (PExpr.unsignL ps) rb := by
                rw [partsT_of_ne hnl hnr]; rfl
              rw [e1]
              refine ⟨?_, ?_⟩
              · simp only [List.map_cons, List.sum_cons, Part.wid]
                exact selfWidthSum2_cons_of hsw ih1
              · simp only [instParts2_cons, List.map_cons, Part.expr, hsw, hin]
                rw [ih2]

/-- The leaf case of `skT_shapeCU`. -/
theorem leaf_caseCU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {v : PExpr} {rs : List Acc}
    (h : rdsLeaf? ds v.unsign = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (tw : Nat)
    (hw : (skT v.unsign rs).WidthOkC σ dw tw) :
    selfWidth2 E elems v = some ((skT v.unsign rs).width σ dw) ∧
    rigidMax2 E elems v = (skT v.unsign rs).rmax σ dw ∧
    ((skT v.unsign rs).isExt = false → (skT v.unsign rs).width σ dw ≤ tw →
      instExpr2 E elems none v = (skT v.unsign rs).low σ dw ((skT v.unsign rs).width σ dw)) ∧
    instExpr2 E elems (some tw) v = (skT v.unsign rs).low σ dw tw ∧
    fitExpr2 E elems (some tw) v = (skT v.unsign rs).low σ dw tw := by
  obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases h
  rw [skT_leafU hl] at hw ⊢
  simp only [Sk.WidthOkC, Sk.low, Sk.width, Sk.rmax] at hw ⊢
  obtain ⟨hsw, hin, -⟩ := leaf_eqU C hdw hl (hacc a (by simp))
  exact ⟨hsw, by rw [rm_leafU hl, hsw], fun _ _ => hin none, hin _, leaf_fitU C hdw hl (hacc a (by simp)) hw⟩

/-! ## The word-level shape theorem -/

/-- **`skT_shapeC` for an expression whose unsigned twin is accepted**: the recognizer and the skeleton read the twin,
the five facts are about the expression as written. -/
theorem skT_shapeCU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOfW? ds v.unsign = .ok rs → fragW v.unsign = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ConstOK σ ns v.unsign → ∀ tw, (skT v.unsign rs).WidthOkC σ dw tw →
        selfWidth2 E elems v = some ((skT v.unsign rs).width σ dw) ∧
        rigidMax2 E elems v = (skT v.unsign rs).rmax σ dw ∧
        ((skT v.unsign rs).isExt = false → (skT v.unsign rs).width σ dw ≤ tw →
          instExpr2 E elems none v = (skT v.unsign rs).low σ dw ((skT v.unsign rs).width σ dw)) ∧
        instExpr2 E elems (some tw) v = (skT v.unsign rs).low σ dw tw ∧
        fitExpr2 E elems (some tw) v = (skT v.unsign rs).low σ dw tw
  | .lit lv, rs, h, _, _, hcn, tw, hw => by
      rw [unsign_lit] at h hw ⊢
      simp only [rdsOfW?, Except.ok.injEq] at h
      subst h
      simp only [skT, Sk.WidthOkC] at hw
      refine ⟨by simp [skT, Sk.width, selfWidth2], by simp [skT, Sk.rmax, rigidMax2, selfWidth2],
        fun _ _ => by simp [skT, Sk.low, instExpr2], by simp [skT, Sk.low, instExpr2], ?_⟩
      rw [fitExpr2_lit, if_pos hw]
      simp [skT, Sk.low]
  | .binary op l r, rs, h, hf, hacc, hcn, tw, hw => by
      cases hu : unsignOp op with
      | false =>
      rw [unsign_binary_f hu] at h hf hcn hw ⊢
      rcases rdsOfW?_binary h with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, ra, rb, hl, hr, rfl⟩
      · rw [unsignOp_of_ctxOpW hb] at hu; cases hu
      · rw [unsignOp_of_selfOpW hb] at hu; cases hu
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
      | true =>
      rw [unsign_binary_t hu] at h hf hcn hw ⊢
      rcases rdsOfW?_binary h with ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨hb, ra, rb, hl, hr, rfl⟩ |
        ⟨hb, ra, rb, hl, hr, rfl⟩
      · -- `& | ^ + -`: context-determined operands
        replace hf := fragW_bin_ctx (selfOpW_false_of_ctx hb) hf
        have hla := rdsOfW?_len l.unsign ra hl hf.1
        have e1 : (ra ++ rb).take (cnt l.unsign) = ra := List.take_left' hla
        have e2 : (ra ++ rb).drop (cnt l.unsign) = rb := List.drop_left' hla
        have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
        have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
        have ihl := skT_shapeCU C hdw l ra hl hf.1 hacl (cok_binary_l hcn)
        have ihr := skT_shapeCU C hdw r rb hr hf.2 hacr (cok_binary_r hcn)
        by_cases hcm : ∃ cm : CmpOp, op = .m0 cm.ex
        · -- a comparison: one bit, the operands context-determined at the wider natural width
          obtain ⟨cm, rfl⟩ := hcm
          have hsk : skT (.binary (.m0 cm.ex) l.unsign r.unsign) (ra ++ rb) = .cmp cm (skT l.unsign ra) (skT r.unsign rb) := by
            cases cm <;> simp [skT, gateOf, CmpOp.ex, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hwl, hwr⟩ := hw
          obtain ⟨Sl, -, -, -, Fl⟩ := ihl _ hwl
          obtain ⟨Sr, -, -, -, Fr⟩ := ihr _ hwr
          have key : ∀ ctx, instExpr2 E elems ctx (.binary (.m0 cm.ex) l r) =
              Sk.low σ dw 1 (.cmp cm (skT l.unsign ra) (skT r.unsign rb)) := by
            intro ctx
            rw [ie_cmp cm ctx _ _ l r Sl Sr, Fl, Fr]
            simp only [Sk.low]
          exact ⟨sw_cmp cm l r, rm_cmp cm l r, fun _ _ => key none, key _, by
            rw [fitExpr2_binary]; exact key _⟩
        by_cases hmul : op = .mul
        · -- `*`: the shape of `+`, a factor being a signal access (`instExpr2` does not fold the product)
          subst hmul
          have hm := sigOpd_or_of_unsign (rdsOfW?_mul h)
          have hsk : skT (.binary .mul l.unsign r.unsign) (ra ++ rb) = .mul (skT l.unsign ra) (skT r.unsign rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨Sl, Rl, -, -, Fl⟩ := ihl tw hw.1
          obtain ⟨Sr, Rr, -, -, Fr⟩ := ihr tw hw.2.1
          have hI1 : instExpr2 E elems (some tw) (.binary .mul l r) = (Sk.mul (skT l.unsign ra) (skT r.unsign rb)).low σ dw tw := by
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
        have hsk : skT (.binary (.m0 b) l.unsign r.unsign) (ra ++ rb) = mkOpW b (skT l.unsign ra) (skT r.unsign rb) := by
          rcases hbb with rfl | rfl | rfl | rfl | rfl <;>
            simp [skT, gateOf, mkGate, mkOpW, e1, e2]
        rw [hsk] at hw ⊢
        have hwk : (skT l.unsign ra).WidthOkC σ dw tw ∧ (skT r.unsign rb).WidthOkC σ dw tw := by
          rcases hbb with rfl | rfl | rfl | rfl | rfl
          · exact hw
          · exact hw
          · exact hw
          · exact ⟨hw.1, hw.2.1⟩
          · exact ⟨hw.1, hw.2.1⟩
        obtain ⟨Sl, Rl, I0l, I1l, Fl⟩ := ihl tw hwk.1
        obtain ⟨Sr, Rr, I0r, I1r, Fr⟩ := ihr tw hwk.2
        have hS : selfWidth2 E elems (.binary (.m0 b) l r) =
            some (max ((skT l.unsign ra).width σ dw) ((skT r.unsign rb).width σ dw)) := by
          rcases hbb with rfl | rfl | rfl | rfl | rfl <;> simp [selfWidth2, Sl, Sr]
        have hR : rigidMax2 E elems (.binary (.m0 b) l r) =
            (mkOpW b (skT l.unsign ra) (skT r.unsign rb)).rmax σ dw := by
          rw [rm_ctx E elems b hbb l r, ctxOpWidth2_eq, Rl, Rr]
          rcases hbb with rfl | rfl | rfl | rfl | rfl <;> rfl
        have hI0 : max ((skT l.unsign ra).width σ dw) ((skT r.unsign rb).width σ dw) ≤ tw →
            instExpr2 E elems none (.binary (.m0 b) l r) =
              (mkOpW b (skT l.unsign ra) (skT r.unsign rb)).low σ dw
                (max ((skT l.unsign ra).width σ dw) ((skT r.unsign rb).width σ dw)) := by
          intro hle
          have hWl := Sk.WidthOkC.mono _ _ (max ((skT l.unsign ra).width σ dw) ((skT r.unsign rb).width σ dw)) hwk.1
            (Nat.le_max_left _ _) hle
          have hWr := Sk.WidthOkC.mono _ _ (max ((skT l.unsign ra).width σ dw) ((skT r.unsign rb).width σ dw)) hwk.2
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
        have hla := rdsOf?_len l.unsign ra hl hf.1
        have e1 : (ra ++ rb).take (cnt l.unsign) = ra := List.take_left' hla
        have e2 : (ra ++ rb).drop (cnt l.unsign) = rb := List.drop_left' hla
        have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
        have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
        rcases selfOpW_cases hb with rfl | rfl
        · have hsk : skT (.binary .land l.unsign r.unsign) (ra ++ rb) = .land (skT l.unsign ra) (skT r.unsign rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr⟩ := hw
          obtain ⟨Sl, -, -, I1l, -⟩ := skT_shapeU C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, I1r, -⟩ := skT_shapeU C hdw r rb hr hf.2 hacr _ (Sk.selfOk_widthOk σ dw _ hsr)
          have key : ∀ ctx, instExpr2 E elems ctx (.binary .land l r) =
              Sk.low σ dw 1 (.land (skT l.unsign ra) (skT r.unsign rb)) := by
            intro ctx
            rw [ie_land, Sl, Sr, I1l, I1r, Sk.low_irrel σ dw (skT l.unsign ra) hsl _ 0,
              Sk.low_irrel σ dw (skT r.unsign rb) hsr _ 0]
            rfl
          exact ⟨sw_land l r, rm_land l r, fun _ _ => key none, key _, by rw [fitExpr2_binary]; exact key _⟩
        · have hsk : skT (.binary .lor l.unsign r.unsign) (ra ++ rb) = .lor (skT l.unsign ra) (skT r.unsign rb) := by
            simp [skT, gateOf, e1, e2]
          rw [hsk] at hw ⊢
          obtain ⟨rfl, hsl, hsr⟩ := hw
          obtain ⟨Sl, -, -, I1l, -⟩ := skT_shapeU C hdw l ra hl hf.1 hacl _ (Sk.selfOk_widthOk σ dw _ hsl)
          obtain ⟨Sr, -, -, I1r, -⟩ := skT_shapeU C hdw r rb hr hf.2 hacr _ (Sk.selfOk_widthOk σ dw _ hsr)
          have key : ∀ ctx, instExpr2 E elems ctx (.binary .lor l r) =
              Sk.low σ dw 1 (.lor (skT l.unsign ra) (skT r.unsign rb)) := by
            intro ctx
            rw [ie_lor, Sl, Sr, I1l, I1r, Sk.low_irrel σ dw (skT l.unsign ra) hsl _ 0,
              Sk.low_irrel σ dw (skT r.unsign rb) hsr _ 0]
            rfl
          exact ⟨sw_lor l r, rm_lor l r, fun _ _ => key none, key _, by rw [fitExpr2_binary]; exact key _⟩
      · rw [unsignOp_of_shOpW (by assumption)] at hu; cases hu
  | .unary op a, rs, h, hf, hacc, hcn, tw, hw => by
      rw [unsign_unary] at h hf hcn hw ⊢
      rcases rdsOfW?_unary h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · replace hf : fragW a.unsign = true := by simpa [fragW] using hf
        have hsk : skT (.unary (.m0 .bnot) a.unsign) rs = .bnot (skT a.unsign rs) := by simp [skT]
        rw [hsk] at hw ⊢
        simp only [Sk.WidthOkC] at hw
        obtain ⟨Sa, Ra, I0a, I1a, Fa⟩ := skT_shapeCU C hdw a rs ha hf hacc (cok_unary hcn) tw hw.1
        have hrm : (rigidMax2 E elems a).getD tw ≤ tw := by
          rw [Ra]; exact Sk.getD_le (Sk.rmax_le _ tw hw.1 hw.2)
        have I1 : instExpr2 E elems (some tw) (.unary (.m0 .bnot) a) =
            (Sk.bnot (skT a.unsign rs)).low σ dw tw := by
          rw [ie_bnot_some tw a hrm, Fa]; rfl
        refine ⟨by rw [sw_bnot]; exact Sa, by rw [rm_bnot]; exact Ra, fun _ hle => ?_, I1, ?_⟩
        · have hW := Sk.WidthOkC.mono _ _ ((skT a.unsign rs).width σ dw) hw.1 (Nat.le_refl _) hle
          obtain ⟨-, -, -, I1aW, -⟩ := skT_shapeCU C hdw a rs ha hf hacc (cok_unary hcn) _ hW
          rw [ie_bnot_none, Sa, I1aW]; rfl
        · rw [fitExpr2_of_not_rigid tw (rigidExpr_unary _ _)]; exact I1
      · replace hf : fragG a.unsign = true := by simpa [fragW] using hf
        have hsk : skT (.unary (.m0 .lnot) a.unsign) rs = .lnot (skT a.unsign rs) := by simp [skT]
        rw [hsk] at hw ⊢
        obtain ⟨rfl, hsa⟩ := hw
        obtain ⟨-, -, I0a, -, -⟩ := skT_shapeU C hdw a rs ha hf hacc _ (Sk.selfOk_widthOk σ dw _ hsa)
        have key : ∀ ctx, instExpr2 E elems ctx (.unary (.m0 .lnot) a) = Sk.low σ dw 1 (.lnot (skT a.unsign rs)) := by
          intro ctx
          rw [ie_lnot, I0a, Sk.low_irrel σ dw (skT a.unsign rs) hsa _ 0]
          rfl
        exact ⟨sw_lnot a, rm_lnot a, fun _ _ => key none, key _, by
          rw [fitExpr2_of_not_rigid 1 (rigidExpr_unary _ _)]; exact key _⟩
  | .ternary c t f, rs, h, hf, hacc, hcn, tw, hw => by
      rw [unsign_ternary] at h hf hcn hw ⊢
      obtain ⟨rc, rt, rf, hc, ht, hfe, rfl⟩ := rdsOfW?_ternary h
      simp only [fragW, Bool.and_eq_true] at hf
      have hc' := rdsOf?_len c.unsign rc hc hf.1.1
      have ht' := rdsOfW?_len t.unsign rt ht hf.1.2
      have e1 : (rc ++ rt ++ rf).take (cnt c.unsign) = rc := by
        rw [List.append_assoc]; exact List.take_left' hc'
      have e2 : (rc ++ rt ++ rf).drop (cnt c.unsign) = rt ++ rf := by
        rw [List.append_assoc]; exact List.drop_left' hc'
      have e3 : (rt ++ rf).take (cnt t.unsign) = rt := List.take_left' ht'
      have e4 : (rt ++ rf).drop (cnt t.unsign) = rf := List.drop_left' ht'
      have hsk : skT (.ternary c.unsign t.unsign f.unsign) (rc ++ rt ++ rf) = .tern (skT c.unsign rc) (skT t.unsign rt) (skT f.unsign rf) := by
        simp only [skT, e1, e2, e3, e4]
      rw [hsk] at hw ⊢
      obtain ⟨hsc, hwc, hwt, hwf⟩ := hw
      have hc1 : (skT c.unsign rc).WidthOk σ dw 1 := by
        have := Sk.selfOk_widthOk σ dw _ hsc
        rwa [hwc] at this
      obtain ⟨-, -, I0c, -, -⟩ := skT_shapeU C hdw c rc hc hf.1.1
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_left _ hx))) 1 hc1
      obtain ⟨St, Rt, -, -, Ft⟩ := skT_shapeCU C hdw t rt ht hf.1.2
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx)))
        (cok_ternary_t hcn) tw hwt
      obtain ⟨Sf, Rf, -, -, Ff⟩ := skT_shapeCU C hdw f rf hfe hf.2
        (fun x hx => hacc x (List.mem_append_right _ hx))
        (cok_ternary_e hcn) tw hwf
      have I1 : instExpr2 E elems (some tw) (.ternary c t f) =
          Sk.low σ dw tw (.tern (skT c.unsign rc) (skT t.unsign rt) (skT f.unsign rf)) := by
        rw [ie_ternary_some, I0c, Ft, Ff]
        simp only [Sk.low, Sk.low_irrel σ dw _ hsc 1 0]
      refine ⟨by simp [selfWidth2, St, Sf, Sk.width],
        by rw [rm_tern_maxO, Rt, Rf]; rfl, fun _ hle => ?_, I1, ?_⟩
      · have hle' : max ((skT t.unsign rt).width σ dw) ((skT f.unsign rf).width σ dw) ≤ tw := hle
        have hWt := Sk.WidthOkC.mono _ _ (max ((skT t.unsign rt).width σ dw) ((skT f.unsign rf).width σ dw)) hwt
          (Nat.le_max_left _ _) hle'
        have hWf := Sk.WidthOkC.mono _ _ (max ((skT t.unsign rt).width σ dw) ((skT f.unsign rf).width σ dw)) hwf
          (Nat.le_max_right _ _) hle'
        obtain ⟨-, -, -, -, FtW⟩ := skT_shapeCU C hdw t rt ht hf.1.2
          (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx)))
          (cok_ternary_t hcn) _ hWt
        obtain ⟨-, -, -, -, FfW⟩ := skT_shapeCU C hdw f rf hfe hf.2
          (fun x hx => hacc x (List.mem_append_right _ hx))
          (cok_ternary_e hcn) _ hWf
        rw [ie_ternary_none' c t f St Sf, I0c, FtW, FfW]
        simp only [Sk.low, Sk.width, Sk.low_irrel σ dw _ hsc 1 0]
      · rw [fitExpr2_of_not_rigid tw (rigidExpr_ternary _ _ _)]; exact I1
  | .reduce op a, rs, h, hf, hacc, hcn, tw, hw => by
      rw [unsign_reduce] at h hf hcn hw ⊢
      simp only [fragW] at hf
      have ha := rdsOfW?_reduce h
      have hsk : skT (.reduce op a.unsign) rs = .red op (skT a.unsign rs) := by simp [skT]
      rw [hsk] at hw ⊢
      obtain ⟨rfl, hsa⟩ := hw
      obtain ⟨Sa, -, -, I1a, -⟩ := skT_shapeU C hdw a rs ha hf hacc _ (Sk.selfOk_widthOk σ dw _ hsa)
      have key : ∀ ctx, instExpr2 E elems ctx (.reduce op a) = Sk.low σ dw 1 (.red op (skT a.unsign rs)) := by
        intro ctx
        rw [ie_reduce, Sa, I1a, Sk.low_irrel σ dw (skT a.unsign rs) hsa _ 0]
        rfl
      exact ⟨sw_reduce op a, rm_reduce op a, fun _ _ => key none, key _, by
        rw [fitExpr2_of_rigid_eq (rigidExpr_reduce op a) (sw_reduce op a)]; exact key _⟩
  | .resize m e, rs, h, hf, hacc, hcn, tw, hw => by
      rw [unsign_resize] at h hf hcn hw ⊢
      rcases rdsOfW?_resize h with ⟨v, hv, rfl⟩ | ⟨hn, a, hl, rfl⟩ | ⟨hop, hr⟩
      · obtain rfl := unsign_eq_lit hv
        rw [unsign_lit] at hw ⊢
        simp only [skT, Sk.WidthOkC, Sk.width, Part.wid] at hw ⊢
        refine ⟨by simp [selfWidth2], by simp [rigidMax2, selfWidth2, Sk.rmax, Part.wid],
          fun h => by simp [Sk.isExt] at h, ?_, ?_⟩
        · rw [ie_resize_lit]; simp [Sk.low, Part.expr]
        · rw [fitExpr2_of_not_rigid tw rfl, ie_resize_lit]; simp [Sk.low, Part.expr]
      · have hsk : skT (.resize m e.unsign) [a] = .ext (.rd a) := by
          generalize e.unsign = x at hn hl
          cases x <;> first | exact absurd rfl (hn _) | (simp [leafRd?] at hl; done) | rfl
        rw [hsk] at hw ⊢
        obtain ⟨hsw, -, -⟩ := leaf_eqU C hdw hl (hacc a (by simp))
        have I1 : instExpr2 E elems (some tw) (.resize m e) = (Sk.ext (.rd a)).low σ dw tw := by
          rw [ie_resize_leafU C hdw hl (hacc a (by simp)) m tw]; rfl
        refine ⟨by simp [selfWidth2, hsw, Sk.width, Part.wid],
          by simp [rigidMax2, Sk.rmax, Part.wid, rm_leafU hl, hsw],
          fun h => by simp [Sk.isExt] at h, I1, ?_⟩
        rw [fitExpr2_of_not_rigid tw rfl]; exact I1
      · -- a marker around an operation
        have hop' : e.isOpW = true := by rw [← unsign_isOpW]; exact hop
        have hf' : fragW e.unsign = true := by simpa [fragW] using hf
        have hsk : skT (.resize m e.unsign) rs = .rsz e.ctxPropagates (skT e.unsign rs) := by
          rw [skT_resize_op m rs hr hop, unsign_ctxPropagates hop']
        rw [hsk] at hw ⊢
        have ihe := skT_shapeCU C hdw e rs hr hf' hacc (cok_resize hcn)
        have hkey : selfWidth2 E elems e = some ((skT e.unsign rs).width σ dw) ∧
            rigidMax2 E elems e = (skT e.unsign rs).rmax σ dw ∧
            instExpr2 E elems (some tw) (.resize m e) = (Sk.rsz e.ctxPropagates (skT e.unsign rs)).low σ dw tw := by
          have hbundle : ∀ c, (skT e.unsign rs).WidthOkC σ dw c →
              selfWidth2 E elems e = some ((skT e.unsign rs).width σ dw) ∧
                rigidMax2 E elems e = (skT e.unsign rs).rmax σ dw ∧
                  instExpr2 E elems (some c) e = (skT e.unsign rs).low σ dw c := by
            intro c hc
            obtain ⟨Se, Re, -, I1e, -⟩ := ihe c hc
            exact ⟨Se, Re, I1e⟩
          cases hpr : e.ctxPropagates
          · rw [hpr] at hw
            simp only [Sk.WidthOkC] at hw
            obtain ⟨Se, Re, I1e⟩ := hbundle _ hw
            refine ⟨Se, Re, ?_⟩
            rw [ie_resize_op_eq hop' Se, hpr]
            simp [Sk.low, I1e]
          · rw [hpr] at hw
            simp only [Sk.WidthOkC] at hw
            by_cases hc : (skT e.unsign rs).width σ dw < tw
            · rw [if_pos hc] at hw
              obtain ⟨Se, Re, I1e⟩ := hbundle _ hw
              refine ⟨Se, Re, ?_⟩
              rw [ie_resize_op_eq hop' Se, hpr]
              simp [Sk.low, hc, I1e]
            · rw [if_neg hc] at hw
              obtain ⟨Se, Re, I1e⟩ := hbundle _ hw
              refine ⟨Se, Re, ?_⟩
              rw [ie_resize_op_eq hop' Se, hpr]
              simp [Sk.low, hc, I1e]
        obtain ⟨Se, Re, I1⟩ := hkey
        refine ⟨by simp [selfWidth2, Se, Sk.width], by simpa [rigidMax2, Sk.rmax] using Re,
          fun h => by simp [Sk.isExt] at h, I1, ?_⟩
        rw [fitExpr2_of_not_rigid tw rfl]; exact I1
  | .int v, rs, h, _, _, hcn, tw, _ => by
      rw [unsign_int] at h ⊢
      simp only [rdsOfW?, Except.ok.injEq] at h
      subst h
      refine ⟨by simp [selfWidth2, skT, Sk.width], by simp [rigidMax2, skT, Sk.rmax], fun _ _ => ?_, ?_, ?_⟩
      · rw [ie_int]; rfl
      · rw [ie_int]; rfl
      · rw [fitExpr2_of_not_rigid tw rfl, ie_int]; rfl
  | .ident n, rs, h, _, hacc, hcn, tw, hw =>
      leaf_caseCU C hdw (by simpa [PExpr.unsign, rdsOfW?] using h) hacc tw hw
  | .bitSel b i, rs, h, _, hacc, hcn, tw, hw =>
      leaf_caseCU C hdw (by simpa [PExpr.unsign, rdsOfW?] using h) hacc tw hw
  | .partSel b pm pl, rs, h, _, hacc, hcn, tw, hw =>
      leaf_caseCU C hdw (by simpa [PExpr.unsign, rdsOfW?] using h) hacc tw hw
  | .arrayElem n is, rs, h, _, hacc, hcn, tw, hw =>
      leaf_caseCU C hdw (by simpa [PExpr.unsign, rdsOfW?] using h) hacc tw hw
  | .arrayPart n is m a b, rs, h, _, hacc, hcn, tw, hw =>
      leaf_caseCU C hdw (by simpa [PExpr.unsign, rdsOfW?] using h) hacc tw hw
  | .cast s x, rs, h, _, hacc, hcn, tw, hw =>
      leaf_caseCU C hdw (by
        cases s <;> cases x <;> first
          | exact (by simpa [PExpr.unsign, rdsOfW?] using h)
          | (exfalso; simp [PExpr.unsign, rdsOfW?, rdsLeaf?, leafRd?] at h)) hacc tw hw
  | .concat ps, rs, h, _, hacc, hcn, tw, hw => by
      rw [unsign_concat] at h hcn hw ⊢
      have h' : partsRdW? ds (PExpr.unsignL ps) = .ok rs := by simpa [rdsOfW?] using h
      obtain ⟨h1, h2⟩ := parts_shapeWU C hdw ps rs h' hacc hcn
      simp only [skT, Sk.WidthOkC] at hw
      have hS : selfWidth2 E elems (.concat ps) = some ((skT (.concat (PExpr.unsignL ps)) rs).width σ dw) := by
        simpa [skT, Sk.width] using h1
      have hI : ∀ (ctx : Option Nat) (tw' : Nat), instExpr2 E elems ctx (.concat ps) =
          (skT (.concat (PExpr.unsignL ps)) rs).low σ dw tw' := by
        intro ctx tw'
        simp only [instExpr2_concat, skT, Sk.low, h2]
      have hRg : rigidMax2 E elems (.concat ps) = selfWidth2 E elems (.concat ps) := by
        first | rfl | simp [rigidMax2]
      refine ⟨hS, ?_, fun _ _ => hI none _, hI _ _, ?_⟩
      · rw [hRg, hS]; simp [skT, Sk.rmax, Sk.width]
      · rw [fitExpr2_concat h1, if_pos hw]
        simp only [skT, Sk.low, h2]
  | .repl c a, rs, h, _, hacc, hcn, tw, hw => by
      rw [unsign_repl] at h hcn hw ⊢
      have h' : repRd? ds c a.unsign = .ok rs := by simpa [rdsOfW?] using h
      obtain ⟨p, hsk, hS, hI⟩ := repl_shapeU C hdw h' hacc hcn
      rw [hsk] at hw ⊢
      simp only [Sk.WidthOkC] at hw
      exact rep_bundle hS hI hw
  | .fill _, _, _, hf, _, _, _, _ => by simp [PExpr.unsign, fragW] at hf
  | .paramRef .., rs, h, _, _, _, _, _ | .genvarRef .., rs, h, _, _, _, _, _
  | .enumRef .., rs, h, _, _, _, _, _
  | .signedResize .., rs, h, _, _, _, _, _
  | .squash2 .., rs, h, _, _, _, _, _
  | .sysCall .., rs, h, _, _, _, _, _
  | .unsupported .., rs, h, _, _, _, _, _ => by
      simp [PExpr.unsign, rdsOfW?, rdsLeaf?, leafRd?] at h

theorem gate_shapeCU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOfW? ds v.unsign = .ok rs → fragW v.unsign = true →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ConstOK σ ns v.unsign → ∀ tw, (skT v.unsign rs).WidthOkC σ dw tw →
        fitExpr2 E elems (some tw) v = (skT v.unsign rs).low σ dw tw :=
  fun v rs h hf hacc hcn tw hw => (skT_shapeCU C hdw v rs h hf hacc hcn tw hw).2.2.2.2

/-- `rhs_shapeC` for a right-hand side whose unsigned twin is accepted. -/
theorem rhs_shapeCU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {v : PExpr}
    {rs : List Acc} (h : rhsRds? ds v.unsign = .ok rs) (hf : fragOk v.unsign = true)
    (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (hcn : ConstOK σ ns v.unsign) {tw : Nat}
    (hw : (skRhs v.unsign rs).WidthOkC σ dw tw) :
    fitExpr2 E elems (some tw) v = (skRhs v.unsign rs).low σ dw tw := by
  by_cases hfill : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hfill
    rw [fitExpr2_of_not_rigid tw rfl]
    simp [instExpr2, PExpr.unsign, skRhs, Sk.low]
  by_cases hcat : ∃ ps, v = .concat ps
  · obtain ⟨ps, rfl⟩ := hcat
    rw [unsign_concat] at h hcn hw ⊢
    have h' : partsRdW? ds (PExpr.unsignL ps) = .ok rs := by simpa [rhsRds?, rdsOfW?] using h
    obtain ⟨h1, h2⟩ := parts_shapeWU C hdw ps rs h' hacc hcn
    simp only [skRhs, Sk.WidthOkC] at hw
    rw [fitExpr2_concat h1, if_pos hw]
    simp only [skRhs, Sk.low, h2]
  · have hn1 : ∀ b, v.unsign ≠ .fill b := fun b h => hfill ⟨b, unsign_eq_fill h⟩
    have hn2 : ∀ ps, v.unsign ≠ .concat ps := fun ps h => by
      obtain ⟨qs, hq, -⟩ : ∃ qs, v = .concat qs ∧ True := by
        cases v with
        | concat qs => exact ⟨qs, rfl, trivial⟩
        | cast s y => cases s <;> cases y <;> simp [PExpr.unsign] at h
        | binary op l r =>
            cases hu : unsignOp op
            · rw [unsign_binary_f hu] at h; cases h
            · rw [unsign_binary_t hu] at h; cases h
        | _ => simp [PExpr.unsign] at h
      exact hcat ⟨qs, hq⟩
    have h2 : rhsRds? ds v.unsign = rdsOfW? ds v.unsign := by
      generalize v.unsign = x at hn1
      cases x <;> first | rfl | exact absurd rfl (hn1 _)
    rw [h2] at h
    rw [fragOk_of_ne hn1 hn2] at hf
    rw [skRhs_of_ne hn1 hn2] at hw ⊢
    exact gate_shapeCU C hdw v rs h hf hacc hcn tw hw

end leaf

end CombEq
end LeanModels.Sv
