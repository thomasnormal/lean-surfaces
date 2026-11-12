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

**Signed reads.** A signed read is the envelope's cast marker around the identifier, `PExpr.cast true (.ident n)`
(`CombView.lean`, "Signed reads: the unsigned twin of a design"). The marker is transparent to every width function and
to `instExpr2`, and it changes `fitExpr2` only for an operand narrower than its context, which the width contract
(`Sk.WidthOkC`: a bare access is exactly as wide as its context) excludes. So the shape theorems are proved for an
expression `v` whose unsigned twin `v.unsign` the recognizer accepts, the recognizer and the skeleton read on `v.unsign`
and the instantiation on `v` (suffix `U`: `skT_shapeU`, `parts_shapeWU`, `skT_shapeCU`, `rhs_shapeCU`), and the theorems
for a design without signed reads are their special case `v.unsign = v` (`unsign_of_rdsOf`, `unsign_of_rdsOfW`,
`unsign_of_rhsRds`): `skT_shape`, `parts_shapeW`, `skT_shapeC`, `rhs_shapeC`. `CombSigned.lean` builds the bridge to a
design as written on the `U` forms.
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

/-! ## Constant leaves read through `IEnv.intVal?`

The comb view's agreement (`Agrees`, `Ctx.agree`) is phrased through `IEnv.intVal?`: a name is a loop binding in
`vals` or an exact signed-32 parameter in `nvals`. A genvar or parameter so bound instantiates to a literal of that
value, as `instExpr2_genvarRef_of`/`instExpr2_paramRef_of` (`Gen2.lean`) state for a `vals` binding. -/

theorem instExpr2_genvarRef_of_intVal {E : IEnv} {elems : List (String × Nat)} {g : String} {v : Int}
    (h : E.intVal? g = some v) (ctx : Option Nat) :
    instExpr2 E elems ctx (.genvarRef g) = .lit (LVec.ofInt (ctx.getD 32) v) := by
  cases hx : E.vals.lookup g with
  | some x =>
      have hxv : x = v := by simpa [IEnv.intVal?, hx] using h
      subst hxv
      exact instExpr2_genvarRef_of ctx hx
  | none =>
      rcases IEnv.intVal?_cases h with hv | ⟨w, s, hn, rfl, rfl⟩
      · rw [hx] at hv; cases hv
      · simp [instExpr2, hx, hn, intLit2_eq]

theorem instExpr2_paramRef_of_intVal {E : IEnv} {elems : List (String × Nat)} {n : String} {v : Int}
    (h : E.intVal? n = some v) (ctx : Option Nat) :
    instExpr2 E elems ctx (.paramRef n none) = .lit (LVec.ofInt (ctx.getD 32) v) := by
  cases hx : E.vals.lookup n with
  | some x =>
      have hxv : x = v := by simpa [IEnv.intVal?, hx] using h
      subst hxv
      exact instExpr2_paramRef_of ctx hx
  | none =>
      have hs : n ∉ E.stale := fun hs => by simp [IEnv.intVal?, hx, hs] at h
      rcases IEnv.intVal?_cases h with hv | ⟨w, s, hn, rfl, rfl⟩
      · rw [hx] at hv; cases hv
      · simp [instExpr2, hx, hn, hs, intLit2_eq]

/-! ## One access leaf -/


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

/-- A leaf whose unsigned twin the leaf recognizer accepts: the leaf itself, a signed read of an identifier, or a bit or
part select of one. -/
theorem leafRd_unsign {ds : List DeclT} {e : PExpr} {a : Acc} (h : leafRd? ds e.unsign = .ok a) :
    leafRd? ds e = .ok a ∨ (∃ n, e = .cast true (.ident n) ∧ leafRd? ds (.ident n) = .ok a) ∨
      (∃ n i, e = .bitSel (.cast true (.ident n)) i ∧ leafRd? ds (.bitSel (.ident n) i) = .ok a) ∨
      (∃ n msb lsb, e = .partSel (.cast true (.ident n)) msb lsb ∧
        leafRd? ds (.partSel (.ident n) msb lsb) = .ok a) := by
  cases e with
  | cast s x =>
      cases s with
      | true =>
          cases x with
          | ident n => exact Or.inr (Or.inl ⟨n, rfl, h⟩)
          | _ => simp [PExpr.unsign, leafRd?] at h
      | false => simp [PExpr.unsign, leafRd?] at h
  | bitSel b i =>
      cases b with
      | cast s x =>
          cases s with
          | true =>
              cases x with
              | ident n => exact Or.inr (Or.inr (Or.inl ⟨n, i, rfl, h⟩))
              | _ => exact Or.inl h
          | false => exact Or.inl h
      | _ => exact Or.inl h
  | partSel b msb lsb =>
      cases b with
      | cast s x =>
          cases s with
          | true =>
              cases x with
              | ident n => exact Or.inr (Or.inr (Or.inr ⟨n, msb, lsb, rfl, h⟩))
              | _ => exact Or.inl h
          | false => exact Or.inl h
      | _ => exact Or.inl h
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
  rcases leafRd_unsign h with h' | ⟨n, rfl, -⟩ | ⟨n, i, rfl, -⟩ | ⟨n, msb, lsb, rfl, -⟩
  · exact leaf_flags h'
  · exact ⟨rfl, rfl, fun _ _ _ => rfl⟩
  · exact ⟨rfl, rfl, fun _ _ _ => rfl⟩
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

/-- The twin of a select is a select of the same index or bounds (the marker of a signed base removed). -/
theorem unsign_bitSel (b i : PExpr) : ∃ b', (PExpr.bitSel b i).unsign = .bitSel b' i := by
  cases b with
  | cast s x => cases s <;> cases x <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

theorem unsign_partSel (b m l : PExpr) : ∃ b', (PExpr.partSel b m l).unsign = .partSel b' m l := by
  cases b with
  | cast s x => cases s <;> cases x <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

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
  | bitSel b i => obtain ⟨b', hb⟩ := unsign_bitSel b i; rw [hb] at h; cases h
  | partSel b m l => obtain ⟨b', hb⟩ := unsign_partSel b m l; rw [hb] at h; cases h
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
  | bitSel b i => obtain ⟨b', hb⟩ := unsign_bitSel b i; rw [hb] at h; cases h
  | partSel b m l => obtain ⟨b', hb⟩ := unsign_partSel b m l; rw [hb] at h; cases h
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
  | bitSel b i => obtain ⟨b', hb⟩ := unsign_bitSel b i; rw [hb] at h; cases h
  | partSel b m l => obtain ⟨b', hb⟩ := unsign_partSel b m l; rw [hb] at h; cases h
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
  | bitSel b i => obtain ⟨b', hb⟩ := unsign_bitSel b i; rw [hb] at h; cases h
  | partSel b m l => obtain ⟨b', hb⟩ := unsign_partSel b m l; rw [hb] at h; cases h
  | _ => simp [PExpr.unsign] at h

theorem unsign_isOpW (e : PExpr) : e.unsign.isOpW = e.isOpW := by
  cases e with
  | cast s y => cases s <;> cases y <;> rfl
  | bitSel b i => obtain ⟨b', hb⟩ := unsign_bitSel b i; rw [hb]; rfl
  | partSel b m l => obtain ⟨b', hb⟩ := unsign_partSel b m l; rw [hb]; rfl
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
  | bitSel b i =>
      cases b with
      | cast s y => cases s <;> cases y <;> simp_all [PExpr.unsign, sigOpd]
      | _ => simp_all [PExpr.unsign, sigOpd]
  | partSel b m l =>
      cases b with
      | cast s y => cases s <;> cases y <;> simp_all [PExpr.unsign, sigOpd]
      | _ => simp_all [PExpr.unsign, sigOpd]
  | resize m a =>
      rw [unsign_resize] at h
      cases a with
      | cast s y => cases s <;> cases y <;> simp_all [PExpr.unsign, sigOpd]
      | bitSel b i =>
          cases b with
          | cast s y => cases s <;> cases y <;> simp_all [PExpr.unsign, sigOpd]
          | _ => simp_all [PExpr.unsign, sigOpd]
      | partSel b m l =>
          cases b with
          | cast s y => cases s <;> cases y <;> simp_all [PExpr.unsign, sigOpd]
          | _ => simp_all [PExpr.unsign, sigOpd]
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

/-- **An access leaf instantiates to the slice it promises**, and has the promised self-width. -/
theorem leaf_eq (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e = .ok a) (ha : AccOK σ DW DG EW ns a) :
    selfWidth2 E elems e = some (a.win σ dw).2.2 ∧ (∀ ctx, instExpr2 E elems ctx e = accExpr σ a) ∧
      rigidExpr e = true := by
  obtain ⟨hdec, hgeo, hns⟩ := ha
  have hagx : ∀ x ∈ a.affs, ∀ n ∈ x.names, E.intVal? n = some (σ n) :=
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

/-- `leaf_eq` for a leaf whose unsigned twin is accepted. -/
theorem leaf_eqU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : leafRd? ds e.unsign = .ok a) (ha : AccOK σ DW DG EW ns a) :
    selfWidth2 E elems e = some (a.win σ dw).2.2 ∧ (∀ ctx, instExpr2 E elems ctx e = accExpr σ a) ∧
      rigidExpr e = true := by
  rcases leafRd_unsign h with h' | ⟨n, rfl, h'⟩ | ⟨n, i, rfl, h'⟩ | ⟨n, msb, lsb, rfl, h'⟩
  · exact leaf_eq C hdw h' ha
  · obtain ⟨h1, h2, h3⟩ := leaf_eq C hdw h' ha
    exact ⟨by rw [selfWidth2_castU]; exact h1, fun ctx => by rw [instExpr2_castU]; exact h2 ctx, h3⟩
  · obtain ⟨h1, h2, -⟩ := leaf_eq C hdw h' ha
    exact ⟨by rw [selfWidth2_bitSel_castU]; exact h1, fun ctx => by rw [instExpr2_bitSel_castU]; exact h2 ctx, rfl⟩
  · obtain ⟨h1, h2, -⟩ := leaf_eq C hdw h' ha
    exact ⟨by rw [selfWidth2_partSel_castU]; exact h1, fun ctx => by rw [instExpr2_partSel_castU]; exact h2 ctx, rfl⟩

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
  rcases leafRd_unsign h with h' | ⟨n, rfl, h'⟩ | ⟨n, i, rfl, -⟩ | ⟨n, msb, lsb, rfl, -⟩
  · exact rm_leaf h'
  · rw [rigidMax2_castU, selfWidth2_castU]; exact rm_leaf h'
  · rfl
  · rfl

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
  | .bitSel b i, rs, h, _, hacc, tw, hw => by
      obtain ⟨b', hb⟩ := unsign_bitSel b i
      have h' : rdsLeaf? ds (PExpr.bitSel b i).unsign = .ok rs := by
        rw [hb] at h ⊢; simpa [rdsOf?] using h
      exact leaf_caseU C hdw h' hacc tw hw
  | .partSel b m l, rs, h, _, hacc, tw, hw => by
      obtain ⟨b', hb⟩ := unsign_partSel b m l
      have h' : rdsLeaf? ds (PExpr.partSel b m l).unsign = .ok rs := by
        rw [hb] at h ⊢; simpa [rdsOf?] using h
      exact leaf_caseU C hdw h' hacc tw hw
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
        fitExpr2 E elems (some tw) v = (skT v rs).low σ dw tw := by
  intro v rs h hf hacc tw hw
  have hu := unsign_of_rdsOf h
  have := skT_shapeU C hdw v rs (by rw [hu]; exact h) (by rw [hu]; exact hf) hacc tw (by rw [hu]; exact hw)
  rwa [hu] at this

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

/-- The parts of a word-level concatenation (literals, accesses, replications). -/
theorem parts_shapeW (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRdW? ds ps = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → PartsCO σ ns ps →
      selfWidthSum2 E elems ps = some ((partsT ps rs).map (Part.wid σ dw)).sum ∧
        instParts2 E elems ps = (partsT ps rs).map (Part.expr σ) := by
  intro ps rs h hacc hco
  have hu : PExpr.unsignL ps = ps := by
    have := unsign_of_rdsOfW (ds := ds) (e := .concat ps) (rs := rs) (by simpa [rdsOfW?] using h)
    rw [unsign_concat] at this
    injection this
  have := parts_shapeWU C hdw ps rs (by rw [hu]; exact h) hacc (by rw [hu]; exact hco)
  rwa [hu] at this

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

/-- The arithmetic shift right of a signed left operand at a context: the left operand SIGN-extended to the context. -/
theorem ie_ashr_some (tw wl : Nat) (l r : PExpr) (hl : divOperandWidth2 E elems l = some wl) :
    instExpr2 E elems (some tw) (.binary (.m0 (.ashr true)) l r) =
      ctxTrunc2 (some tw) (some (max tw wl)) (.binary (.ashr true)
        (instDivOperand2 E elems true (some (max tw wl)) l)
        (instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r)) := by
  simp [instExpr2, hl]

theorem ie_ashr_none (wl : Nat) (l r : PExpr) (hl : divOperandWidth2 E elems l = some wl) :
    instExpr2 E elems none (.binary (.m0 (.ashr true)) l r) =
      .binary (.ashr true) (instDivOperand2 E elems true (some wl) l)
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
            have hagx : ∀ x' ∈ [x, y], ∀ v ∈ x'.names, E.intVal? v = some (σ v) :=
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
  · have hb : E.intVal? g = some (σ g) := C.agree g (hg g rfl)
    have e1 : instDivOperand2 E elems s c (.genvarRef g) =
        fitDivOperand2 s c (some 32) (.lit (LVec.ofInt 32 (σ g))) := by
      rw [show instDivOperand2 E elems s c (.genvarRef g) =
          fitDivOperand2 s c (some 32) (instExpr2 E elems (some 32) (.genvarRef g)) by simp only [instDivOperand2],
        instExpr2_genvarRef_of_intVal hb] <;> rfl
    have e2 : (skT (.genvarRef g) ([] : List Acc)).width σ dw = 32 := by simp [skT, Sk.width]
    have e3 : (skT (.genvarRef g) ([] : List Acc)).low σ dw 32 = .lit (LVec.ofInt 32 (σ g)) := by
      simp [skT, Sk.low, Aff.eval_var]
    refine ⟨by simp [shiftAmtWidth2, divOperandWidth2, e2], ?_⟩
    rw [e1, e2, e3]
  · have hb : E.intVal? n = some (σ n) := C.agree n (hp n rfl)
    · have e1 : instDivOperand2 E elems s c (.paramRef n none) =
          fitDivOperand2 s c (some 32) (.lit (LVec.ofInt 32 (σ n))) := by
        rw [show instDivOperand2 E elems s c (.paramRef n none) =
            fitDivOperand2 s c (some 32) (instExpr2 E elems (some 32) (.paramRef n none)) by simp only [instDivOperand2],
          instExpr2_paramRef_of_intVal hb] <;> rfl
      have e2 : (skT (.paramRef n none) ([] : List Acc)).width σ dw = 32 := by simp [skT, Sk.width]
      have e3 : (skT (.paramRef n none) ([] : List Acc)).low σ dw 32 = .lit (LVec.ofInt 32 (σ n)) := by
        simp [skT, Sk.low, Aff.eval_var]
      refine ⟨by simp [shiftAmtWidth2, divOperandWidth2, e2], ?_⟩
      rw [e1, e2, e3]
  · have hx : shiftAmtWidth2 E elems x = divOperandWidth2 E elems x := by
      cases x <;> simp_all [shiftAmtWidth2, shOpdRd?]
    rw [hx]
    exact shOpd_shape C hdw h' hacc s c

/-- **An operand of a signed comparison** (`scmpRd?`: a whole signed signal, a sized literal, an unsized constant): its
self-width is its skeleton's, and fitted to a context its skeleton meets the width contract at, it is the skeleton lowered
there. -/
theorem scmpOpd_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {e : PExpr} {ra : List Acc}
    (hacc : ∀ a ∈ ra, AccOK σ DW DG EW ns a) (he : ScmpOpdForm e ra) :
    selfWidth2 E elems e = some ((skT e ra).width σ dw) ∧
      ∀ M, (skT e ra).WidthOkC σ dw M → fitExpr2 E elems (some M) e = (skT e ra).low σ dw M := by
  rcases he with ⟨a, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨m, a, rfl, rfl⟩ | ⟨m, v, hx, rfl⟩
  rotate_left 3
  · -- a sign-extension marker around a whole signed signal: `resizeSigned` of the signal at every context
    have hA : E.widths.lookup a = some (dw a) := by
      rw [C.widths]; exact hdw a (hacc (.whole a) (by simp)).1
    refine ⟨by simp [skT, Sk.width, selfWidth2, hA, Acc.win], fun M _ => ?_⟩
    simp [fitExpr2, rigidExpr, instExpr2, selfWidth2, hA, skT, Sk.low, Sk.width, accExpr, Acc.win]
  · -- a sign-extension marker around a sized literal (the loader's own marker of a signed literal included)
    rcases hx with rfl | ⟨n, rfl⟩
    · refine ⟨by simp [skT, Sk.width, selfWidth2], fun M _ => ?_⟩
      simp [fitExpr2, rigidExpr, instExpr2, selfWidth2, skT, Sk.low, Sk.width]
    · refine ⟨by simp [skT, Sk.width, selfWidth2], fun M _ => ?_⟩
      simp [fitExpr2, rigidExpr, instExpr2, selfWidth2, skT, Sk.low, Sk.width]
  · have hA : E.widths.lookup a = some (dw a) := by
      rw [C.widths]; exact hdw a (hacc (.whole a) (by simp)).1
    refine ⟨by simp [skT, Sk.width, selfWidth2, hA, Acc.win], fun M hM => ?_⟩
    simp only [skT, List.headD_cons, Sk.WidthOkC, Acc.win] at hM
    subst hM
    rw [fit_signedRead hA]
    simp [skT, Sk.low, accExpr]
  · refine ⟨by simp [skT, Sk.width, selfWidth2], fun M hM => ?_⟩
    simp only [skT, Sk.WidthOkC] at hM
    subst hM
    simp [fitExpr2, rigidExpr, selfWidth2, instExpr2, skT, Sk.low]
  · refine ⟨by simp [skT, Sk.width, selfWidth2], fun M _ => ?_⟩
    simp [fitExpr2, rigidExpr, instExpr2, intLit2_eq, skT, Sk.low]

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

/-! ### The left operand of a shift: `instDivOperand2` and its mirror `skD`

`instExpr2` lowers the left operand of a shift through `instDivOperand2` at the operation width `max tw w` (`ie_shl_some`),
not through `fitExpr2`: every leaf is extended to that width before the operations run. `skD1_shape` (the
self-determined positions, `rdsOfD1?`) and `skD_shape` (`rdsOfD?`) are the shape theorem of that instantiation against the
mirror `skD`: the operand's `divOperandWidth2` is its skeleton's width, and at every context at least that wide its
lowering is the mirror's. -/

theorem fitDiv_self (s : Bool) (w : Nat) (x : Expr2) : fitDivOperand2 s (some w) (some w) x = x := by
  simp [fitDivOperand2]

theorem iDO_bin (s : Bool) (b : BinOp) (hb : b = .and ∨ b = .or ∨ b = .xor ∨ b = .add ∨ b = .sub)
    {l r : PExpr} {a c : Nat} (hl : divOperandWidth2 E elems l = some a) (hr : divOperandWidth2 E elems r = some c)
    (k : Nat) :
    instDivOperand2 E elems s (some k) (.binary (.m0 b) l r) =
      .binary b (instDivOperand2 E elems s (some (max k (max a c))) l)
        (instDivOperand2 E elems s (some (max k (max a c))) r) := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [instDivOperand2, hl, hr]

theorem iDO_mul (s : Bool) {l r : PExpr} {a c : Nat} (hl : divOperandWidth2 E elems l = some a)
    (hr : divOperandWidth2 E elems r = some c) (k : Nat) :
    instDivOperand2 E elems s (some k) (.binary .mul l r) =
      .binary .mul (instDivOperand2 E elems s (some (max k (max a c))) l)
        (instDivOperand2 E elems s (some (max k (max a c))) r) := by
  simp [instDivOperand2, hl, hr]

theorem iDO_cmp (s : Bool) (cm : CmpOp) {l r : PExpr} {a c : Nat} (hl : divOperandWidth2 E elems l = some a)
    (hr : divOperandWidth2 E elems r = some c) (k : Nat) :
    instDivOperand2 E elems s (some k) (.binary (.m0 cm.ex) l r) =
      fitDivOperand2 s (some k) (some 1) (.binary cm.ex (instDivOperand2 E elems s (some (max a c)) l)
        (instDivOperand2 E elems s (some (max a c)) r)) := by
  cases cm <;> simp [instDivOperand2, CmpOp.ex, hl, hr]

theorem iDO_bnot (s : Bool) {a : PExpr} {w : Nat} (ha : divOperandWidth2 E elems a = some w) (k : Nat) :
    instDivOperand2 E elems s (some k) (.unary (.m0 .bnot) a) =
      .unary .bnot (instDivOperand2 E elems s (some (max k w)) a) := by
  simp [instDivOperand2, ha]

theorem iDO_ternary (s : Bool) (g : PExpr) {t e : PExpr} {a c : Nat} (ht : divOperandWidth2 E elems t = some a)
    (he : divOperandWidth2 E elems e = some c) (k : Nat) :
    instDivOperand2 E elems s (some k) (.ternary g t e) =
      .ternary (instDivOperand2 E elems false (divOperandWidth2 E elems g) g)
        (instDivOperand2 E elems s (some (max k (max a c))) t)
        (instDivOperand2 E elems s (some (max k (max a c))) e) := by
  simp [instDivOperand2, ht, he]

theorem iDO_shl (s sl : Bool) {l : PExpr} (r : PExpr) {a : Nat} (hl : divOperandWidth2 E elems l = some a) (k : Nat) :
    instDivOperand2 E elems s (some k) (.binary (.m0 (.shl sl)) l r) =
      .binary (.shl sl) (instDivOperand2 E elems s (some (max k a)) l)
        (instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r) := by
  simp [instDivOperand2, hl]

theorem iDO_shr (s sl : Bool) {l : PExpr} (r : PExpr) {a : Nat} (hl : divOperandWidth2 E elems l = some a) (k : Nat) :
    instDivOperand2 E elems s (some k) (.binary (.m0 (.shr sl)) l r) =
      .binary (.shr sl) (instDivOperand2 E elems s (some (max k a)) l)
        (instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r) := by
  simp [instDivOperand2, hl]

theorem iDO_scmp (s : Bool) {op : SymBinOp} {cm : CmpOp} (h : scmpOp? op = some cm) {l r : PExpr} {a c : Nat}
    (hl : divOperandWidth2 E elems l = some a) (hr : divOperandWidth2 E elems r = some c) (k : Nat) :
    instDivOperand2 E elems s (some k) (.binary op l r) =
      fitDivOperand2 s (some k) (some 1) (.scmp cm.ex (instDivOperand2 E elems true (some (max a c)) l)
        (instDivOperand2 E elems true (some (max a c)) r)) := by
  cases op <;> simp [scmpOp?] at h <;> subst h <;> simp [instDivOperand2, CmpOp.ex, hl, hr]

/-- A leaf skeleton's mirror is the leaf, fitted. -/
theorem dz_of_shOpd {ds : List DeclT} {x : PExpr} {rs : List Acc} (h : shOpdRd? ds x = .ok rs) (s : Bool) :
    (skT x rs).dz s = .fit s (skT x rs) := by
  rcases shOpdRd?_cases h with ⟨v, rfl, rfl⟩ | ⟨k, rfl, rfl⟩ | ⟨a, hl, rfl⟩
  · rfl
  · rfl
  · rcases leafKind_of_leafRd hl with ⟨n, rfl⟩ | ⟨b, i, rfl⟩ | ⟨n, is, rfl⟩ | ⟨n, is, m, a', b, rfl⟩ |
      ⟨b, pm, pl, rfl⟩ <;> rfl

/-- **A leaf** (a literal, an unsized constant, one access): at every context, `instDivOperand2` is the fitted leaf. -/
theorem leaf_shapeD (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {x : PExpr} {rs : List Acc}
    (h : shOpdRd? ds x = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (s : Bool) :
    divOperandWidth2 E elems x = some ((skT x rs).width σ dw) ∧
      ∀ c, instDivOperand2 E elems s (some c) x = ((skT x rs).dz s).low σ dw c := by
  refine ⟨(shOpd_shape C hdw h hacc s none).1, fun c => ?_⟩
  rw [dz_of_shOpd h, (shOpd_shape C hdw h hacc s (some c)).2]
  rfl

theorem iDO_ashr (s sa : Bool) {l : PExpr} (r : PExpr) {a : Nat} (hl : divOperandWidth2 E elems l = some a)
    (k : Nat) :
    instDivOperand2 E elems s (some k) (.binary (.m0 (.ashr sa)) l r) =
      .binary (.ashr s) (instDivOperand2 E elems s (some (max k a)) l)
        (instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r) := by
  simp [instDivOperand2, hl]

/-- **A leaf of the left operand of a shift** (a signal access, its signed read included): its `divOperandWidth2` is
its access's width, and `instDivOperand2` at any context fits the access. -/
theorem dleaf_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {a : Acc}
    (h : dLeaf? ds e = .ok [a]) (hacc : AccOK σ DW DG EW ns a) :
    divOperandWidth2 E elems e = some ((Sk.rd a).width σ dw) ∧
      ∀ s c, instDivOperand2 E elems s c e =
        fitDivOperand2 s c (some ((Sk.rd a).width σ dw)) ((Sk.rd a).low σ dw ((Sk.rd a).width σ dw)) := by
  obtain ⟨a', ha', -, -, -, -, hsk⟩ := dLeaf_facts h
  cases ha'
  have hx := shOpd_of_dLeaf h
  have e1 := hsk [a]
  simp only [List.headD_cons] at e1
  refine ⟨?_, fun s c => ?_⟩
  · rw [← dow_uncast, (shOpd_shape C hdw hx (fun x hx' => by simp at hx'; subst hx'; exact hacc) false none).1, e1]
  · rw [← iDO_uncast, (shOpd_shape C hdw hx (fun x hx' => by simp at hx'; subst hx'; exact hacc) s c).2, e1]

theorem skD1_ofLeaf (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {rs : List Acc}
    (hd : dLeaf? ds e = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) :
    divOperandWidth2 E elems e = some ((skD1 e rs).width σ dw) ∧
      ((skD1 e rs).SelfOk σ dw → ∀ s, instDivOperand2 E elems s (some ((skD1 e rs).width σ dw)) e =
        (skD1 e rs).low σ dw ((skD1 e rs).width σ dw)) := by
  obtain ⟨a, rfl, -, -, -, h1, -⟩ := dLeaf_facts hd
  obtain ⟨d1, d2⟩ := dleaf_shape C hdw hd (hacc a (by simp))
  rw [h1]
  simp only [List.headD_cons]
  refine ⟨d1, fun _ s => ?_⟩
  rw [d2, fitDiv_self]

theorem skD_ofLeaf (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {e : PExpr} {s : Bool}
    {rs : List Acc} (hd : dLeaf? ds e = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) :
    divOperandWidth2 E elems e = some ((skD s e rs).width σ dw) ∧
      ∀ c, (skD s e rs).width σ dw ≤ c → (skD s e rs).WidthOkC σ dw c →
        instDivOperand2 E elems s (some c) e = (skD s e rs).low σ dw c := by
  obtain ⟨a, rfl, -, -, h1, -⟩ := dLeaf_facts hd
  obtain ⟨d1, d2⟩ := dleaf_shape C hdw hd (hacc a (by simp))
  rw [h1]
  simp only [List.headD_cons]
  refine ⟨d1, fun c _ _ => ?_⟩
  rw [d2]
  rfl

/-- **`instDivOperand2` of a self-determined operand inside the left operand of a shift** (`rdsOfD1?`): its
`divOperandWidth2` is its skeleton's width, and at that width the instantiation is the skeleton's lowering. -/
theorem skD1_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (rs : List Acc), rdsOfD1? ds v = .ok rs → (∀ a ∈ rs, AccOK σ DW DG EW ns a) →
      divOperandWidth2 E elems v = some ((skD1 v rs).width σ dw) ∧
      ((skD1 v rs).SelfOk σ dw → ∀ s, instDivOperand2 E elems s (some ((skD1 v rs).width σ dw)) v =
        (skD1 v rs).low σ dw ((skD1 v rs).width σ dw))
  | .lit lv, rs, h, hacc => by
      simp only [rdsOfD1?, Except.ok.injEq] at h
      subst h
      obtain ⟨d1, -⟩ := leaf_shapeD C hdw (x := .lit lv) (ds := ds) (rs := []) (by simp [shOpdRd?]) hacc false
      refine ⟨by simpa [skD1, skT] using d1, fun _ s => ?_⟩
      obtain ⟨-, d2⟩ := leaf_shapeD C hdw (x := .lit lv) (ds := ds) (rs := []) (by simp [shOpdRd?]) hacc s
      rw [d2]; simp [skT, skD1, Sk.dz, Sk.low, Sk.width, fitDiv_self]
  | .binary op l r, rs, h, hacc => by
      obtain ⟨hb, ra, rb, hl, hr, rfl⟩ := rdsOfD1?_binary h
      have hla := rdsOfD1?_len l ra hl
      have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
      have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
      have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
      have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
      obtain ⟨Dl, Il⟩ := skD1_shape C hdw l ra hl hacl
      obtain ⟨Dr, Ir⟩ := skD1_shape C hdw r rb hr hacr
      have gate : ∀ g : Gate, op = .m0 g.op → (skD1 (.binary op l r) (ra ++ rb) = .gate g (skD1 l ra) (skD1 r rb)) →
          divOperandWidth2 E elems (.binary op l r) = some ((skD1 (.binary op l r) (ra ++ rb)).width σ dw) ∧
          ((skD1 (.binary op l r) (ra ++ rb)).SelfOk σ dw → ∀ s,
            instDivOperand2 E elems s (some ((skD1 (.binary op l r) (ra ++ rb)).width σ dw)) (.binary op l r) =
              (skD1 (.binary op l r) (ra ++ rb)).low σ dw ((skD1 (.binary op l r) (ra ++ rb)).width σ dw)) := by
        intro g hop hsk
        rw [hsk]
        subst hop
        have hg : g.op = .and ∨ g.op = .or ∨ g.op = .xor ∨ g.op = .add ∨ g.op = .sub := by
          cases g <;> simp [Gate.op]
        refine ⟨by cases g <;> simp [divOperandWidth2, Gate.op, Dl, Dr, Sk.width], fun hso s => ?_⟩
        obtain ⟨hsl, hsr, hwe⟩ := hso
        rw [iDO_bin s g.op hg Dl Dr]
        simp only [Sk.width, Sk.low]
        rw [← hwe, Nat.max_self, Nat.max_self, Il hsl s]
        rw [hwe, Ir hsr s]
      rcases binOk_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact gate .and rfl (by simp [skD1, gateOf, mkGate, e1, e2])
      · exact gate .or rfl (by simp [skD1, gateOf, mkGate, e1, e2])
      · exact gate .xor rfl (by simp [skD1, gateOf, mkGate, e1, e2])
      · have hsk : skD1 (.binary .land l r) (ra ++ rb) = .land (skD1 l ra) (skD1 r rb) := by
          simp [skD1, gateOf, e1, e2]
        rw [hsk]
        refine ⟨by simp [divOperandWidth2, Sk.width], fun hso s => ?_⟩
        rw [instDiv_land, Dl, Dr, Il hso.1, Ir hso.2]
        simp only [Sk.width, Sk.low, fitDiv_self, Sk.low_irrel σ dw (skD1 l ra) hso.1 _ 0,
          Sk.low_irrel σ dw (skD1 r rb) hso.2 _ 0]
      · have hsk : skD1 (.binary .lor l r) (ra ++ rb) = .lor (skD1 l ra) (skD1 r rb) := by
          simp [skD1, gateOf, e1, e2]
        rw [hsk]
        refine ⟨by simp [divOperandWidth2, Sk.width], fun hso s => ?_⟩
        rw [instDiv_lor, Dl, Dr, Il hso.1, Ir hso.2]
        simp only [Sk.width, Sk.low, fitDiv_self, Sk.low_irrel σ dw (skD1 l ra) hso.1 _ 0,
          Sk.low_irrel σ dw (skD1 r rb) hso.2 _ 0]
      · have hsk : skD1 (.binary (.m0 .eq) l r) (ra ++ rb) = .cmp .eq (skD1 l ra) (skD1 r rb) := by
          simp [skD1, gateOf, e1, e2]
        rw [hsk]
        refine ⟨by simp [divOperandWidth2, Sk.width], fun hso s => ?_⟩
        obtain ⟨hsl, hsr, hwe⟩ := hso
        have hc := iDO_cmp (E := E) (elems := elems) s .eq Dl Dr ((Sk.cmp .eq (skD1 l ra) (skD1 r rb)).width σ dw)
        simp only [CmpOp.ex] at hc
        rw [hc]
        simp only [Sk.width, Sk.low, fitDiv_self, CmpOp.ex]
        rw [← hwe, Nat.max_self, Il hsl s]
        rw [hwe, Ir hsr s]
      · have hsk : skD1 (.binary (.m0 .ne) l r) (ra ++ rb) = .cmp .ne (skD1 l ra) (skD1 r rb) := by
          simp [skD1, gateOf, e1, e2]
        rw [hsk]
        refine ⟨by simp [divOperandWidth2, Sk.width], fun hso s => ?_⟩
        obtain ⟨hsl, hsr, hwe⟩ := hso
        have hc := iDO_cmp (E := E) (elems := elems) s .ne Dl Dr ((Sk.cmp .ne (skD1 l ra) (skD1 r rb)).width σ dw)
        simp only [CmpOp.ex] at hc
        rw [hc]
        simp only [Sk.width, Sk.low, fitDiv_self, CmpOp.ex]
        rw [← hwe, Nat.max_self, Il hsl s]
        rw [hwe, Ir hsr s]
  | .unary op a, rs, h, hacc => by
      obtain ⟨hop, ha⟩ := rdsOfD1?_unary h
      obtain ⟨Da, Ia⟩ := skD1_shape C hdw a rs ha hacc
      rcases hop with rfl | rfl
      · have hsk : skD1 (.unary (.m0 .bnot) a) rs = .bnot (skD1 a rs) := by simp [skD1]
        rw [hsk]
        refine ⟨by simp [divOperandWidth2, Da, Sk.width], fun hso s => ?_⟩
        rw [iDO_bnot s Da]
        simp only [Sk.width, Sk.low, Nat.max_self]
        rw [Ia hso s]
      · have hsk : skD1 (.unary (.m0 .lnot) a) rs = .lnot (skD1 a rs) := by simp [skD1]
        rw [hsk]
        refine ⟨by simp [divOperandWidth2, Sk.width], fun hso s => ?_⟩
        rw [instDiv_lnot, Da, Ia hso false]
        simp only [Sk.width, Sk.low, fitDiv_self, Sk.low_irrel σ dw (skD1 a rs) hso _ 0]
  | .ternary g t e, rs, h, hacc => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := rdsOfD1?_ternary h
      have hc' := rdsOfD1?_len g rc hc
      have ht' := rdsOfD1?_len t rt ht
      have e1 : (rc ++ rt ++ re).take (cnt g) = rc := by
        rw [List.append_assoc]; exact List.take_left' hc'
      have e2 : (rc ++ rt ++ re).drop (cnt g) = rt ++ re := by
        rw [List.append_assoc]; exact List.drop_left' hc'
      have e3 : (rt ++ re).take (cnt t) = rt := List.take_left' ht'
      have e4 : (rt ++ re).drop (cnt t) = re := List.drop_left' ht'
      have hsk : skD1 (.ternary g t e) (rc ++ rt ++ re) = .tern (skD1 g rc) (skD1 t rt) (skD1 e re) := by
        simp only [skD1, e1, e2, e3, e4]
      rw [hsk]
      obtain ⟨Dg, Ig⟩ := skD1_shape C hdw g rc hc
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_left _ hx)))
      obtain ⟨Dt, It⟩ := skD1_shape C hdw t rt ht
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx)))
      obtain ⟨De, Ie⟩ := skD1_shape C hdw e re he (fun x hx => hacc x (List.mem_append_right _ hx))
      refine ⟨by simp [divOperandWidth2, Dt, De, Sk.width], fun hso s => ?_⟩
      obtain ⟨hsg, hwg, hst, hse, hwe⟩ := hso
      rw [iDO_ternary s g Dt De, Dg, Ig hsg false]
      simp only [Sk.width, Sk.low]
      rw [← hwe, Nat.max_self, Nat.max_self, It hst s,
        Sk.low_irrel σ dw (skD1 g rc) hsg ((skD1 g rc).width σ dw) 0]
      rw [hwe, Ie hse s]
  | .reduce op a, rs, h, hacc => by
      have ha : rdsOfD1? ds a = .ok rs := by simpa [rdsOfD1?] using h
      obtain ⟨Da, Ia⟩ := skD1_shape C hdw a rs ha hacc
      have hsk : skD1 (.reduce op a) rs = .red op (skD1 a rs) := by simp [skD1]
      rw [hsk]
      refine ⟨by simp [divOperandWidth2, Sk.width], fun hso s => ?_⟩
      rw [instDiv_reduce, Da, Ia hso false]
      simp only [Sk.width, Sk.low, fitDiv_self, Sk.low_irrel σ dw (skD1 a rs) hso _ 0]
  | .resize m e, rs, h, hacc => by
      have he : rdsOfD1? ds e = .ok rs := by simpa [rdsOfD1?] using h
      obtain ⟨De, Ie⟩ := skD1_shape C hdw e rs he hacc
      have hsk : skD1 (.resize m e) rs = skD1 e rs := by simp [skD1]
      rw [hsk]
      refine ⟨by simpa [divOperandWidth2] using De, fun hso s => ?_⟩
      rw [instDiv_resizeG s _ m e (rdsOfD1?_ne_genvar he)]
      simpa [Option.orElse] using Ie hso false
  | .signedResize m e, rs, h, hacc => by
      have he : rdsOfD1? ds e = .ok rs := by simpa [rdsOfD1?] using h
      obtain ⟨De, Ie⟩ := skD1_shape C hdw e rs he hacc
      have hsk : skD1 (.signedResize m e) rs = skD1 e rs := by simp [skD1]
      rw [hsk]
      refine ⟨by simpa [divOperandWidth2] using De, fun hso s => ?_⟩
      rw [instDiv_sresize s _ m e]
      simpa [Option.orElse] using Ie hso true
  | .concat _, rs, h, _ => by simp [rdsOfD1?] at h
  | .ident _, rs, h, hacc | .bitSel .., rs, h, hacc | .partSel .., rs, h, hacc | .arrayElem .., rs, h, hacc
  | .arrayPart .., rs, h, hacc | .cast .., rs, h, hacc | .fill _, rs, h, hacc | .paramRef .., rs, h, hacc
  | .genvarRef _, rs, h, hacc | .enumRef .., rs, h, hacc | .int _, rs, h, hacc | .sysCall .., rs, h, hacc
  | .squash2 .., rs, h, hacc | .unsupported .., rs, h, hacc | .repl .., rs, h, hacc => by
      exact skD1_ofLeaf C hdw (by simpa [rdsOfD1?] using h) hacc

/-- **A concatenation part inside the left operand of a shift** (a literal or one access, under conversion markers):
at its own width it lowers to the part's expression. -/
theorem part_shapeD1 (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {p : PExpr} {rs : List Acc}
    (hp : partRdD? ds p = .ok rs) (hacc : ∀ a ∈ rs, AccOK σ DW DG EW ns a) (tl : List Acc) :
    divOperandWidth2 E elems p = some ((dPart p (rs ++ tl)).wid σ dw) ∧
      instDivOperand2 E elems false (divOperandWidth2 E elems p) p = (dPart p (rs ++ tl)).expr σ := by
  rcases partRdD?_cases hp with ⟨v, hv, rfl⟩ | ⟨hnl, hl⟩
  · rw [dPart_lit hv]
    have hd : divOperandWidth2 E elems p = some v.width := by rw [← dow_peel, hv]; simp [divOperandWidth2]
    refine ⟨by simpa [Part.wid] using hd, ?_⟩
    rw [hd, iDO_peel p false v.width (by rw [hv]; intro g h; cases h), hv]
    obtain ⟨-, d2⟩ := shOpd_shape C hdw (x := .lit v) (ds := ds) (rs := []) (by simp [shOpdRd?]) (by simp)
      (p.peelSg false) (some v.width)
    rw [d2]
    simp [skT, Sk.width, Sk.low, fitDiv_self, Part.expr]
  · obtain ⟨a, rfl, -⟩ := dLeaf_facts hl
    rw [dPart_rd hnl]
    simp only [List.singleton_append, List.headD_cons]
    obtain ⟨d1, d2⟩ := dleaf_shape C hdw hl (hacc a (by simp))
    have hd : divOperandWidth2 E elems p = some ((Sk.rd a).width σ dw) := by rw [← dow_peel, d1]
    refine ⟨by simpa [Part.wid, Sk.width] using hd, ?_⟩
    rw [hd, iDO_peel p false _ (dLeaf_ne_genvar hl), d2, fitDiv_self]
    rfl

/-- **A replication inside the left operand of a shift**: the fitted part of its skeleton. -/
theorem repl_shapeDD (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} {c a : PExpr} {rs : List Acc}
    (h : repRdD? ds c a = .ok rs) (hacc : ∀ x ∈ rs, AccOK σ DW DG EW ns x) (hco : ConstOK σ ns (.repl c a))
    (tl : List Acc) :
    divOperandWidth2 E elems (.repl c a) = some ((repPartD c a (rs ++ tl)).wid σ dw) ∧
      ∀ s k, instDivOperand2 E elems s (some k) (.repl c a) =
        fitDivOperand2 s (some k) (some ((repPartD c a (rs ++ tl)).wid σ dw)) ((repPartD c a (rs ++ tl)).expr σ) := by
  obtain ⟨k, hk, harg⟩ := repRdD?_cases h
  obtain ⟨hev, h0⟩ := repl_facts C hk hco
  have hrk : repAff c = k := by simp [repAff, hk]
  obtain ⟨x, rfl, hx⟩ := repArgRdD?_cases harg
  have hpx : partRdD? ds x = .ok rs := by
    unfold partRdD?
    rcases hx with ⟨v, hv, rfl⟩ | ⟨hl, hnl, -⟩
    · simp [hv]
    · split
      · rename_i v hv; exact absurd hv (hnl v)
      · rename_i op a b hb; rw [hb] at hl; simp [dLeaf?, PExpr.uncast, rdsLeaf?, leafRd?] at hl
      · exact hl
  obtain ⟨d1, d2⟩ := part_shapeD1 C hdw hpx hacc tl
  have hrp : ∃ w, (repPartD c (.concat [x]) (rs ++ tl)).wid σ dw = (k.eval σ).toNat * w ∧
      (dPart x (rs ++ tl)).wid σ dw = w ∧
      (repPartD c (.concat [x]) (rs ++ tl)).expr σ = .repl (k.eval σ).toNat (.concat #[(dPart x (rs ++ tl)).expr σ]) := by
    rcases hx with ⟨v, hv, rfl⟩ | ⟨hl, hnl, hnw⟩
    · refine ⟨v.width, ?_, ?_, ?_⟩ <;> simp [repPartD_lit hv, dPart_lit hv, Part.wid, Part.expr, hrk]
    · obtain ⟨a', rfl, -⟩ := dLeaf_facts hl
      have hnw' : ∀ n, a' ≠ .whole n := fun n hn => hnw n (by rw [hn])
      refine ⟨Acc.wid σ a', ?_, ?_, ?_⟩
      · simp [repPartD_rd hnl, Part.wid, hrk]
      · simp [dPart_rd hnl, Part.wid, win_wid_of_ne_whole hnw']
      · simp [repPartD_rd hnl, dPart_rd hnl, Part.expr, hrk]
  obtain ⟨w, hw1, hw2, hw3⟩ := hrp
  rw [hw2] at d1
  have hda : divOperandWidth2 E elems (.concat [x]) = some (w + 0) := by
    simp [divOperandWidth2, divOperandWidthSum2, d1]
  have hds : divOperandWidthSum2 E elems [x] = some (w + 0) := by simpa [divOperandWidth2] using hda
  have hdr : divOperandWidth2 E elems (.repl c (.concat [x])) = some ((k.eval σ).toNat * w) := by
    simp [divOperandWidth2, hev, h0, hds]
  refine ⟨by rw [hdr, hw1], fun s k' => ?_⟩
  rw [instDiv_repl s (some k') c _ hev h0, hdr, hw1, hw3, hda, instDiv_concat, hds, fitDiv_self,
    instDivParts2_cons, instDivParts2_nil, d2]

theorem parts_shapeDD (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRdD? ds ps = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → PartsCO σ ns ps →
      divOperandWidthSum2 E elems ps = some ((partsTD ps rs).map (Part.wid σ dw)).sum ∧
        instDivParts2 E elems ps = (partsTD ps rs).map (Part.expr σ)
  | [], rs, h, _, _ => by
      simp only [partsRdD?, Except.ok.injEq] at h
      subst h
      simp [partsTD, divOperandWidthSum2, instDivParts2_nil]
  | p :: ps, rs, h, hacc, hco => by
      simp only [partsRdD?] at h
      rcases hp : partRdDW? ds p with e | ra
      · simp [hp] at h
      · rcases hq : partsRdD? ds ps with e | rb
        · simp [hp, hq] at h
        · simp only [hp, hq, Except.ok.injEq] at h
          subst h
          obtain ⟨hco', hn, hc⟩ := partsCO_cons hco
          obtain ⟨ih1, ih2⟩ := parts_shapeDD C hdw ps rb hq (fun x hx => hacc x (List.mem_append_right _ hx)) hco'
          have hla := partRdDW_len hp
          have e2 : (ra ++ rb).drop (cnt p) = rb := List.drop_left' hla
          have hacl : ∀ x ∈ ra, AccOK σ DW DG EW ns x := fun x hx => hacc x (List.mem_append_left _ hx)
          have key : divOperandWidth2 E elems p = some ((partTD p (ra ++ rb)).wid σ dw) ∧
              instDivOperand2 E elems false (divOperandWidth2 E elems p) p = (partTD p (ra ++ rb)).expr σ := by
            rcases partRdDW?_cases hp with ⟨c, a, rfl, h'⟩ | ⟨hnr, h'⟩
            · obtain ⟨D, I⟩ := repl_shapeDD C hdw h' hacl ⟨fun n hn' => hn n hn', fun k hk => hc k hk⟩ rb
              refine ⟨D, ?_⟩
              rw [D, I, fitDiv_self]
              rfl
            · rw [partTD_of_ne hnr]
              exact part_shapeD1 C hdw h' hacl rb
          rw [partsTD_cons, e2]
          refine ⟨?_, ?_⟩
          · simp [divOperandWidthSum2, key.1, ih1, Nat.add_comm]
          · rw [instDivParts2_cons, ih2, key.2]
            rfl

/-- **`instDivOperand2` of the left operand of a shift** (`rdsOfD?` at the signedness `s` it is lowered with): its
`divOperandWidth2` is its skeleton's width, and at every context `c` at least that wide where the skeleton meets the
width contract, the instantiation is the skeleton lowered at `c`. -/
theorem skD_shape (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {ds : List DeclT} :
    ∀ (v : PExpr) (s : Bool) (rs : List Acc), rdsOfD? ds s v = .ok rs →
      (∀ a ∈ rs, AccOK σ DW DG EW ns a) → ConstOK σ ns v →
      divOperandWidth2 E elems v = some ((skD s v rs).width σ dw) ∧
      ∀ c, (skD s v rs).width σ dw ≤ c → (skD s v rs).WidthOkC σ dw c →
        instDivOperand2 E elems s (some c) v = (skD s v rs).low σ dw c
  | .lit lv, s, rs, h, hacc, _ => by
      simp only [rdsOfD?, Except.ok.injEq] at h
      subst h
      obtain ⟨d1, d2⟩ := leaf_shapeD C hdw (x := .lit lv) (ds := ds) (rs := []) (by simp [shOpdRd?]) hacc s
      exact ⟨by simpa [skD, skT, Sk.width] using d1, fun c _ _ => by rw [d2 c]; rfl⟩
  | .int k, s, rs, h, hacc, _ => by
      simp only [rdsOfD?, Except.ok.injEq] at h
      subst h
      obtain ⟨d1, d2⟩ := leaf_shapeD C hdw (x := .int k) (ds := ds) (rs := []) (by simp [shOpdRd?]) hacc s
      exact ⟨by simpa [skD, skT, Sk.width] using d1, fun c _ _ => by rw [d2 c]; rfl⟩
  | .binary op l r, s, rs, h, hacc, hcn => by
      rcases rdsOfD?_binary h with ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨hb, ra, rb, hl, hr, rfl⟩ |
        ⟨hb0, hb1, hb, ra, rb, hl, hr, rfl⟩
      · -- `& | ^ + - *` and the six comparisons
        have hla := rdsOfD?_len l s ra hl
        have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
        have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
        have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
        have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
        obtain ⟨Dl, Il⟩ := skD_shape C hdw l s ra hl hacl (cok_binary_l hcn)
        obtain ⟨Dr, Ir⟩ := skD_shape C hdw r s rb hr hacr (cok_binary_r hcn)
        have opw : ∀ b : BinOp, (b = .and ∨ b = .or ∨ b = .xor ∨ b = .add ∨ b = .sub) →
            skD s (.binary (.m0 b) l r) (ra ++ rb) = mkOpW b (skD s l ra) (skD s r rb) →
            divOperandWidth2 E elems (.binary (.m0 b) l r) = some ((skD s (.binary (.m0 b) l r) (ra ++ rb)).width σ dw) ∧
            ∀ c, (skD s (.binary (.m0 b) l r) (ra ++ rb)).width σ dw ≤ c →
              (skD s (.binary (.m0 b) l r) (ra ++ rb)).WidthOkC σ dw c →
                instDivOperand2 E elems s (some c) (.binary (.m0 b) l r) =
                  (skD s (.binary (.m0 b) l r) (ra ++ rb)).low σ dw c := by
          intro b hb' hsk
          rw [hsk]
          have hwid : (mkOpW b (skD s l ra) (skD s r rb)).width σ dw =
              max ((skD s l ra).width σ dw) ((skD s r rb).width σ dw) := by
            rcases hb' with rfl | rfl | rfl | rfl | rfl <;> rfl
          refine ⟨by rw [hwid]; rcases hb' with rfl | rfl | rfl | rfl | rfl <;> simp [divOperandWidth2, Dl, Dr],
            fun c hc hwc => ?_⟩
          rw [hwid] at hc
          have hl' : (skD s l ra).width σ dw ≤ c := Nat.le_trans (Nat.le_max_left _ _) hc
          have hr' : (skD s r rb).width σ dw ≤ c := Nat.le_trans (Nat.le_max_right _ _) hc
          have hmax : max c (max ((skD s l ra).width σ dw) ((skD s r rb).width σ dw)) = c := Nat.max_eq_left hc
          have hW : (skD s l ra).WidthOkC σ dw c ∧ (skD s r rb).WidthOkC σ dw c := by
            rcases hb' with rfl | rfl | rfl | rfl | rfl <;> simp only [mkOpW, mkGate, Sk.WidthOkC] at hwc <;>
              first | exact hwc | exact ⟨hwc.1, hwc.2.1⟩
          rw [iDO_bin s b hb' Dl Dr c, hmax, Il c hl' hW.1, Ir c hr' hW.2]
          rcases hb' with rfl | rfl | rfl | rfl | rfl <;> rfl
        rcases ctxOpW_cases hb with rfl | rfl | rfl | rfl | rfl | rfl | ⟨cm, rfl⟩
        · exact opw .and (Or.inl rfl) (by simp [skD, gateOf, mkGate, mkOpW, e1, e2])
        · exact opw .or (Or.inr (Or.inl rfl)) (by simp [skD, gateOf, mkGate, mkOpW, e1, e2])
        · exact opw .xor (Or.inr (Or.inr (Or.inl rfl))) (by simp [skD, gateOf, mkGate, mkOpW, e1, e2])
        · exact opw .add (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by simp [skD, gateOf, mkGate, mkOpW, e1, e2])
        · exact opw .sub (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (by simp [skD, gateOf, mkGate, mkOpW, e1, e2])
        · -- `*`
          have hsk : skD s (.binary .mul l r) (ra ++ rb) = .mul (skD s l ra) (skD s r rb) := by
            simp [skD, gateOf, e1, e2]
          rw [hsk]
          refine ⟨by simp [divOperandWidth2, Dl, Dr, Sk.width], fun c hc hwc => ?_⟩
          simp only [Sk.width] at hc
          simp only [Sk.WidthOkC] at hwc
          rw [iDO_mul s Dl Dr c, Nat.max_eq_left hc, Il c (Nat.le_trans (Nat.le_max_left _ _) hc) hwc.1,
            Ir c (Nat.le_trans (Nat.le_max_right _ _) hc) hwc.2.1]
          rfl
        · -- a comparison: one bit, fitted; its operands at the wider of their own widths
          have hsk : skD s (.binary (.m0 cm.ex) l r) (ra ++ rb) = .fit s (.cmp cm (skD s l ra) (skD s r rb)) := by
            cases cm <;> simp [skD, gateOf, CmpOp.ex, e1, e2]
          rw [hsk]
          refine ⟨by cases cm <;> simp [divOperandWidth2, CmpOp.ex, Sk.width], fun c _ hwc => ?_⟩
          simp only [Sk.WidthOkC, Sk.width] at hwc
          obtain ⟨-, hwl, hwr⟩ := hwc
          rw [iDO_cmp s cm Dl Dr c, Il _ (Nat.le_max_left _ _) hwl, Ir _ (Nat.le_max_right _ _) hwr]
          simp only [Sk.low, Sk.width]
      · -- `&&`, `||`: one bit, fitted; self-determined operands
        have hla := rdsOfD1?_len l ra hl
        have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
        have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
        have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
        have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
        obtain ⟨Dl, Il⟩ := skD1_shape C hdw l ra hl hacl
        obtain ⟨Dr, Ir⟩ := skD1_shape C hdw r rb hr hacr
        rcases selfOpW_cases hb with rfl | rfl
        · have hsk : skD s (.binary .land l r) (ra ++ rb) = .fit s (.land (skD1 l ra) (skD1 r rb)) := by
            simp [skD, gateOf, e1, e2]
          rw [hsk]
          refine ⟨by simp [divOperandWidth2, Sk.width], fun c _ hwc => ?_⟩
          simp only [Sk.WidthOkC, Sk.width] at hwc
          obtain ⟨-, hsl, hsr⟩ := hwc
          rw [instDiv_land, Dl, Dr, Il hsl false, Ir hsr false]
          simp only [Sk.low, Sk.width, Sk.low_irrel σ dw (skD1 l ra) hsl _ 0,
            Sk.low_irrel σ dw (skD1 r rb) hsr _ 0]
        · have hsk : skD s (.binary .lor l r) (ra ++ rb) = .fit s (.lor (skD1 l ra) (skD1 r rb)) := by
            simp [skD, gateOf, e1, e2]
          rw [hsk]
          refine ⟨by simp [divOperandWidth2, Sk.width], fun c _ hwc => ?_⟩
          simp only [Sk.WidthOkC, Sk.width] at hwc
          obtain ⟨-, hsl, hsr⟩ := hwc
          rw [instDiv_lor, Dl, Dr, Il hsl false, Ir hsr false]
          simp only [Sk.low, Sk.width, Sk.low_irrel σ dw (skD1 l ra) hsl _ 0,
            Sk.low_irrel σ dw (skD1 r rb) hsr _ 0]
      · -- a shift inside, lowered without truncation at the context, its left operand at `s`
        have hsh := shOpW_of_dShOk hb
        have hla := rdsOfD?_len l s ra hl
        have e1 : (ra ++ rb).take (cnt l) = ra := List.take_left' hla
        have e2 : (ra ++ rb).drop (cnt l) = rb := List.drop_left' hla
        have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
        have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
        obtain ⟨Dl, Il⟩ := skD_shape C hdw l s ra hl hacl (cok_binary_l hcn)
        have hR := shAmt_shape C hdw hr hacr (fun g hgr => hcn.1 g (cnames_amount hsh hgr))
          (fun n hnr => hcn.1 n (cnames_amount_param hsh hnr)) false
        have hRexp : instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r =
            (skAmt r rb).low σ dw ((skAmt r rb).width σ dw) := by
          rw [skAmt_eq hr, (hR none).1, (hR _).2]
          simp [fitDivOperand2]
        rcases dShOk_cases hb with ⟨sl, rfl⟩ | rfl | ⟨rfl, rfl⟩
        · have hsk : skD s (.binary (.m0 (.shl sl)) l r) (ra ++ rb) = .sh true sl (skD s l ra) (skAmt r rb) := by
            simp [skD, gateOf, e1, e2]
          rw [hsk]
          refine ⟨by simp [divOperandWidth2, Dl, Sk.width], fun c hc hwc => ?_⟩
          simp only [Sk.WidthOkC, Sk.width] at hc hwc
          rw [iDO_shl s sl r Dl c, Il _ (Nat.le_max_right _ _) hwc.1, hRexp]
          simp only [Sk.low]
          rw [if_pos (Nat.max_le.mpr ⟨Nat.le_refl _, hc⟩)]
          rfl
        · have hsk : skD s (.binary (.m0 (.shr false)) l r) (ra ++ rb) = .sh false false (skD s l ra) (skAmt r rb) := by
            simp [skD, gateOf, e1, e2]
          rw [hsk]
          refine ⟨by simp [divOperandWidth2, Dl, Sk.width], fun c hc hwc => ?_⟩
          simp only [Sk.WidthOkC, Sk.width] at hc hwc
          rw [iDO_shr s false r Dl c, Il _ (Nat.le_max_right _ _) hwc.1, hRexp]
          simp only [Sk.low]
          rw [if_pos (Nat.max_le.mpr ⟨Nat.le_refl _, hc⟩)]
          rfl
        · have hsk : skD true (.binary (.m0 (.ashr true)) l r) (ra ++ rb) =
              .sh false true (skD true l ra) (skAmt r rb) := by
            simp [skD, gateOf, e1, e2]
          rw [hsk]
          refine ⟨by simp [divOperandWidth2, Dl, Sk.width], fun c hc hwc => ?_⟩
          simp only [Sk.WidthOkC, Sk.width] at hc hwc
          rw [iDO_ashr true true r Dl c, Il _ (Nat.le_max_right _ _) hwc.1, hRexp]
          simp only [Sk.low]
          rw [if_pos (Nat.max_le.mpr ⟨Nat.le_refl _, hc⟩)]
          rfl
  | .unary op a, s, rs, h, hacc, hcn => by
      rcases rdsOfD?_unary h with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
      · obtain ⟨Da, Ia⟩ := skD_shape C hdw a s rs ha hacc (cok_unary hcn)
        have hsk : skD s (.unary (.m0 .bnot) a) rs = .bnot (skD s a rs) := by simp [skD]
        rw [hsk]
        refine ⟨by simp [divOperandWidth2, Da, Sk.width], fun c hc hwc => ?_⟩
        simp only [Sk.width] at hc
        simp only [Sk.WidthOkC] at hwc
        rw [iDO_bnot s Da c, Nat.max_eq_left hc, Ia c hc hwc.1]
        rfl
      · obtain ⟨Da, Ia⟩ := skD1_shape C hdw a rs ha hacc
        have hsk : skD s (.unary (.m0 .lnot) a) rs = .fit s (.lnot (skD1 a rs)) := by simp [skD]
        rw [hsk]
        refine ⟨by simp [divOperandWidth2, Sk.width], fun c _ hwc => ?_⟩
        simp only [Sk.WidthOkC, Sk.width] at hwc
        obtain ⟨-, hsa⟩ := hwc
        rw [instDiv_lnot, Da, Ia hsa false]
        simp only [Sk.low, Sk.width, Sk.low_irrel σ dw (skD1 a rs) hsa _ 0]
  | .ternary g t e, s, rs, h, hacc, hcn => by
      obtain ⟨rc, rt, re, hc, ht, he, rfl⟩ := rdsOfD?_ternary h
      have hc' := rdsOfD1?_len g rc hc
      have ht' := rdsOfD?_len t s rt ht
      have e1 : (rc ++ rt ++ re).take (cnt g) = rc := by
        rw [List.append_assoc]; exact List.take_left' hc'
      have e2 : (rc ++ rt ++ re).drop (cnt g) = rt ++ re := by
        rw [List.append_assoc]; exact List.drop_left' hc'
      have e3 : (rt ++ re).take (cnt t) = rt := List.take_left' ht'
      have e4 : (rt ++ re).drop (cnt t) = re := List.drop_left' ht'
      have hsk : skD s (.ternary g t e) (rc ++ rt ++ re) = .tern (skD1 g rc) (skD s t rt) (skD s e re) := by
        simp only [skD, e1, e2, e3, e4]
      rw [hsk]
      obtain ⟨Dg, Ig⟩ := skD1_shape C hdw g rc hc
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_left _ hx)))
      obtain ⟨Dt, It⟩ := skD_shape C hdw t s rt ht
        (fun x hx => hacc x (List.mem_append_left _ (List.mem_append_right _ hx))) (cok_ternary_t hcn)
      obtain ⟨De, Ie⟩ := skD_shape C hdw e s re he
        (fun x hx => hacc x (List.mem_append_right _ hx)) (cok_ternary_e hcn)
      refine ⟨by simp [divOperandWidth2, Dt, De, Sk.width], fun c hc hwc => ?_⟩
      simp only [Sk.width] at hc
      simp only [Sk.WidthOkC] at hwc
      obtain ⟨hsg, hwg, hwt, hwe⟩ := hwc
      rw [iDO_ternary s g Dt De c, Nat.max_eq_left hc, Dg, Ig hsg false,
        It c (Nat.le_trans (Nat.le_max_left _ _) hc) hwt, Ie c (Nat.le_trans (Nat.le_max_right _ _) hc) hwe]
      simp only [Sk.low]
      rw [Sk.low_irrel σ dw (skD1 g rc) hsg ((skD1 g rc).width σ dw) 0]
  | .reduce op a, s, rs, h, hacc, _ => by
      have ha : rdsOfD1? ds a = .ok rs := by simpa [rdsOfD?] using h
      obtain ⟨Da, Ia⟩ := skD1_shape C hdw a rs ha hacc
      have hsk : skD s (.reduce op a) rs = .fit s (.red op (skD1 a rs)) := by simp [skD]
      rw [hsk]
      refine ⟨by simp [divOperandWidth2, Sk.width], fun c _ hwc => ?_⟩
      simp only [Sk.WidthOkC, Sk.width] at hwc
      obtain ⟨-, hsa⟩ := hwc
      rw [instDiv_reduce, Da, Ia hsa false]
      simp only [Sk.low, Sk.width, Sk.low_irrel σ dw (skD1 a rs) hsa _ 0]
  | .concat ps, s, rs, h, hacc, hcn => by
      have h' : partsRdD? ds ps = .ok rs := by simpa [rdsOfD?] using h
      obtain ⟨d1, d2⟩ := parts_shapeDD C hdw ps rs h' hacc hcn
      refine ⟨by simpa [divOperandWidth2, skD, Sk.width] using d1, fun c _ _ => ?_⟩
      rw [instDiv_concat, d1, d2]
      simp [skD, Sk.width, Sk.low]
  | .repl cn a, s, rs, h, hacc, hcn => by
      have h' : repRdD? ds cn a = .ok rs := by simpa [rdsOfD?] using h
      obtain ⟨D, I⟩ := repl_shapeDD C hdw h' hacc hcn []
      rw [List.append_nil] at D I
      refine ⟨by simpa [skD, Sk.width] using D, fun c _ _ => ?_⟩
      rw [I]
      simp [skD, Sk.low, Sk.width]
  | .resize m e, s, rs, h, hacc, hcn => by
      have he : rdsOfD? ds false e = .ok rs := by simpa [rdsOfD?] using h
      obtain ⟨De, Ie⟩ := skD_shape C hdw e false rs he hacc (cok_resize hcn)
      have hsk : skD s (.resize m e) rs = skD false e rs := by simp [skD]
      rw [hsk]
      refine ⟨by simpa [divOperandWidth2] using De, fun c hc hwc => ?_⟩
      rw [instDiv_resizeG s (some c) m e (rdsOfD?_ne_genvar he)]
      simpa [Option.orElse] using Ie c hc hwc
  | .signedResize m e, s, rs, h, hacc, _ => by
      obtain ⟨hn, he⟩ := rdsOfD?_sresize h
      have hco : ConstOK σ ns e := by
        obtain ⟨h1, h2⟩ := noConst_spec e hn
        exact ⟨by simp [h1], by simp [h2]⟩
      obtain ⟨De, Ie⟩ := skD_shape C hdw e true rs he hacc hco
      have hsk : skD s (.signedResize m e) rs = skD true e rs := by simp [skD]
      rw [hsk]
      refine ⟨by simpa [divOperandWidth2] using De, fun c hc hwc => ?_⟩
      rw [instDiv_sresize s (some c) m e]
      simpa [Option.orElse] using Ie c hc hwc
  | .ident _, _, rs, h, hacc, _ | .bitSel .., _, rs, h, hacc, _ | .partSel .., _, rs, h, hacc, _
  | .arrayElem .., _, rs, h, hacc, _ | .arrayPart .., _, rs, h, hacc, _ | .cast .., _, rs, h, hacc, _
  | .fill _, _, rs, h, hacc, _ | .paramRef .., _, rs, h, hacc, _ | .genvarRef _, _, rs, h, hacc, _
  | .enumRef .., _, rs, h, hacc, _ | .sysCall .., _, rs, h, hacc, _ | .squash2 .., _, rs, h, hacc, _
  | .unsupported .., _, rs, h, hacc, _ =>
      skD_ofLeaf C hdw (by simpa [rdsOfD?] using h) hacc

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
      rcases rdsOfW?_binary h with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨cm, hcm, hs⟩
      · rw [unsignOp_of_ctxOpW hb] at hu; cases hu
      · rw [unsignOp_of_selfOpW hb] at hu; cases hu
      · -- a run-time shift (WP-B2 gate 3): the left operand through `instDivOperand2`, its mirror `skD`
        have hacl : ∀ a ∈ ra, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_left _ ha)
        have hacr : ∀ a ∈ rb, AccOK σ DW DG EW ns a := fun a ha => hacc a (List.mem_append_right _ ha)
        have hR := shAmt_shape C hdw hr hacr (fun g hgr => hcn.1 g (cnames_amount hb hgr))
          (fun n hnr => hcn.1 n (cnames_amount_param hb hnr)) false
        have hRexp : instDivOperand2 E elems false (shiftAmtWidth2 E elems r) r =
            (skT r rb).low σ dw ((skT r rb).width σ dw) := by
          rw [(hR none).1]
          rw [(hR _).2]
          simp [fitDivOperand2]
        -- the left operand: its `divOperandWidth2`, and its lowering at every context at least that wide
        obtain ⟨hlsw, hLexp⟩ := skD_shape C hdw l (shSign op) ra hl hacl (cok_binary_l hcn)
        obtain ⟨d, hd, hsk⟩ := skT_sh (rb := rb) hb (rdsOfD?_len l _ ra hl)
        rw [hsk] at hw ⊢
        simp only [Sk.WidthOkC] at hw
        -- at the context `tw`: the operation width `max tw w`
        have hAt : instDivOperand2 E elems (shSign op) (some (max tw ((skD (shSign op) l ra).width σ dw))) l =
            (skD (shSign op) l ra).low σ dw (max tw ((skD (shSign op) l ra).width σ dw)) :=
          hLexp _ (Nat.le_max_right _ _) hw.1
        -- at no context: the operand's own width (no wider than `tw`)
        have hNone : (skD (shSign op) l ra).width σ dw ≤ tw →
            instDivOperand2 E elems (shSign op) (some ((skD (shSign op) l ra).width σ dw)) l =
              (skD (shSign op) l ra).low σ dw ((skD (shSign op) l ra).width σ dw) := fun hle =>
          hLexp _ (Nat.le_refl _) (Sk.WidthOkC.mono _ _ _ hw.1 (by simp) (by omega))
        rcases hd with ⟨sg, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [shSign] at hlsw hAt hNone ⊢
          refine ⟨by simp [selfWidth2, Sk.width, hlsw],
            by simp [rigidMax2, selfWidth2, Sk.rmax, hlsw], fun _ hle => ?_, ?_, ?_⟩
          · simp only [Sk.width] at hle
            rw [ie_shl_none sg _ l r hlsw, hNone hle, hRexp]
            simp [Sk.low, Sk.width]
          · rw [ie_shl_some sg tw _ l r hlsw, hAt, hRexp]
            simp [Sk.low, ctxTrunc2]
          · rw [fitExpr2_binary, ie_shl_some sg tw _ l r hlsw, hAt, hRexp]
            simp [Sk.low, ctxTrunc2]
        · simp only [shSign] at hlsw hAt hNone ⊢
          refine ⟨by simp [selfWidth2, Sk.width, hlsw],
            by simp [rigidMax2, selfWidth2, Sk.rmax, hlsw], fun _ hle => ?_, ?_, ?_⟩
          · simp only [Sk.width] at hle
            rw [ie_shr_none _ l r hlsw, hNone hle, hRexp]
            simp [Sk.low, Sk.width]
          · rw [ie_shr_some tw _ l r hlsw, hAt, hRexp]
            simp [Sk.low, ctxTrunc2]
          · rw [fitExpr2_binary, ie_shr_some tw _ l r hlsw, hAt, hRexp]
            simp [Sk.low, ctxTrunc2]
        · -- the arithmetic shift right of a signed left operand (IEEE 1800-2023 §11.4.10)
          simp only [shSign] at hlsw hAt hNone ⊢
          refine ⟨by simp [selfWidth2, Sk.width, hlsw],
            by simp [rigidMax2, selfWidth2, Sk.rmax, hlsw], fun _ hle => ?_, ?_, ?_⟩
          · simp only [Sk.width] at hle
            rw [ie_ashr_none _ l r hlsw, hNone hle, hRexp]
            simp [Sk.low, Sk.width]
          · rw [ie_ashr_some tw _ l r hlsw, hAt, hRexp]
            simp [Sk.low, ctxTrunc2]
          · rw [fitExpr2_binary, ie_ashr_some tw _ l r hlsw, hAt, hRexp]
            simp [Sk.low, ctxTrunc2]
      · -- a signed comparison (IEEE 1800-2023 §11.4.4, §11.8.1): two signed signals, or a signed signal and a
        -- constant, at the wider of their widths
        have hsk : skT (.binary op l r) rs =
            .scmp cm (skT l (rs.take (cnt l))) (skT r (rs.drop (cnt l))) := by
          cases op <;> simp [scmpOp?] at hcm <;> subst hcm <;> simp [skT, gateOf]
        obtain ⟨hL, hR⟩ := scmpRd?_opds hs
        obtain ⟨sl, fl⟩ := scmpOpd_shape C hdw (fun a ha => hacc a (List.mem_of_mem_take ha)) hL
        obtain ⟨sr, fr⟩ := scmpOpd_shape C hdw (fun a ha => hacc a (List.mem_of_mem_drop ha)) hR
        rw [hsk] at hw ⊢
        obtain ⟨rfl, hwl, hwr⟩ := hw
        have key : ∀ ctx, instExpr2 E elems ctx (.binary op l r) =
            (Sk.scmp cm (skT l (rs.take (cnt l))) (skT r (rs.drop (cnt l)))).low σ dw 1 := by
          intro ctx
          rw [ie_scmp hcm ctx l r sl sr, fl _ hwl, fr _ hwr]
          simp [Sk.low]
        exact ⟨by simp [Sk.width, sw_scmp hcm], by simp [Sk.rmax, rm_scmp hcm],
          fun _ _ => by simpa [Sk.width] using key none, key _, by rw [fitExpr2_binary]; exact key _⟩
      | true =>
      rw [unsign_binary_t hu] at h hf hcn hw ⊢
      rcases rdsOfW?_binary h with ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨hb, ra, rb, hl, hr, rfl⟩ |
        ⟨hb, ra, rb, hl, hr, rfl⟩ | ⟨cm, hsc, -⟩
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
      · rw [(scmpOp_ctx hsc).2.2.2] at hu; cases hu
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
  | .bitSel b i, rs, h, _, hacc, hcn, tw, hw => by
      obtain ⟨b', hb⟩ := unsign_bitSel b i
      have h' : rdsLeaf? ds (PExpr.bitSel b i).unsign = .ok rs := by
        rw [hb] at h ⊢; simpa [rdsOfW?] using h
      exact leaf_caseCU C hdw h' hacc tw hw
  | .partSel b pm pl, rs, h, _, hacc, hcn, tw, hw => by
      obtain ⟨b', hb⟩ := unsign_partSel b pm pl
      have h' : rdsLeaf? ds (PExpr.partSel b pm pl).unsign = .ok rs := by
        rw [hb] at h ⊢; simpa [rdsOfW?] using h
      exact leaf_caseCU C hdw h' hacc tw hw
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
        | bitSel b i => obtain ⟨b', hb⟩ := unsign_bitSel b i; rw [hb] at h; cases h
        | partSel b m l => obtain ⟨b', hb⟩ := unsign_partSel b m l; rw [hb] at h; cases h
        | _ => simp [PExpr.unsign] at h
      exact hcat ⟨qs, hq⟩
    have h2 : rhsRds? ds v.unsign = rdsOfW? ds v.unsign := by
      generalize v.unsign = x at hn1
      cases x <;> first | rfl | exact absurd rfl (hn1 _)
    rw [h2] at h
    rw [fragOk_of_ne hn1 hn2] at hf
    rw [skRhs_of_ne hn1 hn2] at hw ⊢
    exact gate_shapeCU C hdw v rs h hf hacc hcn tw hw

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
        fitExpr2 E elems (some tw) v = (skT v rs).low σ dw tw := by
  intro v rs h hf hacc hcn tw hw
  have hu := unsign_of_rdsOfW h
  have := skT_shapeCU C hdw v rs (by rw [hu]; exact h) (by rw [hu]; exact hf) hacc (by rw [hu]; exact hcn) tw
    (by rw [hu]; exact hw)
  rwa [hu] at this

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
  have hu := unsign_of_rhsRds h
  have := rhs_shapeCU (v := v) C hdw (by rw [hu]; exact h) (by rw [hu]; exact hf) hacc (by rw [hu]; exact hcn)
    (by rw [hu]; exact hw)
  rwa [hu] at this

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
  have hagx : ∀ x ∈ a.affs, ∀ n ∈ x.names, E.intVal? n = some (σ n) :=
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

/-- The shift itself, over an operand already extended to `lc` (bit function `lb`) and an amount of width `wr`: `<<`,
the arithmetic `>>>` of a signed operand (`sg`), or the logical `>>`. -/
theorem xf_shCore (d sg : Bool) {Lx R0 : Expr2} {wr lc : Nat} {lb rbits : Nat → Bool}
    (env : String → Nat → Bool) (hLw : Lx.xfWidth m = some lc)
    (hLb : ∀ k, k < lc → Lx.xfBits m env k = lb k)
    (hRw : R0.xfWidth m = some wr) (hRb : ∀ k, k < wr → R0.xfBits m env k = rbits k) :
    (Expr2.binary (if d then BinOp.shl sg else if sg then BinOp.ashr true else BinOp.shr false) Lx R0).xfWidth m =
        some lc ∧
      ∀ k, k < lc →
        (Expr2.binary (if d then BinOp.shl sg else if sg then BinOp.ashr true else BinOp.shr false) Lx R0).xfBits m
            env k =
          (if d then XF.shlBits lb wr rbits k
           else if sg then XF.ashrBits lc lb wr rbits k else XF.shrBits lc lb wr rbits k) := by
  have hv : XF.val (R0.xfBits m env) wr = XF.val rbits wr := XF.val_congr_lt hRb
  cases d
  · cases sg
    · refine ⟨by simp [Expr2.xfWidth, hLw, hRw, XF.comb], fun k hk => ?_⟩
      simp only [Bool.false_eq_true, if_false, Expr2.xfBits, hLw, hRw, Option.getD_some, XF.shrBits, hv]
      by_cases h1 : k + XF.val rbits wr < lc
      · rw [hLb _ h1]
      · simp [h1]
    · refine ⟨by simp [Expr2.xfWidth, hLw, hRw, XF.comb], fun k hk => ?_⟩
      simp only [Bool.false_eq_true, if_false, reduceIte, Expr2.xfBits, hLw, hRw, Option.getD_some, XF.ashrBits, hv]
      by_cases h1 : k + XF.val rbits wr < lc
      · simp [h1, hLb _ h1]
      · by_cases h0 : 0 < lc
        · simp [h1, h0, hLb (lc - 1) (by omega)]
        · simp [h1, h0]
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
  | .scmp _ _ _, _, _, hw, _, _ => by simp [Sk.WidthOk] at hw

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

/-- The `>>` arm of `Sk.bitC` for a left operand that is not a fitted zero-extended leaf: the operand at the operation
width. -/
theorem Sk.bitC_shr_gen {σ : String → Int} {dw : String → Nat} {tw : Nat} {rd : String → Nat → Bool}
    (l r : Sk) (hl : ∀ p, l ≠ .fit false p) (k : Nat) :
    Sk.bitC σ dw tw rd (.sh false false l r) k =
      XF.shrBits (max tw (l.width σ dw)) (l.bitC σ dw (max tw (l.width σ dw)) rd) (r.width σ dw)
        (r.bitC σ dw (r.width σ dw) rd) k := by
  cases l with
  | fit sg p => cases sg <;> first | exact absurd rfl (hl p) | rfl
  | _ => rfl

/-- The `<<` arm of `Sk.bitC` for a left operand that is not a fitted leaf of the shift's own signedness. -/
theorem Sk.bitC_shl_gen {σ : String → Int} {dw : String → Nat} {tw : Nat} {rd : String → Nat → Bool}
    (sg : Bool) (l r : Sk) (hl : ∀ p, l ≠ .fit sg p) (k : Nat) :
    Sk.bitC σ dw tw rd (.sh true sg l r) k =
      XF.shlBits (l.bitC σ dw (max tw (l.width σ dw)) rd) (r.width σ dw) (r.bitC σ dw (r.width σ dw) rd) k := by
  cases sg <;> cases l with
  | fit sg' p => cases sg' <;> first | exact absurd rfl (hl p) | rfl
  | _ => rfl

/-- The `>>>` arm of `Sk.bitC` for a left operand that is not a fitted sign-extended leaf. -/
theorem Sk.bitC_ashr_gen {σ : String → Int} {dw : String → Nat} {tw : Nat} {rd : String → Nat → Bool}
    (l r : Sk) (hl : ∀ p, l ≠ .fit true p) (k : Nat) :
    Sk.bitC σ dw tw rd (.sh false true l r) k =
      XF.ashrBits (max tw (l.width σ dw)) (l.bitC σ dw (max tw (l.width σ dw)) rd) (r.width σ dw)
        (r.bitC σ dw (r.width σ dw) rd) k := by
  cases l with
  | fit sg p => cases sg <;> first | exact absurd rfl (hl p) | rfl
  | _ => rfl

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
  | .scmp op l r, tw, hk, hw, hL, env => by
      simp only [Sk.knownB, Bool.and_eq_true] at hk
      obtain ⟨⟨hord, hkl⟩, hkr⟩ := hk
      obtain ⟨rfl, hwl, hwr⟩ := hw
      obtain ⟨h1, b1⟩ := low_xf_genC l _ hkl hwl (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      obtain ⟨h2, b2⟩ := low_xf_genC r _ hkr hwr (fun x hx => hL x (by simp [Sk.leaves, hx])) env
      cases op <;> simp [CmpOp.ord] at hord <;>
        exact ⟨by simp [Sk.low, CmpOp.ex, Expr2.xfWidth, h1, h2, XF.comb], fun k _ => by
          simp only [Sk.low, Sk.bitC, scmpBit, CmpOp.ex, Expr2.xfBits]
          rw [h1, h2]
          simp only [Option.getD_some, XF.bv_congr_lt b1, XF.bv_congr_lt b2]
          simp [BitVec.slt, BitVec.sle]⟩
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
      have hlc : l.width σ dw ≤ max tw (l.width σ dw) := Nat.le_max_right _ _
      obtain ⟨hlw, hlb⟩ := low_xf_genC l (max tw (l.width σ dw)) hk.1 hw.1
        (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      obtain ⟨hrw, hrb⟩ := low_xf_genC r (r.width σ dw) hk.2 hw.2 (fun a ha => hL a (by simp [Sk.leaves, ha])) env
      obtain ⟨hEw, hEb⟩ := xf_shCore d sg env hlw hlb hrw hrb
      have h := xf_shFin (tw := tw) env (Nat.le_max_left _ _) hEw hEb
      simp only [Sk.low]
      refine ⟨h.1, fun k hk' => ?_⟩
      rw [h.2 k hk']
      cases d <;> cases sg
      · -- `>>`: a fitted (zero-extended) leaf reads no bit above its own width
        by_cases hfit : ∃ p, l = .fit false p
        · obtain ⟨p, rfl⟩ := hfit
          have hz : (Sk.fit false p).bitC σ dw (max tw ((Sk.fit false p).width σ dw)) env =
              XF.zext (p.width σ dw) (p.bitC σ dw (p.width σ dw) env) := funext fun j => rfl
          simp only [Bool.false_eq_true, if_false, hz]
          simp only [Sk.width] at hlc ⊢
          rw [shrBits_zext hlc]
          rfl
        · simp only [Bool.false_eq_true, if_false]
          rw [Sk.bitC_shr_gen l r (fun p hp => hfit ⟨p, hp⟩)]
      · -- `>>>`
        by_cases hfit : ∃ p, l = .fit true p
        · obtain ⟨p, rfl⟩ := hfit
          have hz : (Sk.fit true p).bitC σ dw (max tw ((Sk.fit true p).width σ dw)) env =
              XF.sext (p.width σ dw) (p.bitC σ dw (p.width σ dw) env) := funext fun j => rfl
          simp only [Bool.false_eq_true, if_false, if_true, hz]
          rfl
        · simp only [Bool.false_eq_true, if_false, if_true]
          rw [Sk.bitC_ashr_gen l r (fun p hp => hfit ⟨p, hp⟩)]
      · -- `<<` of an unsigned operand
        by_cases hfit : ∃ p, l = .fit false p
        · obtain ⟨p, rfl⟩ := hfit
          have hz : (Sk.fit false p).bitC σ dw (max tw ((Sk.fit false p).width σ dw)) env =
              XF.zext (p.width σ dw) (p.bitC σ dw (p.width σ dw) env) := funext fun j => rfl
          simp only [if_true, hz]
          rfl
        · simp only [if_true]
          rw [Sk.bitC_shl_gen false l r (fun p hp => hfit ⟨p, hp⟩)]
      · -- `<<` of a signed operand
        by_cases hfit : ∃ p, l = .fit true p
        · obtain ⟨p, rfl⟩ := hfit
          have hz : (Sk.fit true p).bitC σ dw (max tw ((Sk.fit true p).width σ dw)) env =
              XF.sext (p.width σ dw) (p.bitC σ dw (p.width σ dw) env) := funext fun j => rfl
          simp only [if_true, hz]
          rfl
        · simp only [if_true]
          rw [Sk.bitC_shl_gen true l r (fun p hp => hfit ⟨p, hp⟩)]
  | .fit sg p, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, b1⟩ := low_xf_genC p (p.width σ dw) hk hw (fun a ha => hL a (by simpa [Sk.leaves] using ha)) env
      simp only [Sk.low, fitDivOperand2]
      by_cases he : (tw == p.width σ dw) = true
      · have htw : tw = p.width σ dw := by simpa using he
        rw [if_pos he]
        subst htw
        refine ⟨h1, fun k hk' => ?_⟩
        cases sg <;> simp [Sk.bitC, XF.zext, XF.sext, hk', b1 k hk']
      · rw [if_neg he]
        cases sg
        · simp only [Bool.false_eq_true, if_false]
          refine ⟨by simp [Expr2.xfWidth, h1], fun k _ => ?_⟩
          by_cases hkp : k < p.width σ dw
          · simp [Expr2.xfBits, h1, Sk.bitC, XF.zext, hkp, b1 k hkp]
          · simp [Expr2.xfBits, h1, Sk.bitC, XF.zext, hkp]
        · simp only [if_true]
          refine ⟨by simp [Expr2.xfWidth, h1], fun k _ => ?_⟩
          simp only [Expr2.xfBits, h1, Option.getD_some, Sk.bitC]
          exact sext_congr b1 k
  | .sx p, tw, hk, hw, hL, env => by
      simp only [Sk.knownB] at hk
      simp only [Sk.WidthOkC] at hw
      obtain ⟨h1, b1⟩ := low_xf_genC p (p.width σ dw) hk hw (fun a ha => hL a (by simpa [Sk.leaves] using ha)) env
      refine ⟨by simp [Sk.low, Expr2.xfWidth, h1], fun k _ => ?_⟩
      simp only [Sk.low, Expr2.xfBits, h1, Option.getD_some, Sk.bitC]
      exact sext_congr b1 k
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
