import LeanModels.Sv.CombView

/-!
# `sv_structure`, stage 2: soundness of the summary and the structural theorems

`CombView.lean` defines the summary. Here:

* the per-site soundness theorem (`site_desc`): the process `instProcess2` builds for a template
  site is an `assign` to EXACTLY the promised target whose reads are CONTAINED in the promised
  ones (and equal when every array read is in range), with no loud node and only declared
  identifiers;
* the assembly against `instantiate2` (`Summary.sound`): the whole design is the closed-form
  list `Summary.pairs` (never an enumeration of `N` cells);
* the obligations the summary leaves to the player, as compact `Prop`s over the loop indices
  (`InRangeObl`, `DisjObl`, `RankObl`; `AutoObl` is for the tactic's `omega`);
* `CombDesign` and `Acyclic` of the instantiated design from the obligations
  (`comb_of_summary`, `acyclic_of_summary`), for `d.instantiateGD2 args` (= `name.sem`).
-/

namespace LeanModels.Sv
namespace CombView

/-! ## Derived definitions on the summary -/

def TSite.arrNames (st : TSite) : List String :=
  (match st.tgt with | .arr n _ => [n] | _ => []) ++
    st.rds.filterMap fun r => match r with | .arr n _ => some n | _ => none

def Summary.arrOk (s : Summary) (n : String) : Bool :=
  match s.find n with
  | some ⟨_, _, _, some (_, _, l)⟩ => decide (l = Aff.const 0)
  | _ => false

/-- The loop index ranges over `[c0, bound)`. -/
def TFam.Rng (f : TFam) (σ : String → Int) (i : Int) : Prop := f.c0 ≤ i ∧ i < f.bound.eval σ

theorem TFam.mem_range {f : TFam} {σ : String → Int} {i : Int} :
    i ∈ f.range σ ↔ f.Rng σ i := by
  simp only [TFam.range, TFam.Rng, mem_intRange]
  omega

/-- Structural well-formedness of a summary: decidable closed data, discharged by `decide`. -/
def Summary.StructOk (s : Summary) : Prop :=
  s.declNames.Nodup ∧
  (∀ st ∈ s.sites, ∀ n ∈ st.names, n ∈ s.declNames) ∧
  (∀ st ∈ s.sites, st.tgt.name ∉ s.inputNames) ∧
  (∀ st ∈ s.statics, ∀ n ∈ st.affNames, n ∈ s.params) ∧
  (∀ f ∈ s.fam.toList, (∀ st ∈ f.body, ∀ n ∈ st.affNames, n ∈ f.g :: s.params) ∧
      (∀ n ∈ f.bound.names, n ∈ s.params ∧ n ≠ f.g) ∧ 0 ≤ f.c0) ∧
  (∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, n ∈ s.params) ∧
  (∀ st ∈ s.sites, ∀ n ∈ st.arrNames, s.arrOk n = true)

instance (s : Summary) : Decidable s.StructOk := by
  unfold Summary.StructOk; infer_instance

/-- Numeric facts about a read (a bit read's index is non-negative; an array read's declared
dimension is non-negative) — discharged by the tactic's `omega`. -/
def Summary.RdNum (s : Summary) (σd σs : String → Int) : TRd → Prop
  | .whole _ => True
  | .bit _ a => 0 ≤ a.eval σs
  | .arr n _ => 0 ≤ (s.AD σd n).getD 0

def Summary.AutoObl (s : Summary) (σ : String → Int) (args : List Int) : Prop :=
  (∀ st ∈ s.statics, ∀ r ∈ st.rds, s.RdNum σ σ r) ∧
  (∀ f ∈ s.fam.toList,
    (∀ i, f.Rng σ i → ∀ st ∈ f.body, ∀ r ∈ st.rds, s.RdNum σ (bindσ f.g i σ) r) ∧
    (f.bound.eval σ - f.c0).toNat ≤ (args.map Int.natAbs).sum + 60)

/-- A site's write window lies inside its declared signal (`inWidth`). -/
def Summary.InWin (s : Summary) (σd σs : String → Int) (st : TSite) : Prop :=
  match st.tgt with
  | .whole _ => True
  | .bit n a => 0 ≤ a.eval σs ∧ a.eval σs + 1 ≤ (s.dw σd n : Int)
  | .arr n a => 0 ≤ a.eval σs ∧ a.eval σs ≤ (s.AD σd n).getD 0

def Summary.InRangeObl (s : Summary) (σ : String → Int) : Prop :=
  (∀ st ∈ s.statics, s.InWin σ σ st) ∧
  (∀ f ∈ s.fam.toList, ∀ i, f.Rng σ i → ∀ st ∈ f.body, s.InWin σ (bindσ f.g i σ) st)

/-- **One driver per bit.** -/
def Summary.DisjObl (s : Summary) (σ : String → Int) : Prop :=
  (s.statics.Pairwise fun a b =>
      Win.overlaps (a.tgt.win σ (s.dw σ)) (b.tgt.win σ (s.dw σ)) = false) ∧
  (∀ f ∈ s.fam.toList,
    (∀ a ∈ s.statics, ∀ i, f.Rng σ i → ∀ b ∈ f.body,
      Win.overlaps (a.tgt.win σ (s.dw σ)) (b.tgt.win (bindσ f.g i σ) (s.dw σ)) = false) ∧
    (∀ i, f.Rng σ i → f.body.Pairwise fun a b =>
      Win.overlaps (a.tgt.win (bindσ f.g i σ) (s.dw σ)) (b.tgt.win (bindσ f.g i σ) (s.dw σ)) = false) ∧
    (∀ i, f.Rng σ i → ∀ k, f.Rng σ k → i < k → ∀ a ∈ f.body, ∀ b ∈ f.body,
      Win.overlaps (a.tgt.win (bindσ f.g i σ) (s.dw σ)) (b.tgt.win (bindσ f.g k σ) (s.dw σ)) = false))

/-- **The rank decreases along every read** (design principle 13: sites by identity). -/
def Summary.RankObl (s : Summary) (ρ : SiteId → Nat) (σ : String → Int) : Prop :=
  (∀ a ∈ s.statics, ∀ b ∈ s.statics, ∀ r ∈ a.rds,
      ReadWin.overlaps (r.rd σ) (b.tgt.win σ (s.dw σ)) = true →
        ρ (.plain b.pos) < ρ (.plain a.pos)) ∧
  (∀ f ∈ s.fam.toList,
    (∀ a ∈ s.statics, ∀ k, f.Rng σ k → ∀ b ∈ f.body, ∀ r ∈ a.rds,
        ReadWin.overlaps (r.rd σ) (b.tgt.win (bindσ f.g k σ) (s.dw σ)) = true →
          ρ (.fam f.label b.pos [k]) < ρ (.plain a.pos)) ∧
    (∀ i, f.Rng σ i → ∀ a ∈ f.body, ∀ b ∈ s.statics, ∀ r ∈ a.rds,
        ReadWin.overlaps (r.rd (bindσ f.g i σ)) (b.tgt.win σ (s.dw σ)) = true →
          ρ (.plain b.pos) < ρ (.fam f.label a.pos [i])) ∧
    (∀ i, f.Rng σ i → ∀ k, f.Rng σ k → ∀ a ∈ f.body, ∀ b ∈ f.body, ∀ r ∈ a.rds,
        ReadWin.overlaps (r.rd (bindσ f.g i σ)) (b.tgt.win (bindσ f.g k σ) (s.dw σ)) = true →
          ρ (.fam f.label b.pos [k]) < ρ (.fam f.label a.pos [i])))

/-! ## Expression-level facts -/

/-- What the summary promises about an instantiated expression. -/
def RdOK (σ : String → Int) (rs : List TRd) (x : Expr2) : Prop :=
  x.unsupportedFree = true ∧ (∀ r ∈ x.reads, r ∈ rs.map (TRd.rd σ)) ∧
    ∀ i ∈ x.idents, i ∈ rs.map TRd.name

theorem RdOK.binary {σ : String → Int} {ra rb : List TRd} {x y : Expr2} (op : BinOp)
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

theorem RdOK.resize {σ : String → Int} {rs : List TRd} {x : Expr2} (w : Nat)
    (h : RdOK σ rs x) : RdOK σ rs (.resize w x) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa [Expr2.unsupportedFree] using h1,
    fun r hr => h2 r (by simpa [Expr2.reads] using hr),
    fun i hi => h3 i (by simpa [Expr2.idents] using hi)⟩

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

theorem RdOK.fit {σ : String → Int} {rs : List TRd} {E : IEnv} {elems : List (String × Nat)}
    {e : PExpr} (hs : e.signedCast = false)
    (h : ∀ c, RdOK σ rs (instExpr2 E elems c e)) (ctx : Option Nat) :
    RdOK σ rs (fitExpr2 E elems ctx e) := by
  rcases fitExpr2_cases E elems ctx e hs with ⟨c, hc⟩ | ⟨w, c, hc⟩
  · rw [hc]; exact h c
  · rw [hc]; exact RdOK.resize w (h c)

theorem signedCast_of_rds {e : PExpr} {rs : List TRd} (h : rdsOf? e = .ok rs) :
    e.signedCast = false := by
  cases e <;> first | rfl | (simp [rdsOf?] at h)

/-- Numeric side conditions of one read. -/
def ReadOK (σs : String → Int) (AD : String → Option Int) : TRd → Prop
  | .whole _ => True
  | .bit _ a => 0 ≤ a.eval σs
  | .arr n _ => ∃ m, AD n = some m ∧ 0 ≤ m

/-- The instantiation environment's facts the site lemmas read. -/
structure Ctx (σ : String → Int) (E : IEnv) (elems : List (String × Nat))
    (DW : String → Option Nat) (AD : String → Option Int) (ns : List String) : Prop where
  agree : Agrees σ E ns
  widths : ∀ n, E.widths.lookup n = DW n
  elems : ∀ n, (DW n).isSome = true → elems.lookup n = some 1
  dims : ∀ n m, AD n = some m → E.dims.lookup n = some [(m, 0)]

theorem Ctx.bindVal {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
    {DW : String → Option Nat} {AD : String → Option Int} {ns : List String}
    (C : Ctx σ E elems DW AD ns) (g : String) (i : Int) :
    Ctx (bindσ g i σ) (E.bindVal g i) elems DW AD (g :: ns) :=
  ⟨C.agree.bindVal g i, C.widths, C.elems, C.dims⟩

/-- A 1-D zero-based descending array select, in range. -/
theorem arrayElemWindow_1d_in {E : IEnv} {n : String} {i : PExpr} {m k : Int}
    (hd : E.dims.lookup n = some [(m, 0)]) (hev : evalInt E i = .ok k) (hk0 : 0 ≤ k)
    (hkm : k ≤ m) : arrayElemWindow E n [i] = .ok (k, 1, true) := by
  have hm : 0 ≤ m := by omega
  rw [arrayElemWindow_of (arrayDims_of hd)
    (walkIndices_desc0_cons hm hev hk0 hkm (walkIndices_nil (env := E) []))]
  simp

/-- … and out of range (the read is all-x). -/
theorem arrayElemWindow_1d_out {E : IEnv} {n : String} {i : PExpr} {m k : Int}
    (hd : E.dims.lookup n = some [(m, 0)]) (hm : 0 ≤ m) (hev : evalInt E i = .ok k)
    (hout : ¬ (0 ≤ k ∧ k ≤ m)) : ∃ lo w, arrayElemWindow E n [i] = .ok (lo, w, false) := by
  have hc := dimCount_desc0 hm
  have hw := arrayElemWindow_of (arrayDims_of hd)
    (walkIndices_cons_of hev (walkIndices_nil (env := E) []))
  have hb : (true && decide (0 ≤ labelOffset m 0 k) &&
      decide (labelOffset m 0 k < (dimCount m 0 : Int))) = false := by
    rw [labelOffset_desc0 hm, hc]
    by_cases h1 : 0 ≤ k
    · have h2 : ¬ k < m + 1 := by intro h; exact hout ⟨h1, by omega⟩
      simp [h1, h2]
    · simp [h1]
  rw [hb] at hw
  exact ⟨_, _, hw⟩

/-- A gate node instantiates to the gate over two `fitExpr2`s at one context. -/
theorem instExpr2_gate (E : IEnv) (elems : List (String × Nat)) (ctx : Option Nat) (bop : BinOp)
    (hb : bop = .and ∨ bop = .or ∨ bop = .xor) (l r : PExpr) :
    ∃ c, instExpr2 E elems ctx (.binary (.m0 bop) l r) =
      .binary bop (fitExpr2 E elems c l) (fitExpr2 E elems c r) := by
  rcases hb with rfl | rfl | rfl <;> cases ctx <;> simp [instExpr2] <;>
    first | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl⟩

theorem inst_rd {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
    {DW : String → Option Nat} {AD : String → Option Int} {ns : List String}
    (C : Ctx σ E elems DW AD ns) :
    ∀ (e : PExpr) (rs : List TRd), rdsOf? e = .ok rs →
      (∀ r ∈ rs, (DW r.name).isSome = true) → (∀ r ∈ rs, ReadOK σ AD r) →
      (∀ r ∈ rs, ∀ a ∈ r.affs, ∀ n ∈ a.names, n ∈ ns) →
      ∀ ctx, RdOK σ rs (instExpr2 E elems ctx e)
  | .ident n, rs, h, _, _, _, ctx => by
      simp only [rdsOf?, Except.ok.injEq] at h
      subst h
      simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents, TRd.rd, TRd.name]
  | .lit v, rs, h, _, _, _, ctx => by
      simp only [rdsOf?, Except.ok.injEq] at h
      subst h
      simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
  | .bitSel b i, rs, h, hd, hr, hn, ctx => by
      cases b with
      | ident n =>
        simp only [rdsOf?] at h
        rcases ha : affOf? i with _ | a
        · simp [ha] at h
        · simp only [ha, Except.ok.injEq] at h
          subst h
          have hdn : (DW n).isSome = true := hd (.bit n a) (by simp)
          have hel : elems.lookup n = some 1 := C.elems n hdn
          have hag : ∀ x ∈ a.names, E.vals.lookup x = some (σ x) :=
            fun x hx => C.agree x (hn (.bit n a) (by simp) a (by simp [TRd.affs]) x hx)
          obtain ⟨-, hev⟩ := affOf?_sound i a ha hag
          have hnn : 0 ≤ a.eval σ := hr (.bit n a) (by simp)
          rw [instExpr2_bitSel_ident ctx hel hev hnn]
          simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents, TRd.rd,
            TRd.name]
      | _ => simp [rdsOf?] at h
  | .arrayElem n is, rs, h, hd, hr, hn, ctx => by
      cases is with
      | nil => simp [rdsOf?] at h
      | cons i rest =>
        cases rest with
        | nil =>
          simp only [rdsOf?] at h
          rcases ha : affOf? i with _ | a
          · simp [ha] at h
          · simp only [ha, Except.ok.injEq] at h
            subst h
            obtain ⟨m, hAD, hm0⟩ := hr (.arr n a) (by simp)
            have hdm := C.dims n m hAD
            have hag : ∀ x ∈ a.names, E.vals.lookup x = some (σ x) :=
              fun x hx => C.agree x (hn (.arr n a) (by simp) a (by simp [TRd.affs]) x hx)
            obtain ⟨-, hev⟩ := affOf?_sound i a ha hag
            rw [instExpr2_arrayElem]
            by_cases hin : 0 ≤ a.eval σ ∧ a.eval σ ≤ m
            · rw [arrayElemRead_of_inRange (arrayElemWindow_1d_in hdm hev hin.1 hin.2)]
              simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.sliceReads, Expr2.idents,
                TRd.rd, TRd.name]
            · obtain ⟨lo, w, hlo⟩ := arrayElemWindow_1d_out hdm hm0 hev hin
              rw [arrayElemRead_of_oob hlo]
              simp [RdOK, Expr2.unsupportedFree, Expr2.reads, Expr2.idents]
        | cons j rest' => simp [rdsOf?] at h
  | .binary op l r, rs, h, hd, hr, hn, ctx => by
      simp only [rdsOf?] at h
      rcases hg : gateOf op with _ | b
      · simp [hg] at h
      · rcases hl : rdsOf? l with e1 | ra
        · simp [hg, hl] at h
        · rcases hr' : rdsOf? r with e2 | rb
          · simp [hg, hl, hr'] at h
          · simp only [hg, hl, hr', Except.ok.injEq] at h
            subst h
            obtain ⟨rfl, hb⟩ := gateOf_cases hg
            have ihl := inst_rd C l ra hl (fun x hx => hd x (by simp [hx]))
              (fun x hx => hr x (by simp [hx])) (fun x hx => hn x (by simp [hx]))
            have ihr := inst_rd C r rb hr' (fun x hx => hd x (by simp [hx]))
              (fun x hx => hr x (by simp [hx])) (fun x hx => hn x (by simp [hx]))
            have hfl := RdOK.fit (E := E) (elems := elems) (signedCast_of_rds hl) ihl
            have hfr := RdOK.fit (E := E) (elems := elems) (signedCast_of_rds hr') ihr
            obtain ⟨c, hc⟩ := instExpr2_gate E elems ctx b hb l r
            rw [hc]
            exact RdOK.binary _ (hfl c) (hfr c)
  | .unary .., rs, h, _, _, _, _ | .ternary .., rs, h, _, _, _, _
  | .concat _, rs, h, _, _, _, _ | .partSel .., rs, h, _, _, _, _
  | .arrayPart .., rs, h, _, _, _, _ | .repl .., rs, h, _, _, _, _
  | .reduce .., rs, h, _, _, _, _ | .paramRef .., rs, h, _, _, _, _
  | .genvarRef .., rs, h, _, _, _, _ | .enumRef .., rs, h, _, _, _, _
  | .int .., rs, h, _, _, _, _ | .fill .., rs, h, _, _, _, _
  | .resize .., rs, h, _, _, _, _ | .signedResize .., rs, h, _, _, _, _
  | .squash2 .., rs, h, _, _, _, _ | .sysCall .., rs, h, _, _, _, _
  | .cast .., rs, h, _, _, _, _ | .unsupported .., rs, h, _, _, _, _ => by
      simp [rdsOf?] at h

/-- The right-hand side of a site, at any context width. -/
theorem rhs_ok {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
    {DW : String → Option Nat} {AD : String → Option Int} {ns : List String}
    (C : Ctx σ E elems DW AD ns) {v : PExpr} {rds : List TRd} (h : rdsOf? v = .ok rds)
    (hd : ∀ r ∈ rds, (DW r.name).isSome = true) (hr : ∀ r ∈ rds, ReadOK σ AD r)
    (hn : ∀ r ∈ rds, ∀ a ∈ r.affs, ∀ n ∈ a.names, n ∈ ns) (ctx : Option Nat) :
    RdOK σ rds (fitExpr2 E elems ctx v) :=
  RdOK.fit (signedCast_of_rds h) (inst_rd C v rds h hd hr hn) ctx

/-! ## One site -/

/-- The instantiated process `p` is an `assign` to the footprint's target, reading only the
footprint's reads. -/
def Desc (names : List String) (si : SiteInst) (p : Process2) : Prop :=
  ∃ e, p = .assign si.tgt e ∧ (∀ r ∈ e.reads, r ∈ si.rd) ∧ e.unsupportedFree = true ∧
    ∀ x ∈ e.idents, x ∈ names

def TgtOK (σs : String → Int) (AD : String → Option Int) : TTgt → Prop
  | .whole _ => True
  | .bit _ a => 0 ≤ a.eval σs
  | .arr n a => ∃ m, AD n = some m ∧ 0 ≤ a.eval σs ∧ a.eval σs ≤ m

structure SiteOK (σ : String → Int) (DW : String → Option Nat) (AD : String → Option Int)
    (ns : List String) (st : TSite) : Prop where
  decl : ∀ n ∈ st.names, (DW n).isSome = true
  affs : ∀ n ∈ st.affNames, n ∈ ns
  rd : ∀ r ∈ st.rds, ReadOK σ AD r
  win : TgtOK σ AD st.tgt

theorem siteOf?_cases {pos : Nat} {p : PProcess} {st : TSite} (h : siteOf? pos p = .ok st) :
    (∃ t v rds, p = .assign t v ∧ rdsOf? v = .ok rds ∧ st = ⟨pos, .whole t, rds, p⟩) ∨
    (∃ l v tg rds, p = .assignL l v ∧ tgtOf? l = .ok tg ∧ rdsOf? v = .ok rds ∧
      st = ⟨pos, tg, rds, p⟩) := by
  cases p with
  | assign t v =>
    left
    simp only [siteOf?] at h
    rcases hr : rdsOf? v with e | rds
    · simp [hr] at h
    · simp only [hr, Except.ok.injEq] at h
      exact ⟨t, v, rds, rfl, hr, h.symm⟩
  | assignL l v =>
    right
    simp only [siteOf?] at h
    rcases ht : tgtOf? l with e | tg
    · simp [ht] at h
    · rcases hr : rdsOf? v with e | rds
      · simp [ht, hr] at h
      · simp only [ht, hr, Except.ok.injEq] at h
        exact ⟨l, v, tg, rds, rfl, ht, hr, h.symm⟩
  | alwaysFF _ _ => simp [siteOf?] at h
  | alwaysPlain _ _ => simp [siteOf?] at h
  | alwaysComb _ => simp [siteOf?] at h
  | alwaysFFR _ _ _ => simp [siteOf?] at h
  | unsupported _ _ => simp [siteOf?] at h

theorem siteOf?_proc {pos : Nat} {p : PProcess} {st : TSite} (h : siteOf? pos p = .ok st) :
    st.proc = p := by
  rcases siteOf?_cases h with ⟨t, v, rds, rfl, -, rfl⟩ | ⟨l, v, tg, rds, rfl, -, -, rfl⟩ <;> rfl

theorem tgtOf?_cases {l : PLhs} {tg : TTgt} (h : tgtOf? l = .ok tg) :
    (∃ n, l = .ident n ∧ tg = .whole n) ∨
    (∃ n i a, l = .bitSel n i ∧ affOf? i = some a ∧ tg = .bit n a) ∨
    (∃ n i a, l = .arrayElem n [i] ∧ affOf? i = some a ∧ tg = .arr n a) := by
  cases l with
  | ident n =>
    left
    simp only [tgtOf?, Except.ok.injEq] at h
    exact ⟨n, rfl, h.symm⟩
  | bitSel n i =>
    right; left
    simp only [tgtOf?] at h
    rcases ha : affOf? i with _ | a
    · simp [ha] at h
    · simp only [ha, Except.ok.injEq] at h
      exact ⟨n, i, a, rfl, ha, h.symm⟩
  | arrayElem n is =>
    right; right
    cases is with
    | nil => simp [tgtOf?] at h
    | cons i rest =>
      cases rest with
      | nil =>
        simp only [tgtOf?] at h
        rcases ha : affOf? i with _ | a
        · simp [ha] at h
        · simp only [ha, Except.ok.injEq] at h
          exact ⟨n, i, a, rfl, ha, h.symm⟩
      | cons j rest' => simp [tgtOf?] at h
  | partSel _ _ _ => simp [tgtOf?] at h
  | arrayPart _ _ _ _ _ => simp [tgtOf?] at h
  | concat _ => simp [tgtOf?] at h

theorem desc_mk {names : List String} {σ : String → Int} {si : SiteInst} {p : Process2}
    {t : Lhs2} {x : Expr2} {rds : List TRd} (hp : p = .assign t x) (ht : si.tgt = t)
    (hrd : RdOK σ rds x) (hsi : si.rd = rds.map (TRd.rd σ))
    (hnm : ∀ r ∈ rds, r.name ∈ names) : Desc names si p := by
  refine ⟨x, by rw [hp, ht], fun r hr => hsi ▸ hrd.2.1 r hr, hrd.1, fun i hi => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (hrd.2.2 i hi)
  exact hnm r hr

theorem instLhs2_arr {E : IEnv} {elems : List (String × Nat)} {n : String} {i : PExpr}
    {k m : Int} (hd : E.dims.lookup n = some [(m, 0)]) (hev : evalInt E i = .ok k)
    (h0 : 0 ≤ k) (hk : k ≤ m) :
    instLhs2 E elems (.arrayElem n [i]) = .ok (.slice n k.toNat 1, 1) :=
  arrayElemTarget_of_inRange (arrayElemWindow_1d_in hd hev h0 hk)

/-- **The per-site soundness theorem.** -/
theorem site_desc {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
    {DW : String → Option Nat} {AD : String → Option Int} {ns : List String}
    (C : Ctx σ E elems DW AD ns) {names : List String}
    (hnm : ∀ n, (DW n).isSome = true → n ∈ names)
    {pos : Nat} {p : PProcess} {st : TSite} (hs : siteOf? pos p = .ok st)
    (hso : SiteOK σ DW AD ns st) (id : SiteId) :
    Desc names (st.inst σ (fun n => (DW n).getD 0) id) (instProcess2 E elems p) := by
  have hrdd : ∀ rds, rds = st.rds → ∀ r ∈ rds, (DW r.name).isSome = true := by
    rintro rds rfl r hr
    exact hso.decl r.name (by simp [TSite.names]; exact Or.inr ⟨r, hr, rfl⟩)
  have hrdn : ∀ rds, rds = st.rds → ∀ r ∈ rds, ∀ a ∈ r.affs, ∀ n ∈ a.names, n ∈ ns := by
    rintro rds rfl r hr a ha n hn
    exact hso.affs n (by
      simp only [TSite.affNames, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨r, hr, a, ha, hn⟩)
  rcases siteOf?_cases hs with ⟨t, v, rds, rfl, hrds, rfl⟩ | ⟨l, v, tg, rds, rfl, htg, hrds, rfl⟩
  · -- `assign t = v`
    have hdt : (DW t).isSome = true := hso.decl t (by simp [TSite.names, TTgt.name])
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hdt
    have hW : E.widths.lookup t = some w := by rw [C.widths t, hw]
    rw [instProcess2_assign v hW]
    exact desc_mk rfl rfl (rhs_ok C hrds (hrdd _ rfl) hso.rd (hrdn _ rfl) _) rfl
      (fun r hr => hnm _ (hrdd _ rfl r hr))
  · rcases tgtOf?_cases htg with ⟨n, rfl, rfl⟩ | ⟨n, i, a, rfl, hia, rfl⟩ | ⟨n, i, a, rfl, hia, rfl⟩
    · have hdt : (DW n).isSome = true := hso.decl n (by simp [TSite.names, TTgt.name])
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hdt
      have hW : E.widths.lookup n = some w := by rw [C.widths n, hw]
      rw [instProcess2_assignL v (instLhs2_ident hW)]
      exact desc_mk rfl rfl (rhs_ok C hrds (hrdd _ rfl) hso.rd (hrdn _ rfl) _) rfl
        (fun r hr => hnm _ (hrdd _ rfl r hr))
    · have hdt : (DW n).isSome = true := hso.decl n (by simp [TSite.names, TTgt.name])
      have hel := C.elems n hdt
      have hag : ∀ x ∈ a.names, E.vals.lookup x = some (σ x) :=
        fun x hx => C.agree x (hso.affs x (by simp [TSite.affNames, TTgt.affs, hx]))
      obtain ⟨-, hev⟩ := affOf?_sound i a hia hag
      have h0 : 0 ≤ a.eval σ := hso.win
      rw [instProcess2_assignL v (instLhs2_bitSel hel hev h0)]
      exact desc_mk rfl (by simp [TSite.inst, TTgt.lhs]) (rhs_ok C hrds (hrdd _ rfl) hso.rd (hrdn _ rfl) _)
        rfl (fun r hr => hnm _ (hrdd _ rfl r hr))
    · obtain ⟨m, hAD, h0, hm⟩ := hso.win
      have hdm := C.dims n m hAD
      have hag : ∀ x ∈ a.names, E.vals.lookup x = some (σ x) :=
        fun x hx => C.agree x (hso.affs x (by simp [TSite.affNames, TTgt.affs, hx]))
      obtain ⟨-, hev⟩ := affOf?_sound i a hia hag
      rw [instProcess2_assignL v (instLhs2_arr hdm hev h0 hm)]
      exact desc_mk rfl (by simp [TSite.inst, TTgt.lhs]) (rhs_ok C hrds (hrdd _ rfl) hso.rd (hrdn _ rfl) _)
        rfl (fun r hr => hnm _ (hrdd _ rfl r hr))

end CombView
end LeanModels.Sv
