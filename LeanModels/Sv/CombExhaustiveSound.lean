import LeanModels.Sv.CombExhaustive

/-!
# The compiled program is sound (`sv_exhaustive`, the soundness)

* `Sk.compile_sound`: a compiled bit evaluates, on packed bits `f` that hold `rd` inside the declared widths,
  to the skeleton's bit `Sk.bitC` of `rd` (the compiler refuses reads past a declared width).
* `runG_sound`: if `R` (the true bits) is a fixpoint of every compiled bit, the program reads only input bits
  and bits written earlier (`topoG`, decided), and the start environment holds `R` on the input bits and `0`
  elsewhere, then every bit the program writes is `R`'s. For ANY list of compiled bits (a cone).
-/

namespace LeanModels.Sv.Exh

open CombView CombEq

/-! ## Gate expressions -/

theorem GE.eval_congr {f f' : Nat → Bool} : ∀ g : GE, (∀ j ∈ g.bits, f j = f' j) → g.eval f = g.eval f'
  | .bit j, h => h j (by simp [GE.bits])
  | .const _, _ => rfl
  | .not a, h => by simp [GE.eval, GE.eval_congr a (by simpa [GE.bits] using h)]
  | .and a b, h | .or a b, h | .xor a b, h => by
      simp only [GE.bits, List.mem_append] at h
      simp [GE.eval, GE.eval_congr a fun j hj => h j (.inl hj), GE.eval_congr b fun j hj => h j (.inr hj)]
  | .ite c a b, h => by
      simp only [GE.bits, List.mem_append] at h
      simp [GE.eval, GE.eval_congr c fun j hj => h j (.inl (.inl hj)),
        GE.eval_congr a fun j hj => h j (.inl (.inr hj)), GE.eval_congr b fun j hj => h j (.inr hj)]
  | .lut base w bits, h => by
      simp only [GE.eval, XF.val_congr (n := w) fun i hi => h (base + i) (by simp [GE.bits]; omega)]

theorem setB_testBit (x p : Nat) (b : Bool) (i : Nat) :
    (setB x p b).testBit i = if i = p then b else x.testBit i := by
  unfold setB
  by_cases hi : i = p
  · subst hi; split <;> cases b <;> cases h : x.testBit i <;> simp_all [Nat.testBit_xor, Nat.testBit_two_pow]
  · split <;> simp [Nat.testBit_xor, Nat.testBit_two_pow, hi, Ne.symm hi]

theorem lutT_testBit {k d N n : Nat} (hn : n < N) :
    ∀ t, (lutT k d N t).testBit n = (XF.lookupNat t d n).testBit k
  | [] => by by_cases h : d.testBit k <;> simp [lutT, XF.lookupNat, h, Nat.testBit_two_pow_sub_one, hn]
  | (p, v) :: rest => by
      rw [lutT, setB_testBit, lutT_testBit hn rest]; by_cases h : n = p <;> simp [XF.lookupNat, h]

/-! ## The compiler is sound -/

section
variable {σ : String → Int} {dw off : String → Nat} {f : Nat → Bool} {rd : String → Nat → Bool}
  (hf : ∀ n i, i < dw n → f (off n + i) = rd n i)
include hf

/-- **A compiled bit is the skeleton's bit** of any reads the packed bits hold inside the declared widths. -/
theorem Sk.compile_sound : ∀ (sk : Sk) (tw k : Nat) (g : GE), sk.compile σ dw off tw k = some g →
    g.eval f = sk.bitC σ dw tw rd k
  | .lit _, _, _, _, h | .fill _, _, _, _, h | .const _, _, _, _, h => by cases h; rfl
  | .rd a, _, k, _, h => by
      by_cases hi : Acc.lo σ a + k < dw a.name
      · simp only [Sk.compile, bitG, hi, if_true, Option.some.injEq] at h; subst h
        simp [GE.eval, Sk.bitC, accBit, hf _ _ hi]
      · simp [Sk.compile, bitG, hi] at h
  | .bnot a, tw, k, g, h => by
      simp only [Sk.compile, Option.map_eq_some_iff] at h
      obtain ⟨ga, ha, rfl⟩ := h
      simp [GE.eval, Sk.bitC, Sk.compile_sound a tw k ga ha]
  | .gate gt l r, tw, k, g, h => by
      simp only [Sk.compile, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨gl, hl, gr, hr, rfl⟩ := h
      cases gt <;> simp [GE.eval, Sk.bitC, Sk.compile_sound l tw k gl hl, Sk.compile_sound r tw k gr hr]
  | .cat _, _, _, _, h | .rep _, _, _, _, h | .ext _, _, _, _, h | .tern _ _ _, _, _, _, h | .cref _, _, _, _, h
  | .rsz _ _, _, _, _, h | .lnot _, _, _, _, h | .red _ _, _, _, _, h | .land _ _, _, _, _, h
  | .lor _ _, _, _, _, h | .cmp _ _ _, _, _, _, h | .add _ _, _, _, _, h | .sub _ _, _, _, _, h
  | .sh _ _ _ _, _, _, _, h | .scmp _ _ _, _, _, _, h => by simp [Sk.compile] at h

theorem tblOf_sound {w tw k : Nat} {sv : Nat → Bool} {dv : LVec} : ∀ {its : List (List LVec × Sk)} {t},
    tblOf w its = some t →
      XF.caseSel w sv (pskArmsBit σ dw tw rd its) dv.boolAt k = (XF.lookupNat t dv.nat (XF.val sv w)).testBit k
  | [], t, h => by cases h; simp [pskArmsBit, XF.lookupNat, XF.testBit_nat_boolAt]
  | e :: its, t, h => by
      simp only [tblOf, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, t', ht', rfl⟩ := h
      unfold armOf at hq
      split at hq <;> (try split at hq) <;> cases hq
      rename_i p v _
      have he : XF.eqv w sv p.boolAt = decide (XF.val sv w = p.nat) := by
        rw [Bool.eq_iff_iff, XF.eqv_eq_true_iff]; simp [LVec.nat, *]
      by_cases hv : XF.val sv w = p.nat <;>
        simp [pskArmsBit, XF.caseSel, XF.lookupNat, Sk.bitC, he, hv, XF.testBit_nat_boolAt, tblOf_sound ht']

/-- **A compiled bit of a procedural skeleton is its bit.** -/
theorem PSk.compile_sound : ∀ (p : PSk) (tw k : Nat) (g : GE), p.compile σ dw off tw k = some g →
    g.eval f = p.bit σ dw tw rd k
  | .leaf sk, tw, k, g, h => Sk.compile_sound hf sk tw k g h
  | .blk a, tw, k, g, h => PSk.compile_sound a tw k g h
  | .ite c a b, tw, k, g, h | .ovr c a b, tw, k, g, h => by
      simp only [PSk.compile, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨gc, hc, ga, ha, gb, hb, rfl⟩ := h
      simp [GE.eval, PSk.bit, Sk.compile_sound hf c 1 0 gc hc, PSk.compile_sound a tw k ga ha,
        PSk.compile_sound b tw k gb hb]
  | .cases s its d, tw, k, g, h => by
      simp only [PSk.compile, casesG] at h
      split at h <;> (try split at h) <;> (try cases h)
      rename_i a dv _
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [PSk.bit, show (Sk.lit dv).bitC σ dw tw rd = dv.boolAt from rfl, Sk.width, tblOf_sound hf ht, GE.eval,
        lutT_testBit (XF.val_lt _ _)]
      congr 2
      exact XF.val_congr fun i hi => by simp only [Sk.bitC, accBit]; rw [Nat.add_assoc, hf _ _ (by omega)]
end

/-! ## The run is sound -/

/-- Packed bit `j` is an input bit or written by a compiled bit of `done`. -/
def readyB (ins : List Nat) (done : List GSite) (j : Nat) : Bool := ins.contains j || done.any (·.out == j)

/-- **The order check** (bit granularity): each compiled bit writes a fresh packed bit and reads only
ready ones. -/
def topoG (ins : List Nat) : List GSite → List GSite → Bool
  | _, [] => true
  | done, g :: gs => !(readyB ins done g.out) && g.e.bits.all (readyB ins done) && topoG ins (done ++ [g]) gs

theorem runG_inv {ins : List Nat} {R : Nat → Bool} :
    ∀ (gs done : List GSite) (e : Nat), topoG ins done gs = true → (∀ g ∈ gs, R g.out = g.e.eval R) →
      (∀ j, e.testBit j = (readyB ins done j && R j)) →
      ∀ j, (runG gs e).testBit j = (readyB ins (done ++ gs) j && R j)
  | [], done, e, _, _, h => by simpa [runG] using h
  | g :: gs, done, e, ht, hfix, h => by
      simp only [topoG, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at ht
      obtain ⟨⟨hfresh, hrd⟩, hrest⟩ := ht
      have hval : g.e.eval e.testBit = R g.out := by
        rw [hfix g (List.mem_cons_self ..)]
        exact GE.eval_congr g.e fun j hj => by rw [h j, hrd j hj, Bool.true_and]
      have hstep : ∀ j, (if g.e.eval e.testBit then e ||| 2 ^ g.out else e).testBit j =
          (readyB ins (done ++ [g]) j && R j) := by
        intro j
        have hr : readyB ins (done ++ [g]) j = (readyB ins done j || g.out == j) := by
          simp [readyB, List.any_append, Bool.or_assoc]
        rw [hr, hval]
        by_cases hj : g.out = j
        · subst hj
          have h0 := h g.out
          rw [hfresh, Bool.false_and] at h0
          cases hR : R g.out <;> simp [hR, h0, Nat.testBit_or, Nat.testBit_two_pow]
        · have hb : (g.out == j) = false := by simpa using hj
          cases hR : R g.out <;> simp [hR, h j, Nat.testBit_or, Nat.testBit_two_pow, hj, hb]
      have := runG_inv gs (done ++ [g]) _ hrest (fun g' hg => hfix g' (List.mem_cons_of_mem _ hg)) hstep
      intro j; simpa [runG, List.append_assoc] using this j

/-- **Soundness of the run**: a packed bit the program writes is `R`'s. -/
theorem runG_sound {ins : List Nat} {R : Nat → Bool} {gs : List GSite} {e₀ : Nat}
    (ht : topoG ins [] gs = true) (hfix : ∀ g ∈ gs, R g.out = g.e.eval R)
    (h₀ : ∀ j, e₀.testBit j = (ins.contains j && R j)) {j : Nat} (hj : gs.any (·.out == j) = true) :
    (runG gs e₀).testBit j = R j := by
  rw [runG_inv gs [] e₀ ht hfix (fun j => by simpa [readyB] using h₀ j) j]
  simp [readyB, hj]

/-! ## The layout: disjoint windows by construction -/

/-- The true packed bits from offset `o`: bit `j` of the declaration whose window holds `j`. -/
def truthR (σ : String → Int) (rd : String → Nat → Bool) (j : Nat) : Nat → List DeclT → Bool
  | _, [] => false
  | o, d :: ds => if o ≤ j ∧ j < o + d.width σ then rd d.name (j - o) else truthR σ rd j (o + d.width σ) ds

theorem truthR_at {σ : String → Int} {rd : String → Nat → Bool} {n : String} {i : Nat} :
    ∀ (ds : List DeclT) (o : Nat), i < ((findDecl ds n).map (·.width σ)).getD 0 →
      ∃ o', (layoutR σ o ds).lookup n = some o' ∧ o ≤ o' ∧ truthR σ rd (o' + i) o ds = rd n i
  | [], _, h => by simp [findDecl] at h
  | d :: ds, o, h => by
      by_cases hd : d.name = n
      · subst hd; simp_all [findDecl, layoutR, truthR]
      · have hd' : (n == d.name) = false := by simpa using Ne.symm hd
        obtain ⟨o', h1, h2, h3⟩ := truthR_at ds (o + d.width σ) (by simpa [findDecl, hd] using h)
        refine ⟨o', by simp [layoutR, List.lookup, hd', h1], by omega, ?_⟩
        rw [truthR, if_neg (by omega), h3]

/-- The true packed bits of the reads `rd` at the layout. -/
def truth (s : Summary) (σ : String → Int) (rd : String → Nat → Bool) (j : Nat) : Bool := truthR σ rd j 0 s.decls

theorem truth_at {s : Summary} {σ : String → Int} {rd : String → Nat → Bool} {n : String} {i : Nat}
    (hi : i < s.dw σ n) : truth s σ rd (layout s σ n + i) = rd n i := by
  obtain ⟨o', h1, -, h3⟩ := truthR_at (rd := rd) s.decls 0 hi
  simp [truth, layout, h1, h3]

theorem layout_inj {s : Summary} {σ : String → Int} {n m : String} {i j : Nat} (hi : i < s.dw σ n)
    (hj : j < s.dw σ m) (h : layout s σ n + i = layout s σ m + j) : n = m ∧ i = j := by
  have h1 := truth_at (rd := fun a b => decide (a = m ∧ b = j)) hi
  rw [h, truth_at hj] at h1
  simpa using h1.symm

/-! ## The compiled program -/

theorem mem_bitsG {σ : String → Int} {dw off : String → Nat} {sk : PSk} {o tw : Nat} :
    ∀ {c : Nat} {gs : List GSite}, bitsG σ dw off sk o tw c = some gs → ∀ {g}, g ∈ gs →
      ∃ k < c, g.out = o + k ∧ sk.compile σ dw off tw k = some g.e
  | 0, _, h, _, hg => by cases h; cases hg
  | c + 1, gs, h, g, hg => by
      simp only [bitsG, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨gs', h1, g', h2, rfl⟩ := h
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨k, hk, h3, h4⟩ := mem_bitsG h1 hg; exact ⟨k, by omega, h3, h4⟩
      · simp only [List.mem_singleton] at hg; subst hg; exact ⟨c, by omega, rfl, h2⟩

theorem mem_compileNet {s : Summary} {σ : String → Int} {off : String → Nat} :
    ∀ {ord : List Nat} {prog : List GSite}, compileNet s σ off ord = some prog → ∀ {g}, g ∈ prog →
      ∃ i ∈ ord, ∃ ls, s.lsites[i]? = some ls ∧ ∃ gs, siteG s σ off ls = some gs ∧ g ∈ gs
  | [], _, h, _, hg => by cases h; cases hg
  | i :: ord, prog, h, g, hg => by
      simp only [compileNet, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ls, hls, gs, hgs, rest, hrest, rfl⟩ := h
      rcases List.mem_append.mp hg with hg | hg
      · exact ⟨i, List.mem_cons_self .., ls, hls, gs, hgs, hg⟩
      · obtain ⟨j, hj, ls', h1, h2⟩ := mem_compileNet hrest hg
        exact ⟨j, List.mem_cons_of_mem _ hj, ls', h1, h2⟩

/-- Every compiled bit is bit `k` of a flat site's target window `T`, inside the declared width. -/
theorem mem_prog {s : Summary} {σ : String → Int} {ord : List Nat} {prog : List GSite}
    (hc : compileNet s σ (layout s σ) ord = some prog) {g : GSite} (hg : g ∈ prog) :
    ∃ ls ∈ s.lsites, ls.hdrs = [] ∧ ∃ T, ls.site.tgt.win σ (s.dw σ) = T ∧ ∃ k < T.2.2, T.2.1 + k < s.dw σ T.1 ∧
      g.out = layout s σ T.1 + (T.2.1 + k) ∧
      (rhsSk ls.site.proc ls.site.rds).compile σ (s.dw σ) (layout s σ) T.2.2 k = some g.e := by
  obtain ⟨i, -, ls, hls, gs, hgs, hgl⟩ := mem_compileNet hc hg
  simp only [siteG] at hgs
  split at hgs
  · rename_i hw
    simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hw
    obtain ⟨k, hk, hout, hcomp⟩ := mem_bitsG hgs hgl
    exact ⟨ls, List.mem_of_getElem? hls, hw.1, _, rfl, k, hk, by omega, by rw [hout, Nat.add_assoc], hcomp⟩
  · cases hgs

/-- **The true bits of a settled state are a fixpoint of the compiled program.** -/
theorem fix_of_eqs {s : Summary} {σ : String → Int} {ord : List Nat} {prog : List GSite} {st : SvState}
    (hc : compileNet s σ (layout s σ) ord = some prog) (heqs : s.EqsL σ st) :
    ∀ g ∈ prog, truth s σ st.boolAt g.out = g.e.eval (truth s σ st.boolAt) := by
  intro g hg
  obtain ⟨ls, hls, hflat, T, hT, k, hk, hw, hout, hcomp⟩ := mem_prog hc hg
  have he : s.EqSiteL σ σ st ls := by have := heqs ls hls; rwa [hflat] at this
  unfold Summary.EqSiteL at he; rw [hT] at he
  rw [PSk.compile_sound (fun n i hi => truth_at hi) _ _ _ _ hcomp, hout, truth_at hw, he k hk]

/-- The netlist view of a design without `always_comb` is its procedural view. -/
theorem eqsL_of_eqs {s : Summary} {σ : String → Int} {st : SvState}
    (hp : s.lsites.all (fun l => !isCombProc l.site.proc) = true) (h : s.Eqs σ st ∧ s.Knowns σ st) :
    s.EqsL σ st ∧ s.Knowns σ st := by
  refine ⟨fun ls hls => ?_, h.2⟩
  have hne : ∀ b, ls.site.proc ≠ .alwaysComb b := fun b hb => by
    simpa [hb, isCombProc] using List.all_eq_true.mp hp ls hls
  simpa only [Summary.EqSiteL, Summary.EqSite, rhsSk_of_ne hne, PSk.bit] using h.1 ls hls

/-! ## The obligations of `eq_viewL` for a flat design, in closed decidable form -/

instance PSk.decWidthOk (σ : String → Int) (dw : String → Nat) (tw : Nat) : ∀ p : PSk, Decidable (p.WidthOk σ dw tw)
  | .leaf sk => inferInstanceAs (Decidable (sk.WidthOkC σ dw tw))
  | .ite c a b | .ovr c a b => have := PSk.decWidthOk σ dw tw a; have := PSk.decWidthOk σ dw tw b
      inferInstanceAs (Decidable (c.WidthOkC σ dw 1 ∧ a.WidthOk σ dw tw ∧ b.WidthOk σ dw tw))
  | .blk a => PSk.decWidthOk σ dw tw a
  | .cases s its d => inferInstanceAs (Decidable (s.SelfOk σ dw ∧
      (∀ it ∈ its, (∀ v ∈ it.1, v.width = s.width σ dw) ∧ it.2.WidthOkC σ dw tw) ∧ d.WidthOkC σ dw tw))

theorem widthOblL_of_plain {s : Summary} {σ : String → Int} (hp : s.lsites.all (·.hdrs.isEmpty) = true)
    (h : ∀ ls ∈ s.lsites, (rhsSk ls.site.proc ls.site.rds).WidthOk σ (s.dw σ) (ls.site.tgt.win σ (s.dw σ)).2.2) :
    s.WidthOblL σ := fun ls hls => by rw [List.isEmpty_iff.mp (List.all_eq_true.mp hp ls hls)]; exact h ls hls

theorem noSelfRead_of_plain {s : Summary} {σ : String → Int} (hp : s.lsites.all (·.hdrs.isEmpty) = true)
    (hm : ∀ b ∈ s.lsites, b.site.more = [])
    (h : ∀ ls ∈ s.lsites, ∀ r ∈ ls.site.rds, (r.rd σ).overlaps (ls.site.tgt.win σ (s.dw σ)) = false) :
    s.NoSelfRead σ :=
  ⟨fun ls hls _ => by rw [List.isEmpty_iff.mp (List.all_eq_true.mp hp ls hls)]; exact h ls hls,
    by rw [if_pos hm]; trivial⟩

/-- A bit the program writes is known, and its name is bound at the declared width. -/
theorem known_of_prog {s : Summary} {σ : String → Int} {ord : List Nat} {prog : List GSite} {st : SvState}
    (hc : compileNet s σ (layout s σ) ord = some prog) (hK : s.Knowns σ st) {y : String} {j : Nat}
    (hj : j < s.dw σ y) (hw : prog.any (·.out == layout s σ y + j) = true) :
    (∃ v, SvState.lookup st y = some v ∧ v.width = s.dw σ y) ∧ KnownBit st y j := by
  obtain ⟨g, hg, hgo⟩ := List.any_eq_true.mp hw
  obtain ⟨ls, hls, hflat, T, hT, k, hk, hwk, hout, -⟩ := mem_prog hc hg
  obtain ⟨rfl, rfl⟩ := layout_inj hwk hj (by rw [← hout]; simpa using hgo)
  have h : s.KnownSite σ σ st ls := by have := hK ls hls; rwa [hflat] at this
  unfold Summary.KnownSite at h; rw [hT] at h
  exact h k hk

/-! ## Inputs and outputs -/

/-- The input values `(name, value)`, packed at the layout. -/
def packIns (off : String → Nat) : List (String × Nat) → Nat
  | [] => 0
  | (n, v) :: xs => (v <<< off n) ||| packIns off xs

/-- The packed bits of the names `xs`. -/
def inBits (off dw : String → Nat) (xs : List String) : List Nat :=
  xs.flatMap fun n => (List.range (dw n)).map (off n + ·)

theorem packIns_spec {s : Summary} {σ : String → Int} {rd : String → Nat → Bool} : ∀ xs : List (String × Nat),
      (∀ p ∈ xs, p.2 < 2 ^ s.dw σ p.1 ∧ ∀ i < s.dw σ p.1, rd p.1 i = p.2.testBit i) → ∀ j,
      (packIns (layout s σ) xs).testBit j =
        ((inBits (layout s σ) (s.dw σ) (xs.map Prod.fst)).contains j && truth s σ rd j)
  | [], _, j => by simp [packIns, inBits]
  | (n, v) :: xs, h, j => by
      have ih := packIns_spec xs (fun p hp => h p (List.mem_cons_of_mem _ hp)) j
      obtain ⟨hv, hrd⟩ := h (n, v) (List.mem_cons_self ..)
      have hin : (layout s σ n ≤ j ∧ j < layout s σ n + s.dw σ n) ↔ ∃ i < s.dw σ n, layout s σ n + i = j :=
        ⟨fun ⟨h1, h2⟩ => ⟨j - layout s σ n, by omega, by omega⟩, fun ⟨i, hi, h⟩ => by omega⟩
      simp only [packIns, Nat.testBit_or, Nat.testBit_shiftLeft, inBits, List.map_cons, List.flatMap_cons,
        List.contains_append, ih]
      by_cases hj : layout s σ n ≤ j ∧ j < layout s σ n + s.dw σ n
      · obtain ⟨i, hi, rfl⟩ := hin.mp hj
        simp [truth_at hi, hrd i hi, hi]
      · have : ¬ ∃ i < s.dw σ n, layout s σ n + i = j := fun h => hj (hin.mpr h)
        have hb : (v.testBit (j - layout s σ n) && decide (j ≥ layout s σ n)) = false := by
          by_cases h1 : layout s σ n ≤ j
          · have : s.dw σ n ≤ j - layout s σ n := by omega
            simp [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) this))]
          · simp [h1]
        have hb' : (decide (j ≥ layout s σ n) && v.testBit (j - layout s σ n)) = false := by
          rw [Bool.and_comm]; exact hb
        simp [hb', this]

/-- **An output bit of a settled state, read off the run** (any bit the program writes). -/
theorem out_bit {s : Summary} {σ : String → Int} {ord : List Nat} {prog : List GSite} {st : SvState}
    {xs : List (String × Nat)} (hc : compileNet s σ (layout s σ) ord = some prog) (heqs : s.EqsL σ st)
    (ht : topoG (inBits (layout s σ) (s.dw σ) (xs.map Prod.fst)) [] prog = true)
    (hxs : ∀ p ∈ xs, p.2 < 2 ^ s.dw σ p.1 ∧ ∀ i < s.dw σ p.1, st.boolAt p.1 i = p.2.testBit i)
    {y : String} {j : Nat} (hj : j < s.dw σ y) (hw : prog.any (·.out == layout s σ y + j) = true) :
    st.boolAt y j = (runG prog (packIns (layout s σ) xs)).testBit (layout s σ y + j) := by
  rw [runG_sound ht (fix_of_eqs hc heqs) (packIns_spec xs hxs) hw, truth_at hj]

theorem bv_congr {W : Nat} {f g : Nat → Bool} (h : ∀ j < W, f j = g j) : XF.bv W f = XF.bv W g :=
  BitVec.eq_of_getLsbD_eq fun j hj => by rw [XF.getLsbD_bv hj, XF.getLsbD_bv hj, h j hj]

/-- An input port holding `ofBitVec x` is packed as `x.toNat` (the premise `hxs` of `exh_out`, one input). -/
theorem in_of_ofBitVec {s : Summary} {σ : String → Int} {st : SvState} {n : String} {w : Nat} {x : BitVec w}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) (hw : s.dw σ n = w) :
    (n, x.toNat).2 < 2 ^ s.dw σ (n, x.toNat).1 ∧
      ∀ i < s.dw σ (n, x.toNat).1, st.boolAt (n, x.toNat).1 i = (n, x.toNat).2.testBit i := by
  subst hw; exact ⟨x.isLt, fun i hi => by rw [SvState.boolAt_ofBitVec h hi, BitVec.testBit_toNat]⟩

/-- **An output of a settled state, read off the run** (`sv_exhaustive`'s one lemma; every premise but the
first is a closed decidable fact over bit indices, or comes from the stimulus). -/
theorem exh_out {s : Summary} {σ : String → Int} {st : SvState} {ord : List Nat} {prog : List GSite}
    {xs : List (String × Nat)} (hEK : s.EqsL σ st ∧ s.Knowns σ st) (hc : compileNet s σ (layout s σ) ord = some prog)
    (ht : topoG (inBits (layout s σ) (s.dw σ) (xs.map Prod.fst)) [] prog = true)
    (hxs : ∀ p ∈ xs, p.2 < 2 ^ s.dw σ p.1 ∧ ∀ i < s.dw σ p.1, st.boolAt p.1 i = p.2.testBit i)
    {y : String} {W : Nat} (hW : s.dw σ y = W) (hW0 : 0 < W)
    (hout : (List.range W).all (fun j => prog.any (·.out == layout s σ y + j)) = true) :
    SvState.lookup st y =
      some (LVec.ofBitVec (XF.bv W fun j => (runG prog (packIns (layout s σ) xs)).testBit (layout s σ y + j))) := by
  have hj : ∀ j < W, prog.any (·.out == layout s σ y + j) = true := fun j hj => by
    simpa using List.all_eq_true.mp hout j (List.mem_range.mpr hj)
  subst hW
  obtain ⟨⟨v, hv, hvw⟩, -⟩ := known_of_prog hc hEK.2 hW0 (hj 0 hW0)
  rw [hv, SvState.lookup_eq_ofBitVec_bv hv hvw fun k hk => (known_of_prog hc hEK.2 hk (hj k hk)).2,
    bv_congr fun j hjw => out_bit hc hEK.1 ht hxs hjw (hj j hjw)]

end LeanModels.Sv.Exh
