import LeanModels.Sv.CombEqShape

/-!
# `sv_equations`, stage 3: the producer theorem

From a design in the fragment of `PDesign.summary`, with the structural proofs `CombDesign` and
`Acyclic` (the product of `sv_structure`) and a settled state `st` (`CombEqs`, `StateShape`, known
inputs), this file proves the **netlist view**: for every located site `ls` of the summary and every
valuation `σ'` of its enclosing loops,

* `EqSite` — the pointwise Boolean equations
  `st.boolAt n (lo + k) = (skRhs …).bit σ' dw st.boolAt k` for the bits `k` of the site's target
  window `(n, lo, w)`, with the SV's gate structure preserved (`Sk.bit`);
* `KnownSite` — those target bits are known (`0`/`1`), and the target signal is bound at its
  declared width in `st`.

Both come from the one x-free knownness theorem of lane K (`CombKnown.settled`), whose two static
hypotheses (`XFree`, `Covered`) are DERIVED here from compact obligations on the summary:

* `EqFrag` — decidable: the right-hand sides are in the fragment, literals carry no `x`/`z`;
* `WidthObl` — operand widths equal target widths (otherwise `fitExpr2` inserts a `resize`);
* `BitReadObl` — a bit read is inside the declared vector;
* `CoverObl` — every bit a read observes has a source (an input bit, or a bit some site writes).

The loops are quantified over `Nat` (`LoopsN`), so the equations read `∀ i, i < N → …`.
-/

namespace LeanModels.Sv
namespace CombEq
open CombView

/-! ## Loop quantifiers over `Nat` -/

/-- `P` holds at every valuation of the loops (outermost first), the indices being naturals. -/
def LoopsN : List Hdr → (String → Int) → ((String → Int) → Prop) → Prop
  | [], σ, P => P σ
  | h :: hs, σ, P =>
      ∀ i : Nat, h.c0 ≤ (i : Int) → (i : Int) < h.bound.eval σ →
        LoopsN hs (bindσ h.g (i : Int) σ) P

/-- `P` holds at SOME valuation of the loops. -/
def LoopsE : List Hdr → (String → Int) → ((String → Int) → Prop) → Prop
  | [], σ, P => P σ
  | h :: hs, σ, P =>
      ∃ i : Nat, h.c0 ≤ (i : Int) ∧ (i : Int) < h.bound.eval σ ∧
        LoopsE hs (bindσ h.g (i : Int) σ) P

theorem LoopsN_of_reach : ∀ (hs : List Hdr) (σ : String → Int) (P : (String → Int) → Prop),
    (∀ σ', Reach hs σ σ' → P σ') → LoopsN hs σ P
  | [], σ, P, H => H σ rfl
  | h :: hs, σ, P, H => by
      intro i h1 h2
      exact LoopsN_of_reach hs _ P (fun σ' hr => H σ' ⟨(i : Int), And.intro h1 h2, hr⟩)

theorem reach_of_LoopsE : ∀ (hs : List Hdr) (σ : String → Int) (P : (String → Int) → Prop),
    LoopsE hs σ P → ∃ σ', Reach hs σ σ' ∧ P σ'
  | [], σ, P, H => ⟨σ, rfl, H⟩
  | h :: hs, σ, P, ⟨i, h1, h2, H⟩ => by
      obtain ⟨σ', hr, hp⟩ := reach_of_LoopsE hs _ P H
      exact ⟨σ', ⟨(i : Int), And.intro h1 h2, hr⟩, hp⟩

/-! ## Skeleton facts -/

theorem partsT_leaves {ds : List DeclT} :
    ∀ (ps : List PExpr) (rs : List Acc), partsRd? ds ps = .ok rs →
      partLeaves (partsT ps rs) = rs
  | [], rs, h => by
      simp only [partsRd?, Except.ok.injEq] at h
      subst h
      simp [partsT, partLeaves]
  | p :: ps, rs, h => by
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
            simp only [List.nil_append]
            rw [partsT_lit]
            simp [partLeaves, partsT_leaves ps rb hq]
          · have hnl : ∀ v, p ≠ .lit v := fun v h => hpl ⟨v, h⟩
            rw [partRd?_of_ne hnl] at hp
            obtain ⟨a, hl, rfl⟩ := rdsLeaf_cases hp
            rw [partsT_of_ne hnl]
            simp [partLeaves, partsT_leaves ps rb hq]

/-- The skeleton's access leaves are exactly the reads. -/
theorem skRhs_leaves {ds : List DeclT} {v : PExpr} {rs : List Acc}
    (h : rhsRds? ds v = .ok rs) (hf : fragOk v = true) : (skRhs v rs).leaves = rs := by
  by_cases hfill : ∃ b, v = .fill b
  · obtain ⟨b, rfl⟩ := hfill
    simp only [rhsRds?, Except.ok.injEq] at h
    subst h
    simp [skRhs, Sk.leaves]
  by_cases hcat : ∃ ps, v = .concat ps
  · obtain ⟨ps, rfl⟩ := hcat
    have h' : partsRd? ds ps = .ok rs := by simpa [rhsRds?, rdsOf?] using h
    simp only [skRhs, Sk.leaves]
    exact partsT_leaves ps rs h'
  · have hn1 : ∀ b, v ≠ .fill b := fun b h => hfill ⟨b, h⟩
    have hn2 : ∀ ps, v ≠ .concat ps := fun ps h => hcat ⟨ps, h⟩
    rw [rhsRds?_of_ne hn1] at h
    rw [fragOk_of_ne hn1 hn2] at hf
    rw [skRhs_of_ne hn1 hn2]
    exact skT_leaves v rs h hf

theorem site_sk {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (hs : siteOf? ds pos p = .ok st) (hf : fragOk (rhsOf p) = true) :
    (skRhs (rhsOf p) st.rds).leaves = st.rds := by
  rcases siteOf?_cases hs with ⟨t, v, rds, rfl, hrds, rfl⟩ | ⟨l, v, tg, rds, rfl, htg, hrds, rfl⟩
  · exact skRhs_leaves hrds hf
  · exact skRhs_leaves hrds hf

/-- A bit read lies inside the declared vector (the lower bound is already in `AutoObl`). -/
def accBitUpper (dwv : String → Nat) (σ' : String → Int) : Acc → Prop
  | .bit n a => a.eval σ' + 1 ≤ (dwv n : Int)
  | _ => True

end CombEq

/-! ## The obligations on the summary (what the player closes) -/

namespace CombView
namespace Summary
open LeanModels.Sv.CombEq

variable (s : Summary)

/-- Every right-hand side is in the fragment of `sv_equations` and its literals are known. -/
def EqFrag : Prop :=
  ∀ ls ∈ s.lsites, fragOk (rhsOf ls.site.proc) = true ∧
    (skRhs (rhsOf ls.site.proc) ls.site.rds).knownB = true

instance : Decidable s.EqFrag := by unfold EqFrag; infer_instance

/-- Bit reads inside their vectors. -/
def BitReadObl (σ : String → Int) : Prop :=
  ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' => ∀ r ∈ ls.site.rds, accBitUpper (s.dw σ) σ' r

/-- Operand widths equal the target width. -/
def WidthObl (σ : String → Int) : Prop :=
  ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' =>
    (skRhs (rhsOf ls.site.proc) ls.site.rds).WidthOk σ' (s.dw σ) (ls.site.tgt.win σ' (s.dw σ)).2.2

/-- Bit `p` of signal `n` has a source: an input bit, or a bit inside the window of some site. -/
def SrcS (σ : String → Int) (n : String) (p : Nat) : Prop :=
  (n ∈ s.inputNames ∧ p < s.dw σ n) ∨
  ∃ b ∈ s.lsites, b.site.tgt.name = n ∧
    LoopsE b.hdrs σ fun σ2 =>
      (b.site.tgt.win σ2 (s.dw σ)).2.1 ≤ p ∧
        p < (b.site.tgt.win σ2 (s.dw σ)).2.1 + (b.site.tgt.win σ2 (s.dw σ)).2.2

/-- Every bit a read observes has a source. -/
def CoverObl (σ : String → Int) : Prop :=
  ∀ ls ∈ s.lsites, Loops.all ls.hdrs σ fun σ' =>
    ∀ r ∈ ls.site.rds, ∀ k, k < (r.win σ' (s.dw σ)).2.2 →
      s.SrcS σ r.name ((r.win σ' (s.dw σ)).2.1 + k)

/-- The input ports hold fully known vectors of their declared width (the player's premise: the
tactic cannot know how the inputs were obtained). -/
def InKnown (σ : String → Int) (st : SvState) : Prop :=
  ∀ n ∈ s.inputNames, ∃ v, SvState.lookup st n = some v ∧ v.allKnown = true ∧
    v.width = s.dw σ n

/-- **The equations of one site**: the Boolean bits of its target window are the skeleton's bits. -/
def EqSite (σ σ' : String → Int) (st : SvState) (ls : LSite) : Prop :=
  ∀ k, k < (ls.site.tgt.win σ' (s.dw σ)).2.2 →
    st.boolAt (ls.site.tgt.win σ' (s.dw σ)).1 ((ls.site.tgt.win σ' (s.dw σ)).2.1 + k) =
      (skRhs (rhsOf ls.site.proc) ls.site.rds).bit σ' (s.dw σ) st.boolAt k

/-- **The knownness of one site**: its target bits are known, and its target signal is bound at the
declared width. -/
def KnownSite (σ σ' : String → Int) (st : SvState) (ls : LSite) : Prop :=
  ∀ k, k < (ls.site.tgt.win σ' (s.dw σ)).2.2 →
    (∃ v, SvState.lookup st (ls.site.tgt.win σ' (s.dw σ)).1 = some v ∧
      v.width = s.dw σ (ls.site.tgt.win σ' (s.dw σ)).1) ∧
    KnownBit st (ls.site.tgt.win σ' (s.dw σ)).1 ((ls.site.tgt.win σ' (s.dw σ)).2.1 + k)

/-- The netlist view: every site's equations, at every valuation of its loops. -/
def Eqs (σ : String → Int) (st : SvState) : Prop :=
  ∀ ls ∈ s.lsites, LoopsN ls.hdrs σ fun σ' => s.EqSite σ σ' st ls

def Knowns (σ : String → Int) (st : SvState) : Prop :=
  ∀ ls ∈ s.lsites, LoopsN ls.hdrs σ fun σ' => s.KnownSite σ σ' st ls

end Summary
end CombView

/-! ## Soundness: the instantiated processes are the promised ones -/

namespace CombEq
open CombView

/-- `Summary.sound` with the realized process list kept: `m.processes` IS the closed-form list
`Summary.pairs`, and the instantiation context is the summary's. -/
theorem sound_pairs {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) :
    ∃ (m : Design2) (E : IEnv) (elems : List (String × Nat)),
      d.instantiate2 args (PDesign.surfaceFuel args) = .ok m ∧
      m.decls.toList = s.decls.map (DeclT.toDecl σ) ∧
      m.processes.toList = (s.pairs σ E elems).map Prod.snd ∧
      Ctx σ E elems (s.DW σ) (s.DG σ) (s.EW σ) s.params ∧
      (∀ q ∈ s.pairs σ E elems, Desc s.declNames q.1 q.2) ∧
      (∀ ls ∈ s.lsites, ∃ pos p, siteOf? s.decls pos p = .ok ls.site) := by
  obtain ⟨hloc, hens, hoth, hpar, hsd, hsts, hgen, hspec⟩ := summary_spec hs
  have hok' := hok
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ := hok'
  have hagd : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n) :=
    fun dt hdt n hn => hag n (hdecl dt hdt n hn)
  have h2 := buildDecls_summary (σ := σ) d.decls s.decls hsd env hagd
  have h3 := buildElems_summary (σ := σ) d.decls s.decls hsd env hagd
  have hdim := paramEnv2_dims h1
  have C := ctx_of_env hsd hdim hag hdecl
  obtain ⟨hproc, hsites0⟩ := sitesOf?_spec hsts
  have hsites := lsites_spec hsites0 hspec
  have hfuel : ∀ p ∈ s.hdrPaths, ∀ h ∈ p,
      (h.bound.eval σ - h.c0).toNat < PDesign.surfaceFuel args :=
    fun p hp h hh => surfaceFuel_gt args _ (hauto.2.2 p hp h hh)
  have h4 : expandList2 (env.withDecls (s.decls.map (DeclT.toDecl σ)))
      (s.decls.map fun dt => (dt.name, dt.elemW σ)) (PDesign.surfaceFuel args) d.generates =
      .ok (s.fams.flatMap fun f => TFam.enum
        (procB (s.decls.map fun dt => (dt.name, dt.elemW σ))) σ
        (env.withDecls (s.decls.map (DeclT.toDecl σ))) f) := by
    rw [hgen]
    exact fams_expand2 (env := env.withDecls (s.decls.map (DeclT.toDecl σ)))
      (elems := s.decls.map fun dt => (dt.name, dt.elemW σ)) hag hok hspec hfuel
      s.fams (fun f hf => hf)
  refine ⟨_, env.withDecls (s.decls.map (DeclT.toDecl σ)),
    s.decls.map fun dt => (dt.name, dt.elemW σ), PDesign.instantiate2_of_ok harity h1 h2 h3 h4,
    by simp, ?_, C, pairs_desc C hok hauto hin hsites, hsites⟩
  rw [PDesign.assemble2_processes, hoth, ← hproc]
  have hmap := Summary.enum_map s
    (fun ls σ' E' => (ls.inst σ' (s.dw σ),
      instProcess2 E' (s.decls.map fun dt => (dt.name, dt.elemW σ)) ls.site.proc))
    Prod.snd σ (env.withDecls (s.decls.map (DeclT.toDecl σ)))
  unfold Summary.pairs
  rw [hmap]
  simp only [Summary.enum, List.map_map, List.map_nil, List.append_nil, Function.comp_def]
  try rfl

/-- The facts about one instance a site lemma reads: the context at the reached environment, the
in-range facts, the `AccOK` facts, and the window facts of every read. -/
theorem site_ok {s : Summary} {σ : String → Int} {envD : IEnv} {elems : List (String × Nat)}
    {args : List Int} (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params)
    (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    {ls : LSite} (hls : ls ∈ s.lsites) {σ' : String → Int} {E' : IEnv}
    (hr : ReachE ls.hdrs σ envD σ' E')
    (hbit : ∀ r ∈ ls.site.rds, accBitUpper (s.dw σ) σ' r) :
    Ctx σ' E' elems (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) ∧
    (∀ a ∈ ls.site.tgt :: ls.site.rds,
      AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) a) ∧
    (∀ a ∈ ls.site.rds, (s.find a.name).isSome = true ∧
      0 < (a.win σ' (s.dw σ)).2.2 ∧
      (a.win σ' (s.dw σ)).2.1 + (a.win σ' (s.dw σ)).2.2 ≤ s.dw σ a.name) := by
  have hok' := hok
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ := hok'
  obtain ⟨hauto1, hauto2, hauto3⟩ := hauto
  have hpar : ∀ n ∈ s.params, σ' n = σ n := by
    rcases lsite_hdrs hls with h0 | hp
    · rw [h0] at hr
      have : σ' = σ := hr.1
      subst this
      intro n _; rfl
    · apply Reach_params (ReachE_Reach hr)
      intro h hh
      exact notin_of_nodup (hpaths _ hp).1 (List.mem_map.mpr ⟨h, hh, rfl⟩)
  have C' := Ctx.reachE C hr (ns' := ls.hdrs.map (·.g) ++ s.params) (fun n hn => hn)
  have hin' := (Loops.all_iff _ _ _).mp (hin ls hls) σ' (ReachE_Reach hr)
  have hauto' := (Loops.all_iff _ _ _).mp (hauto1 ls hls) σ' (ReachE_Reach hr)
  have hInR : ∀ a ∈ ls.site.tgt :: ls.site.rds, s.InR σ σ' a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hm
    · exact hin'.1
    · exact hauto' a hm
  have hso : ∀ a ∈ ls.site.tgt :: ls.site.rds,
      AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) a := by
    intro a ha
    refine ⟨?_, accGeom_of hpar hdecl (hacc ls hls a ha) (hInR a ha) (hauto2 ls hls a ha), ?_⟩
    · have hn : a.name ∈ s.declNames := by
        apply hnames ls hls
        simp only [TSite.names, List.mem_cons, List.mem_map]
        rcases List.mem_cons.mp ha with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr ⟨a, hm, rfl⟩
      simpa [Summary.DW] using find_isSome_of_mem hn
    · intro x hx n hn
      apply haff ls hls n
      simp only [TSite.affNames, List.mem_append, List.mem_flatMap]
      rcases List.mem_cons.mp ha with rfl | hm
      · exact Or.inl ⟨x, hx, hn⟩
      · exact Or.inr ⟨a, hm, x, hx, hn⟩
  refine ⟨C', hso, fun a ha => ?_⟩
  have hn : a.name ∈ s.declNames := by
    apply hnames ls hls
    simp only [TSite.names, List.mem_cons, List.mem_map]
    exact Or.inr ⟨a, ha, rfl⟩
  have hdn := find_isSome_of_mem hn
  have hg : AccGeom σ' (s.DG σ) (s.EW σ) a :=
    accGeom_of hpar hdecl (hacc ls hls a (List.mem_cons_of_mem _ ha))
      (hInR a (List.mem_cons_of_mem _ ha)) (hauto2 ls hls a (List.mem_cons_of_mem _ ha))
  obtain ⟨hpos, hle⟩ := acc_win_facts (σd := σ) hdn hg (fun n x h => by
    have := hbit a ha
    rw [h] at this
    exact this)
  exact ⟨hdn, hpos, hle⟩

/-! ## The producer theorem -/

theorem dw_some {s : Summary} {σ : String → Int} (n : String) (h : (s.DW σ n).isSome = true) :
    s.DW σ n = some (s.dw σ n) := by
  have hf : (s.find n).isSome = true := by simpa [Summary.DW] using h
  exact DW_eq hf

theorem mem_declNames_of_input {s : Summary} {n : String} (h : n ∈ s.inputNames) :
    n ∈ s.declNames := by
  simp only [Summary.inputNames, List.mem_filterMap] at h
  obtain ⟨dt, hdt, h⟩ := h
  simp only [Summary.declNames, List.mem_map]
  refine ⟨dt, hdt, ?_⟩
  by_cases hi : dt.isInput = true
  · simp [hi] at h; exact h
  · simp [hi] at h

/-- **The equations and knownness of a design `X.sem N` of the fragment.** -/
theorem eq_of_summary {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hfrag : s.EqFrag) (hwid : s.WidthObl σ) (hbit : s.BitReadObl σ) (hcov : s.CoverObl σ)
    {st : SvState} (hinK : s.InKnown σ st)
    (hc : CombDesign (d.instantiateGD2 args)) (ha : Acyclic (d.instantiateGD2 args))
    (heqs : CombEqs (d.instantiateGD2 args) st) (hsh : StateShape (d.instantiateGD2 args) st) :
    s.Eqs σ st ∧ s.Knowns σ st := by
  obtain ⟨m, E, elems, hm, hdecl, hproc, C, hdesc, hsites⟩ :=
    sound_pairs hs harity h1 hag hok hauto hin
  have hGD := instantiateGD2_eq_of_comb hm hc
  rw [hGD] at hc ha heqs hsh
  have hik : m.InputsKnown st := by
    intro n hn
    rw [Realized.inputNames hdecl] at hn
    obtain ⟨v, hv, hk, hw⟩ := hinK n hn
    refine ⟨v, hv, hk, ?_⟩
    have hfn : (s.find n).isSome = true := find_isSome_of_mem (mem_declNames_of_input hn)
    rw [declWidth_eq hdecl, dw_some n (by simpa [Summary.DW] using hfn), hw]
  -- instances
  have hP : ∀ q ∈ s.pairs σ E elems, ∃ ls ∈ s.lsites, ∃ σ' E', ReachE ls.hdrs σ E σ' E' ∧
      q = (ls.inst σ' (s.dw σ), instProcess2 E' elems ls.site.proc) := by
    intro q hq
    unfold Summary.pairs at hq
    rw [mem_enum_E] at hq
    exact hq
  have hdw : ∀ n, (s.DW σ n).isSome = true → s.DW σ n = some (s.dw σ n) :=
    fun n h => dw_some n h
  -- the shape of every instantiated process
  have hshape : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      instProcess2 E' elems ls.site.proc = Process2.assign (ls.site.tgt.lhs σ')
        ((skRhs (rhsOf ls.site.proc) ls.site.rds).low σ' (ls.site.tgt.win σ' (s.dw σ)).2.2) := by
    intro ls hls σ' E' hr
    obtain ⟨pos, p, hp⟩ := hsites ls hls
    have hpp := siteOf?_proc hp
    have hb : ∀ r ∈ ls.site.rds, accBitUpper (s.dw σ) σ' r :=
      (Loops.all_iff _ _ _).mp (hbit ls hls) σ' (ReachE_Reach hr)
    obtain ⟨C', hso, -⟩ := site_ok C hok hauto hin hls hr hb
    have hw := (Loops.all_iff _ _ _).mp (hwid ls hls) σ' (ReachE_Reach hr)
    have hf := (hfrag ls hls).1
    subst hpp
    exact proc_shape C' hdw hp hso hf hw
  -- index-level facts
  have hform : ∀ (i : Nat) (p : Process2), m.processes[i]? = some p →
      ∃ q ∈ s.pairs σ E elems, q.2 = p := by
    intro i p hp
    have h1 : m.processes.toList[i]? = some p := by rw [Array.getElem?_toList]; exact hp
    rw [hproc, List.getElem?_map] at h1
    cases hL : (s.pairs σ E elems)[i]? with
    | none => simp [hL] at h1
    | some q =>
        simp only [hL, Option.map_some, Option.some.injEq] at h1
        exact ⟨q, List.mem_of_getElem? hL, h1⟩
  have hex : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      ∃ i : Nat, m.processes[i]? = some (Process2.assign (ls.site.tgt.lhs σ')
        ((skRhs (rhsOf ls.site.proc) ls.site.rds).low σ' (ls.site.tgt.win σ' (s.dw σ)).2.2)) := by
    intro ls hls σ' E' hr
    have hmem : (ls.inst σ' (s.dw σ), instProcess2 E' elems ls.site.proc) ∈
        s.pairs σ E elems := by
      unfold Summary.pairs
      rw [mem_enum_E]
      exact ⟨ls, hls, σ', E', hr, rfl⟩
    have h2 : instProcess2 E' elems ls.site.proc ∈ m.processes.toList := by
      rw [hproc]; exact List.mem_map.mpr ⟨_, hmem, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp h2
    refine ⟨i, ?_⟩
    rw [← Array.getElem?_toList, hi, hshape ls hls σ' E' hr]
  have hok' := hok
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl', hacc, hkeys⟩ := hok'
  have hfindTgt : ∀ ls ∈ s.lsites, (s.find ls.site.tgt.name).isSome = true := fun ls hls =>
    find_isSome_of_mem (hnames ls hls _ (by simp [TSite.names]))
  have hfindRd : ∀ ls ∈ s.lsites, ∀ a ∈ ls.site.rds, (s.find a.name).isSome = true :=
    fun ls hls a ha => find_isSome_of_mem (hnames ls hls _ (by
      simp only [TSite.names, List.mem_cons, List.mem_map]
      exact Or.inr ⟨a, ha, rfl⟩))
  -- the leaves of every instance are declared, non-empty and in range
  have hleaf : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      ∀ a ∈ ls.site.rds, LeafOk m σ' (s.dw σ) a := by
    intro ls hls σ' E' hr a ha
    have hb : ∀ r ∈ ls.site.rds, accBitUpper (s.dw σ) σ' r :=
      (Loops.all_iff _ _ _).mp (hbit ls hls) σ' (ReachE_Reach hr)
    obtain ⟨-, -, hl⟩ := site_ok C hok hauto hin hls hr hb
    obtain ⟨hdn, hpos, hle⟩ := hl a ha
    refine ⟨?_, hle, hpos⟩
    rw [declWidth_eq hdecl, dw_some a.name (by simpa [Summary.DW] using hdn)]
  -- the lowered right-hand sides are in the x-free fragment
  have hxw : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      ((skRhs (rhsOf ls.site.proc) ls.site.rds).low σ' (ls.site.tgt.win σ' (s.dw σ)).2.2).xfWidth m =
        some (ls.site.tgt.win σ' (s.dw σ)).2.2 := by
    intro ls hls σ' E' hr
    obtain ⟨pos, p, hp0⟩ := hsites ls hls
    have hpp := siteOf?_proc hp0
    subst hpp
    have hleaves := site_sk hp0 (hfrag ls hls).1
    refine low_xfWidth _ (hfrag ls hls).2
      ((Loops.all_iff _ _ _).mp (hwid ls hls) σ' (ReachE_Reach hr)) ?_
    intro a ha
    rw [hleaves] at ha
    exact hleaf ls hls σ' E' hr a ha
  have hxf : m.XFree := by
    intro i t e hp
    obtain ⟨q, hq, hqp⟩ := hform i _ hp
    obtain ⟨ls, hls, σ', E', hr, rfl⟩ := hP q hq
    simp only at hqp
    rw [hshape ls hls σ' E' hr] at hqp
    simp only [Process2.assign.injEq] at hqp
    obtain ⟨rfl, rfl⟩ := hqp
    exact ⟨_, hxw ls hls σ' E' hr⟩
  -- every bit with a summary-level source has a source in the design
  have hsrc : ∀ n p, s.SrcS σ n p → m.Sourced n p := by
    intro n p h
    rcases h with ⟨hn, hp⟩ | ⟨b, hb, hname, hl⟩
    · left
      have hf : (s.find n).isSome = true := by
        unfold Summary.dw at hp
        rcases hfi : s.find n with _ | dt
        · simp [hfi] at hp
        · rfl
      refine ⟨?_, s.dw σ n, ?_, hp⟩
      · rw [Realized.inputNames hdecl]; exact hn
      · rw [declWidth_eq hdecl, dw_some n (by simpa [Summary.DW] using hf)]
    · right
      obtain ⟨σ2, hr2, hwin⟩ := reach_of_LoopsE _ _ _ hl
      obtain ⟨E2, hE2⟩ := Reach_ReachE E hr2
      obtain ⟨i, hi⟩ := hex b hb σ2 E2 hE2
      have hwins : (b.site.tgt.lhs σ2).wins m = [b.site.tgt.win σ2 (s.dw σ)] :=
        Lhs2.wins_of_windows? (acc_windows hdecl b.site.tgt (hfindTgt b hb))
      have hn1 : n = (b.site.tgt.win σ2 (s.dw σ)).1 := by
        rw [Acc.win_name]; exact hname.symm
      refine ⟨i, (b.site.tgt.win σ2 (s.dw σ)).2.1, (b.site.tgt.win σ2 (s.dw σ)).2.2,
        ⟨_, _, hi, ?_⟩, hwin.1, hwin.2⟩
      rw [hwins, hn1]
      exact List.mem_singleton.mpr rfl
  have hcv : m.Covered := by
    intro i t e hp r hr
    obtain ⟨q, hq, hqp⟩ := hform i _ hp
    obtain ⟨e', hpe, hrd, -, -⟩ := hdesc q hq
    rw [hpe] at hqp
    simp only [Process2.assign.injEq] at hqp
    obtain ⟨-, rfl⟩ := hqp
    have hrm := hrd r hr
    obtain ⟨ls, hls, σ', E', hrch, rfl⟩ := hP q hq
    simp only [LSite.inst, List.mem_map] at hrm
    obtain ⟨a, ha, rfl⟩ := hrm
    have hco := (Loops.all_iff _ _ _).mp (hcov ls hls) σ' (ReachE_Reach hrch) a ha
    cases a with
    | whole n =>
        have hfn : (s.find n).isSome = true := hfindRd ls hls _ ha
        simp only [Acc.rd, ReadWin.Covered]
        refine ⟨s.dw σ n, ?_, dw_pos hfn, fun k hk => ?_⟩
        · rw [declWidth_eq hdecl, dw_some n (by simpa [Summary.DW] using hfn)]
        · have h : m.Sourced n (0 + k) := hsrc _ _ (hco k hk)
          simpa using h
    | bit n x => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | cell1 n x => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | row n w r' => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | cell2 n w r' c => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | part1 n h l => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
    | part2 n w r' h l => simp only [Acc.rd, ReadWin.Covered]; intro k hk; exact hsrc _ _ (hco k hk)
  -- the equations and the knownness of every instance
  have hmain : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' →
      s.EqSite σ σ' st ls ∧ s.KnownSite σ σ' st ls := by
    intro ls hls σ' E' hr
    obtain ⟨i, hi⟩ := hex ls hls σ' E' hr
    obtain ⟨pos, p, hp0⟩ := hsites ls hls
    have hpp := siteOf?_proc hp0
    subst hpp
    have hleaves := site_sk hp0 (hfrag ls hls).1
    have hwidth := (Loops.all_iff _ _ _).mp (hwid ls hls) σ' (ReachE_Reach hr)
    have hwins : (ls.site.tgt.lhs σ').wins m = [ls.site.tgt.win σ' (s.dw σ)] :=
      Lhs2.wins_of_windows? (acc_windows hdecl ls.site.tgt (hfindTgt ls hls))
    have hset := fun k (hk : k < (ls.site.tgt.win σ' (s.dw σ)).2.2) =>
      CombKnown.settled hc ha hxf hcv heqs hsh hik i _ _ (ls.site.tgt.win σ' (s.dw σ)).1
        (ls.site.tgt.win σ' (s.dw σ)).2.1 (ls.site.tgt.win σ' (s.dw σ)).2.2 0 hi
        (by rw [hwins]; simp [Win.placed]) k hk
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have h1 := (hset k hk).2
      rw [Nat.zero_add, Expr2.xfBitsZ_of_lt (hxw ls hls σ' E' hr) hk] at h1
      refine h1.trans ?_
      exact low_xfBits (m := m) st.boolAt _ (hfrag ls hls).2 hwidth (fun a ha => by
        rw [hleaves] at ha
        exact hleaf ls hls σ' E' hr a ha) k hk
    · refine ⟨?_, (hset k hk).1⟩
      obtain ⟨v, hv, hdv⟩ := hsh.driven (ls.site.tgt.win σ' (s.dw σ)).1
        ⟨i, (ls.site.tgt.win σ' (s.dw σ)).2.1, (ls.site.tgt.win σ' (s.dw σ)).2.2,
          _, _, hi, by rw [hwins]; exact List.mem_singleton.mpr rfl⟩
      refine ⟨v, hv, ?_⟩
      have hD := declWidth_eq hdecl (ls.site.tgt.win σ' (s.dw σ)).1
      have hfn : (s.find (ls.site.tgt.win σ' (s.dw σ)).1).isSome = true := by
        rw [Acc.win_name]; exact hfindTgt ls hls
      rw [hD, dw_some _ (by simpa [Summary.DW] using hfn)] at hdv
      exact (Option.some.inj hdv).symm
  refine ⟨fun ls hls => LoopsN_of_reach _ _ _ (fun σ' hr => ?_),
    fun ls hls => LoopsN_of_reach _ _ _ (fun σ' hr => ?_)⟩
  · obtain ⟨E', hE'⟩ := Reach_ReachE E hr
    exact (hmain ls hls σ' E' hE').1
  · obtain ⟨E', hE'⟩ := Reach_ReachE E hr
    exact (hmain ls hls σ' E' hE').2

/-- The tactic's form: the valuation is the parameters zipped with the arguments, then the
localparams (`s.val args`), the environment check in a `rfl`-provable form (as `comb_view`). -/
theorem eq_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summary = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args))
    (hfrag : s.EqFrag) (hwid : s.WidthObl (s.val args))
    (hbit : s.BitReadObl (s.val args)) (hcov : s.CoverObl (s.val args))
    {st : SvState} (hinK : s.InKnown (s.val args) st)
    (hc : CombDesign (d.instantiateGD2 args)) (ha : Acyclic (d.instantiateGD2 args))
    (heqs : CombEqs (d.instantiateGD2 args) st) (hsh : StateShape (d.instantiateGD2 args) st) :
    s.Eqs (s.val args) st ∧ s.Knowns (s.val args) st :=
  eq_of_summary hs harity h1 (Agrees_of_map hag) hok hauto hin hfrag hwid hbit hcov hinK hc ha
    heqs hsh

/-- An input port holding `ofBitVec x` is known, at the width `W = w` the obligation names. -/
theorem inKnown_ofBitVec {st : SvState} {n : String} {w W : Nat} {x : BitVec w}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) (hw : w = W) :
    ∃ v, SvState.lookup st n = some v ∧ v.allKnown = true ∧ v.width = W :=
  ⟨_, h, LVec.allKnown_ofBitVec x, by rw [LVec.width_ofBitVec]; exact hw⟩

/-! ## Axiom pins -/

/-- info: 'LeanModels.Sv.CombEq.eq_of_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_of_summary

/-- info: 'LeanModels.Sv.CombEq.eq_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eq_view

/-- info: 'LeanModels.Sv.CombEq.sound_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sound_pairs

end CombEq
end LeanModels.Sv
