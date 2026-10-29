import LeanModels.Sv.CombViewThm

/-!
# `sv_structure`, stage 3: the soundness theorem against `instantiate2`, and the structural
theorems `CombDesign` / `Acyclic` of `name.sem N`

* `Summary.sound` — THE SOUNDNESS THEOREM. If `PDesign.summary d = .ok s`, the parameter stage
  succeeded with an environment `σ` agrees with, and the structural/auto/in-range obligations
  hold, then `d.instantiate2 args` succeeds with a design `m` that REALIZES the summary:
  `m.decls = s.decls.map toDecl`, and `m.processes` is the closed-form list
  `Summary.pairs` (statics, then `range.flatMap body` — no `N`-length enumeration), each
  process an `assign` to exactly the promised window reading only promised windows.
* `comb_of_summary`, `acyclic_of_summary` — `CombDesign` / `Acyclic` of
  `d.instantiateGD2 args` (= `name.sem`), from the obligations the player discharges.
-/

namespace LeanModels.Sv
namespace CombView

/-! ## Inversion lemmas for the recognizers -/

theorem sitesOf?_spec {tag : String} : ∀ {ps : List PProcess} {pos : Nat} {sts : List TSite},
    sitesOf? tag pos ps = .ok sts →
      sts.map TSite.proc = ps ∧ ∀ st ∈ sts, ∃ pos' p, siteOf? pos' p = .ok st
  | [], pos, sts, h => by
      simp only [sitesOf?, Except.ok.injEq] at h
      subst h
      simp
  | p :: ps, pos, sts, h => by
      simp only [sitesOf?] at h
      rcases hs : siteOf? pos p with e | st
      · simp [hs] at h
      · rcases hr : sitesOf? tag (pos + 1) ps with e | sts'
        · simp [hs, hr] at h
        · simp only [hs, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨h1, h2⟩ := sitesOf?_spec hr
          refine ⟨?_, ?_⟩
          · simp [h1, siteOf?_proc hs]
          · intro st' hst'
            rcases List.mem_cons.mp hst' with rfl | hm
            · exact ⟨pos, p, hs⟩
            · exact h2 st' hm

theorem summary_spec {d : PDesign} {s : Summary} (h : d.summary = .ok s) :
    d.localParams = [] ∧ d.enums = [] ∧ d.others = [] ∧ s.params = d.params.map (·.name) ∧
    declsOf? d.decls = .ok s.decls ∧ sitesOf? "plain" 0 d.processes = .ok s.statics ∧
    ((d.generates = [] ∧ s.fam = none) ∨
      ∃ it f, d.generates = [it] ∧ famOf? it = .ok f ∧ s.fam = some f) := by
  unfold PDesign.summary at h
  split at h
  · simp at h
  rename_i h1
  split at h
  · simp at h
  rename_i h2
  split at h
  · simp at h
  rename_i h3
  have hl : d.localParams = [] := by simpa using h1
  have he : d.enums = [] := by simpa using h2
  have ho : d.others = [] := by simpa using h3
  rcases hd : declsOf? d.decls with e | ds
  · simp [hd] at h
  rcases hp : sitesOf? "plain" 0 d.processes with e | sts
  · simp [hd, hp] at h
  rcases hg : d.generates with _ | ⟨it, rest⟩
  · simp only [hd, hp, hg, Except.ok.injEq] at h
    subst h
    exact ⟨hl, he, ho, rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rcases rest with _ | ⟨it2, rest2⟩
    · rcases hf : famOf? it with e | f
      · simp [hd, hp, hg, hf] at h
      · simp only [hd, hp, hg, hf, Except.ok.injEq] at h
        subst h
        exact ⟨hl, he, ho, rfl, rfl, rfl, Or.inr ⟨it, f, rfl, hf, rfl⟩⟩
    · simp [hd, hp, hg] at h

theorem famOf?_spec {it : GenItem} {f : TFam} (h : famOf? it = .ok f) :
    ∃ lbl rc bnd ps, it = .genFor lbl f.g (.int f.c0) (.binary .slt (.genvarRef f.g) bnd)
        (.unary .inc (.genvarRef f.g)) rc (ps.map GenItem.process) ∧
      affOf? bnd = some f.bound ∧ sitesOf? (lbl.getD "genblk") 0 ps = .ok f.body := by
  cases it <;> try (simp [famOf?] at h; done)
  rename_i label g initE bound step rc body
  cases initE <;> try (simp [famOf?] at h; done)
  rename_i c0
  cases bound <;> try (simp [famOf?] at h; done)
  rename_i op l r
  cases op <;> try (simp [famOf?] at h; done)
  cases l <;> try (simp [famOf?] at h; done)
  rename_i g'
  cases step <;> try (simp [famOf?] at h; done)
  rename_i u a
  cases u <;> try (simp [famOf?] at h; done)
  cases a <;> try (simp [famOf?] at h; done)
  rename_i g''
  simp only [famOf?] at h
  by_cases hgg : g' = g ∧ g'' = g
  · have hg1 : g' = g := hgg.1
    have hg2 : g'' = g := hgg.2
    subst g' g''
    rcases hb : affOf? r with _ | b
    · simp [hb] at h
    · rcases hp : procsOf? body with _ | ps
      · simp [hb, hp] at h
      · rcases hs : sitesOf? (label.getD "genblk") 0 ps with e | sts
        · simp [hb, hp, hs] at h
        · simp [hb, hp, hs] at h
          subst h
          exact ⟨label, rc, r, ps, by rw [procsOf?_eq hp], hb, hs⟩
  · simp [hgg] at h

theorem paramEnv2_dims {d : PDesign} {args : List Int} {env : IEnv}
    (h : d.paramEnv2 args = .ok env) :
    ∃ env2 : IEnv, env = { env2 with dims := dimTable env2 d.decls } := by
  unfold PDesign.paramEnv2 at h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨e0, -, e1, -, e2, -, pws, -, hfin⟩ := h
  exact ⟨{ e2 with pwidths := pws }, (Res.ok.inj hfin).symm⟩

theorem surfaceFuel_gt (args : List Int) (x : Nat) (hx : x ≤ (args.map Int.natAbs).sum + 60) :
    x < PDesign.surfaceFuel args := by
  show x < ((args.map Int.natAbs).sum + 2) * ((args.map Int.natAbs).sum + 2) + 64
  have := Nat.le_mul_self ((args.map Int.natAbs).sum + 2)
  omega

/-! ## The declaration stage -/

@[simp] theorem toDecl_name (σ : String → Int) (dt : DeclT) : (dt.toDecl σ).name = dt.name := rfl
@[simp] theorem toDecl_width (σ : String → Int) (dt : DeclT) :
    (dt.toDecl σ).width = dt.width σ := rfl
@[simp] theorem toDecl_isInput (σ : String → Int) (dt : DeclT) :
    (dt.toDecl σ).isInput = dt.isInput := rfl
@[simp] theorem toDecl_init (σ : String → Int) (dt : DeclT) : (dt.toDecl σ).init = none := rfl

theorem DeclT.width_pos (σ : String → Int) (dt : DeclT) : 0 < dt.width σ := by
  unfold DeclT.width
  rcases dt.dim with _ | ⟨d, m, l⟩ <;> simp

theorem lookup_widths' (σ : String → Int) :
    ∀ (sd : List DeclT) (n : String),
      (sd.map fun dt => (dt.name, dt.width σ)).lookup n =
        (sd.find? fun dt => dt.name == n).map (DeclT.width σ)
  | [], n => by simp
  | dt :: rest, n => by
      by_cases h : n = dt.name
      · have h1 : (n == dt.name) = true := beq_iff_eq.2 h
        have h2 : (dt.name == n) = true := beq_iff_eq.2 h.symm
        simp [List.lookup, h1, h2]
      · have h1 : (n == dt.name) = false := beq_eq_false_iff_ne.2 h
        have h2 : (dt.name == n) = false := beq_eq_false_iff_ne.2 (Ne.symm h)
        simp [List.lookup, h1, h2, lookup_widths' σ rest n]

theorem lookup_widths (σ : String → Int) (sd : List DeclT) (n : String) :
    ((sd.map (DeclT.toDecl σ)).map fun dc => (dc.name, dc.width)).lookup n =
      (sd.find? fun dt => dt.name == n).map (DeclT.width σ) := by
  rw [List.map_map]
  exact lookup_widths' σ sd n

theorem lookup_elems : ∀ (sd : List DeclT) (n : String),
    (sd.find? fun dt => dt.name == n).isSome = true →
      (sd.map fun dt => (dt.name, 1)).lookup n = some 1
  | [], n, h => by simp at h
  | dt :: rest, n, h => by
      by_cases hn : n = dt.name
      · have h1 : (n == dt.name) = true := beq_iff_eq.2 hn
        simp [List.lookup, h1]
      · have h1 : (n == dt.name) = false := beq_eq_false_iff_ne.2 hn
        have h2 : (dt.name == n) = false := beq_eq_false_iff_ne.2 (Ne.symm hn)
        simp only [List.find?_cons, h2] at h
        simp [List.lookup, h1, lookup_elems rest n h]

theorem find_isSome_of_mem {s : Summary} {n : String} (h : n ∈ s.declNames) :
    (s.find n).isSome = true := by
  unfold Summary.find
  rw [List.find?_isSome]
  simp only [Summary.declNames, List.mem_map] at h
  obtain ⟨dt, hdt, rfl⟩ := h
  exact ⟨dt, hdt, by simp⟩

theorem mem_declNames_of_find {s : Summary} {n : String} (h : (s.find n).isSome = true) :
    n ∈ s.declNames := by
  unfold Summary.find at h
  rw [List.find?_isSome] at h
  obtain ⟨dt, hdt, hn⟩ := h
  simp only [Summary.declNames, List.mem_map]
  exact ⟨dt, hdt, by simpa using hn⟩

theorem ad_dw {s : Summary} {σ : String → Int} {n : String} (hok : s.arrOk n = true) :
    ∃ m, s.AD σ n = some m ∧ s.dw σ n = m.natAbs + 1 := by
  unfold Summary.arrOk at hok
  unfold Summary.AD Summary.dw
  rcases hf : s.find n with _ | dt
  · simp [hf] at hok
  · obtain ⟨nm, i, o, dim⟩ := dt
    cases dim with
    | none => simp [hf] at hok
    | some p =>
      obtain ⟨d, ma, la⟩ := p
      simp only [hf, decide_eq_true_eq] at hok
      subst hok
      refine ⟨ma.eval σ, by simp, ?_⟩
      simp [DeclT.width, Aff.eval_const]

theorem ad_vals {s : Summary} {σ : String → Int} {n : String} {m : Int}
    (hm : s.AD σ n = some m) :
    (s.decls.find? fun dt => dt.name == n).map (DeclT.vals σ) = some [(m, 0)] := by
  unfold Summary.AD Summary.find at hm
  rcases hf : s.decls.find? (fun dt => dt.name == n) with _ | dt
  · simp [hf] at hm
  · obtain ⟨nm, i, o, dim⟩ := dt
    cases dim with
    | none => simp [hf] at hm
    | some p =>
      obtain ⟨d, ma, la⟩ := p
      by_cases hl : la = Aff.const 0
      · subst hl
        simp [hf] at hm
        subst hm
        rw [hf]
        simp [DeclT.vals, Aff.eval_const]
      · simp [hf, hl] at hm

/-- The environment facts of the instantiation, from the declaration stage. -/
theorem ctx_of_env {s : Summary} {d : PDesign} (hsd : declsOf? d.decls = .ok s.decls)
    {σ : String → Int} {env : IEnv}
    (hdim : ∃ env2 : IEnv, env = { env2 with dims := dimTable env2 d.decls })
    (hag : Agrees σ env s.params)
    (hdecl : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, n ∈ s.params) :
    Ctx σ (env.withDecls (s.decls.map (DeclT.toDecl σ))) (s.decls.map fun dt => (dt.name, 1))
      (s.DW σ) (s.AD σ) s.params := by
  obtain ⟨env2, henv⟩ := hdim
  have hagd : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, env2.vals.lookup n = some (σ n) := by
    intro dt hdt n hn
    have := hag n (hdecl dt hdt n hn)
    rw [henv] at this
    exact this
  refine ⟨hag, ?_, ?_, ?_⟩
  · intro n
    exact lookup_widths σ s.decls n
  · intro n hn
    apply lookup_elems
    simpa [Summary.DW, Summary.find] using hn
  · intro n m hm
    have h1 := dimTable_summary d.decls s.decls hsd env2 hagd n
    have h2 : env.dims = dimTable env2 d.decls := by rw [henv]
    show env.dims.lookup n = _
    rw [h2, h1]
    exact ad_vals hm

/-! ## One site, assembled from the obligations -/

theorem siteOK_of {s : Summary} {σd σs : String → Int} {ns : List String} {st : TSite}
    (hdecl : ∀ n ∈ st.names, n ∈ s.declNames) (haff : ∀ n ∈ st.affNames, n ∈ ns)
    (harr : ∀ n ∈ st.arrNames, s.arrOk n = true)
    (hrd : ∀ r ∈ st.rds, s.RdNum σd σs r) (hw : s.InWin σd σs st) :
    SiteOK σs (s.DW σd) (s.AD σd) ns st := by
  refine ⟨?_, haff, ?_, ?_⟩
  · intro n hn
    simpa [Summary.DW] using find_isSome_of_mem (hdecl n hn)
  · intro r hr
    cases r with
    | whole n => trivial
    | bit n a => exact hrd _ hr
    | arr n a =>
      have hnn : s.arrOk n = true :=
        harr n (List.mem_append_right _ (List.mem_filterMap.2 ⟨TRd.arr n a, hr, rfl⟩))
      obtain ⟨m, hm, -⟩ := ad_dw (σ := σd) hnn
      have := hrd _ hr
      simp only [Summary.RdNum, hm, Option.getD_some] at this
      exact ⟨m, hm, this⟩
  · cases ht : st.tgt with
    | whole n => trivial
    | bit n a =>
      simp only [Summary.InWin, ht] at hw
      exact hw.1
    | arr n a =>
      have hnn : s.arrOk n = true := harr n (by simp [TSite.arrNames, ht])
      obtain ⟨m, hm, -⟩ := ad_dw (σ := σd) hnn
      simp only [Summary.InWin, ht, hm, Option.getD_some] at hw
      exact ⟨m, hm, hw.1, hw.2⟩

theorem pairs_desc {s : Summary} {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
    (C : Ctx σ E elems (s.DW σ) (s.AD σ) s.params) (hok : s.StructOk)
    (hrd : (∀ st ∈ s.statics, ∀ r ∈ st.rds, s.RdNum σ σ r) ∧
      (∀ f ∈ s.fam.toList, ∀ i, f.Rng σ i → ∀ st ∈ f.body, ∀ r ∈ st.rds,
        s.RdNum σ (bindσ f.g i σ) r))
    (hin : s.InRangeObl σ)
    (hsites : ∀ st ∈ s.sites, ∃ pos p, siteOf? pos p = .ok st) :
    ∀ q ∈ s.pairs σ E elems, Desc s.declNames q.1 q.2 := by
  obtain ⟨-, hnames, -, hstat, hfam, -, harr⟩ := hok
  have hnm : ∀ n, (s.DW σ n).isSome = true → n ∈ s.declNames := by
    intro n hn
    exact mem_declNames_of_find (by simpa [Summary.DW] using hn)
  intro q hq
  simp only [Summary.pairs, List.mem_append, List.mem_map] at hq
  rcases hq with ⟨st, hst, rfl⟩ | hq
  · obtain ⟨pos, p, hp⟩ := hsites st (by simp [Summary.sites, hst])
    have hso := siteOK_of (s := s) (σd := σ) (σs := σ) (ns := s.params)
      (fun n hn => hnames st (by simp [Summary.sites, hst]) n hn) (hstat st hst)
      (fun n hn => harr st (by simp [Summary.sites, hst]) n hn) (hrd.1 st hst) (hin.1 st hst)
    have h := site_desc C hnm hp hso (.plain st.pos)
    rw [← siteOf?_proc hp] at h
    exact h
  · cases hfm : s.fam with
    | none => simp [hfm] at hq
    | some f =>
      simp only [hfm, List.mem_flatMap, List.mem_map] at hq
      obtain ⟨i, hi, st, hst, rfl⟩ := hq
      have hf : f ∈ s.fam.toList := by simp [hfm]
      have hRng := TFam.mem_range.mp hi
      obtain ⟨hbody, -, -⟩ := hfam f hf
      obtain ⟨pos, p, hp⟩ := hsites st (by simp [Summary.sites, Summary.famSites, hfm, hst])
      have hso := siteOK_of (s := s) (σd := σ) (σs := bindσ f.g i σ) (ns := f.g :: s.params)
        (fun n hn => hnames st (by simp [Summary.sites, Summary.famSites, hfm, hst]) n hn)
        (hbody st hst)
        (fun n hn => harr st (by simp [Summary.sites, Summary.famSites, hfm, hst]) n hn)
        (hrd.2 f hf i hRng st hst) (hin.2 f hf i hRng st hst)
      have h := site_desc (C.bindVal f.g i) hnm hp hso (.fam f.label st.pos [i])
      rw [← siteOf?_proc hp] at h
      exact h

/-! ## The soundness theorem -/

/-- `m` realizes the summary at `σ`: its declarations are the summary's, and its process list is
the closed-form `Summary.pairs` — each process an `assign` to the promised window reading only
promised windows. -/
def Realized (s : Summary) (σ : String → Int) (m : Design2) : Prop :=
  m.decls.toList = s.decls.map (DeclT.toDecl σ) ∧
  ∃ L : List (SiteInst × Process2), L.map Prod.fst = s.insts σ ∧
    m.processes.toList = L.map Prod.snd ∧ ∀ q ∈ L, Desc s.declNames q.1 q.2

/-- **`Summary.sound`: the family summary is sound against `PDesign.instantiate2`.** -/
theorem Summary.sound {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) :
    ∃ m, d.instantiate2 args (PDesign.surfaceFuel args) = .ok m ∧ Realized s σ m := by
  obtain ⟨hloc, hens, hoth, hpar, hsd, hsts, hgen⟩ := summary_spec hs
  have hok' := hok
  obtain ⟨hnodup, hnames, hinput, hstat, hfam, hdecl, harr⟩ := hok'
  have hagd : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n) :=
    fun dt hdt n hn => hag n (hdecl dt hdt n hn)
  have h2 := buildDecls_summary (σ := σ) d.decls s.decls hsd env hagd
  have h3 := buildElems_summary (σ := σ) d.decls s.decls hsd env hagd
  have hdim := paramEnv2_dims h1
  have C := ctx_of_env hsd hdim hag hdecl
  obtain ⟨hproc, hsites0⟩ := sitesOf?_spec hsts
  -- the sites of the family body
  have hsites : ∀ st ∈ s.sites, ∃ pos p, siteOf? pos p = .ok st := by
    intro st hst
    simp only [Summary.sites, List.mem_append] at hst
    rcases hst with hst | hst
    · exact hsites0 st hst
    · cases hfm : s.fam with
      | none => simp [Summary.famSites, hfm] at hst
      | some f =>
        rcases hgen with ⟨-, hnone⟩ | ⟨it, f', hgi, hfo, hsf⟩
        · rw [hfm] at hnone; cases hnone
        · rw [hfm] at hsf
          cases hsf
          obtain ⟨lbl, rc, bnd, ps, hit, hb, hss⟩ := famOf?_spec hfo
          exact (sitesOf?_spec hss).2 st (by simpa [Summary.famSites, hfm] using hst)
  have hrd := hauto
  have hpd := pairs_desc C hok
    ⟨hauto.1, fun f hf i hRng st hst r hr => (hauto.2 f hf).1 i hRng st hst r hr⟩ hin hsites
  rcases hgen with ⟨hg, hnone⟩ | ⟨it, f, hg, hfo, hfm⟩
  · -- no generate item
    have h4 : expandList2 ((env).withDecls (s.decls.map (DeclT.toDecl σ)))
        (s.decls.map fun dt => (dt.name, 1)) (PDesign.surfaceFuel args) d.generates = .ok [] := by
      rw [hg]; exact expandList2_nil
    refine ⟨_, PDesign.instantiate2_of_ok harity h1 h2 h3 h4, ?_⟩
    refine ⟨by simp, s.pairs σ _ _, Summary.pairs_map_fst .., ?_, hpd⟩
    rw [PDesign.assemble2_processes, hoth, ← hproc]
    simp [Summary.pairs, hnone, List.map_map, Function.comp_def]
  · -- one generate-for
    obtain ⟨lbl, rc, bnd, ps, hit, hb, hss⟩ := famOf?_spec hfo
    obtain ⟨hbody, -⟩ := sitesOf?_spec hss
    obtain ⟨hfbody, hfbound, hfc0⟩ := hfam f (by simp [hfm])
    have hbag : ∀ i : Int, ∀ n ∈ f.bound.names,
        ((env.withDecls (s.decls.map (DeclT.toDecl σ))).bindVal f.g i).vals.lookup n = some (σ n) := by
      intro i n hn
      obtain ⟨hnp, hng⟩ := hfbound n hn
      have hb' : (n == f.g) = false := beq_eq_false_iff_ne.2 hng
      simp only [IEnv.bindVal, List.lookup, hb']
      exact hag n hnp
    have hei : ∀ i : Int, bnd.isInt
        ((env.withDecls (s.decls.map (DeclT.toDecl σ))).bindVal f.g i) = true :=
      fun i => (affOf?_sound bnd f.bound hb (hbag i)).1
    have he : ∀ i : Int, evalInt
        ((env.withDecls (s.decls.map (DeclT.toDecl σ))).bindVal f.g i) bnd =
        .ok (f.bound.eval σ) :=
      fun i => (affOf?_sound bnd f.bound hb (hbag i)).2
    have hfuel := (hauto.2 f (by simp [hfm])).2
    have hF : (f.bound.eval σ - f.c0).toNat < PDesign.surfaceFuel args :=
      surfaceFuel_gt args _ hfuel
    have hexp := GenItem.expand2_genFor_ascending_processes
      (env := (env.withDecls (s.decls.map (DeclT.toDecl σ))))
      (elems := (s.decls.map fun dt => (dt.name, 1))) (F := PDesign.surfaceFuel args)
      (label := lbl) (g := f.g) (initE := .int f.c0) (e := bnd) (rc := rc) (ps := ps)
      (i0 := f.c0) (N := f.bound.eval σ) (evalInt_int f.c0) hei he hF
    have h4 : expandList2 ((env).withDecls (s.decls.map (DeclT.toDecl σ)))
        (s.decls.map fun dt => (dt.name, 1)) (PDesign.surfaceFuel args) d.generates =
        .ok ((intRange f.c0 (f.bound.eval σ - f.c0).toNat).flatMap fun v =>
          ps.map (instProcess2 ((env.withDecls (s.decls.map (DeclT.toDecl σ))).bindVal f.g v)
            (s.decls.map fun dt => (dt.name, 1)))) := by
      rw [hg, hit]
      exact expandList2_singleton_ok hexp
    refine ⟨_, PDesign.instantiate2_of_ok harity h1 h2 h3 h4, ?_⟩
    refine ⟨by simp, s.pairs σ _ _, Summary.pairs_map_fst .., ?_, hpd⟩
    rw [PDesign.assemble2_processes, hoth, ← hproc, ← hbody]
    simp [Summary.pairs, hfm, List.map_append, List.map_flatMap, List.map_map,
      Function.comp_def, TFam.range]

end CombView
end LeanModels.Sv
