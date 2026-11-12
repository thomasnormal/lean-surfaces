import LeanModels.Sv.CombViewThm

/-!
# `sv_structure`, stage 3: the soundness theorem against `instantiate2`

* `summary_spec` and friends: what a successful `PDesign.summary` says about the envelope
  (the generate tree IS the envelope's, every site was recognized from a process);
* the declaration stage (`ctx_of_env`) and the access geometry (`accGeom_of`: the player-facing
  `InR` facts give the `Ctx`-level geometry the site lemmas read);
* `mem_enum_E` (membership in the closed-form list), the expansion of the generate tree
  (`fams_expand2`: `GenItem.expand2` of each loop IS `TFam.enum`) and `pairs_desc`;
* `Summary.sound` — THE SOUNDNESS THEOREM. If `PDesign.summary d = .ok s`, the parameter stage
  succeeded with an environment `σ` agrees with, and the structural/auto/in-range obligations hold,
  then `d.instantiate2 args` succeeds with a design `m` that REALIZES the summary:
  `m.decls = s.decls.map toDecl`, and `m.processes` is the closed-form `Summary.pairs` (module-level
  sites, then each generate loop, no `N`-length enumeration), each process an `assign` to exactly the
  promised window reading only promised windows.
-/

namespace LeanModels.Sv
namespace CombView


theorem sitesOfG_spec (so : List DeclT → Nat → PProcess → Except String TSite)
    (hso : ∀ ds pos p st, so ds pos p = .ok st → st.proc = p) {ds : List DeclT} {tag : String} :
    ∀ {ps : List PProcess} {pos : Nat} {sts : List TSite},
    sitesOfG so ds tag pos ps = .ok sts →
      sts.map TSite.proc = ps ∧ ∀ st ∈ sts, ∃ pos' p, so ds pos' p = .ok st
  | [], pos, sts, h => by
      simp only [sitesOfG, Except.ok.injEq] at h
      subst h
      simp
  | p :: ps, pos, sts, h => by
      simp only [sitesOfG] at h
      rcases hs : so ds pos p with e | st
      · simp [hs] at h
      · rcases hr : sitesOfG so ds tag (pos + 1) ps with e | sts'
        · simp [hs, hr] at h
        · simp only [hs, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨h1, h2⟩ := sitesOfG_spec so hso hr
          refine ⟨?_, ?_⟩
          · simp [h1, hso _ _ _ _ hs]
          · intro st' hst'
            rcases List.mem_cons.mp hst' with rfl | hm
            · exact ⟨pos, p, hs⟩
            · exact h2 st' hm

/-- The sites an item holds. -/
def TItem.stList : TItem → List TSite
  | .site st => [st]
  | .loop l => l.body

theorem itemOfG_spec (so : List DeclT → Nat → PProcess → Except String TSite)
    (hso : ∀ ds pos p st, so ds pos p = .ok st → st.proc = p) {ds : List DeclT} {tag : String} {pos : Nat} {it : GenItem} {x : TItem}
    (h : itemOfG so ds tag pos it = .ok x) :
    x.toGen = it ∧ x.Wf ∧ ∀ st ∈ x.stList, ∃ pos' p, so ds pos' p = .ok st := by
  cases it with
  | process p =>
      simp only [itemOfG] at h
      rcases hs : so ds pos p with e | st
      · simp [hs] at h
      · simp only [hs, Except.ok.injEq] at h
        subst h
        refine ⟨?_, trivial, ?_⟩
        · simp [TItem.toGen, hso _ _ _ _ hs]
        · intro st' hst'
          simp only [TItem.stList, List.mem_singleton] at hst'
          subst hst'
          exact ⟨pos, p, hs⟩
  | genFor label g initE bound step rc body =>
      simp only [itemOfG] at h
      rcases hh : hdrOf? label g initE bound step with e | h0
      · simp [hh] at h
      · rcases hp : procsOf? body with _ | ps
        · simp [hh, hp] at h
        · rcases hsx : sitesOfG so ds h0.name 0 ps with e | sts
          · simp [hh, hp, hsx] at h
          · simp only [hh, hp, hsx, Except.ok.injEq] at h
            subst h
            obtain ⟨hl, hg, hwf, hi, hb, hst⟩ := hdrOf?_spec hh
            obtain ⟨hmap, hsites⟩ := sitesOfG_spec so hso hsx
            refine ⟨?_, hwf, hsites⟩
            have hbody : (sts.map fun st => GenItem.process st.proc) = body := by
              rw [procsOf?_eq hp, ← hmap, List.map_map]; rfl
            simp only [TItem.toGen, Hdr.gen]
            rw [← hi, ← hb, ← hst, hl, hg, hbody]
  | genIf c t e => simp [itemOfG] at h
  | inst i => simp [itemOfG] at h
  | unsupported k t => simp [itemOfG] at h

theorem itemsOfG_spec (so : List DeclT → Nat → PProcess → Except String TSite)
    (hso : ∀ ds pos p st, so ds pos p = .ok st → st.proc = p) {ds : List DeclT} {tag : String} :
    ∀ {pos : Nat} {items : List GenItem} {its : List TItem}, itemsOfG so ds tag pos items = .ok its →
      its.map TItem.toGen = items ∧ ∀ x ∈ its, x.Wf ∧
        ∀ st ∈ x.stList, ∃ pos' p, so ds pos' p = .ok st
  | pos, [], its, h => by
      simp only [itemsOfG, Except.ok.injEq] at h
      subst h
      simp
  | pos, it :: rest, its, h => by
      simp only [itemsOfG] at h
      rcases hx : itemOfG so ds tag pos it with e | x
      · simp [hx] at h
      · rcases hr : itemsOfG so ds tag (pos + 1) rest with e | xs
        · simp [hx, hr] at h
        · simp only [hx, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨h1, h2, h3⟩ := itemOfG_spec so hso hx
          obtain ⟨k1, k2⟩ := itemsOfG_spec so hso hr
          refine ⟨by simp [h1, k1], ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hm
          · exact ⟨h2, h3⟩
          · exact k2 y hm

theorem famOfG_spec (so : List DeclT → Nat → PProcess → Except String TSite)
    (hso : ∀ ds pos p st, so ds pos p = .ok st → st.proc = p) {ds : List DeclT} {it : GenItem} {f : TFam} (h : famOfG so ds it = .ok f) :
    f.toGen = it ∧ f.Wf ∧ ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos' p, so ds pos' p = .ok st := by
  cases it with
  | genFor label g initE bound step rc body =>
      simp only [famOfG] at h
      rcases hh : hdrOf? label g initE bound step with e | h0
      · simp [hh] at h
      · rcases hit : itemsOfG so ds h0.name 0 body with e | its
        · simp [hh, hit] at h
        · simp only [hh, hit, Except.ok.injEq] at h
          subst h
          obtain ⟨hl, hg, hwf, hi, hb, hst⟩ := hdrOf?_spec hh
          obtain ⟨k1, k2⟩ := itemsOfG_spec so hso hit
          refine ⟨?_, ⟨hwf, fun x hx => (k2 x hx).1⟩, fun x hx => (k2 x hx).2⟩
          simp only [TFam.toGen, Hdr.gen]
          rw [← hi, ← hb, ← hst, hl, hg, k1]
  | process p => simp [famOfG] at h
  | genIf c t e => simp [famOfG] at h
  | inst i => simp [famOfG] at h
  | unsupported k t => simp [famOfG] at h

/-- The generate tree of a recognized design: every loop is the envelope's, with recognized
bounds, and every site was recognized from a process. -/
def Summary.SpecOkG (s : Summary) (so : List DeclT → Nat → PProcess → Except String TSite) : Prop :=
  ∀ f ∈ s.fams, f.Wf ∧ ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos p, so s.decls pos p = .ok st

def Summary.SpecOk (s : Summary) : Prop := s.SpecOkG siteOf?

theorem famsOfG_spec (so : List DeclT → Nat → PProcess → Except String TSite)
    (hso : ∀ ds pos p st, so ds pos p = .ok st → st.proc = p) {ds : List DeclT} :
    ∀ {gens : List GenItem} {fs : List TFam}, famsOfG so ds gens = .ok fs →
      fs.map TFam.toGen = gens ∧ ∀ f ∈ fs, f.Wf ∧
        ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos' p, so ds pos' p = .ok st
  | [], fs, h => by
      simp only [famsOfG, Except.ok.injEq] at h
      subst h
      simp
  | it :: rest, fs, h => by
      simp only [famsOfG] at h
      rcases hf : famOfG so ds it with e | f
      · simp [hf] at h
      · rcases hr : famsOfG so ds rest with e | fs'
        · simp [hf, hr] at h
        · simp only [hf, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨h1, h2, h3⟩ := famOfG_spec so hso hf
          obtain ⟨k1, k2⟩ := famsOfG_spec so hso hr
          refine ⟨by simp [h1, k1], ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hm
          · exact ⟨h2, h3⟩
          · exact k2 y hm


/-! ### The `siteOf?` instances (the old names and statements) -/

theorem siteOf?_proc' : ∀ (ds : List DeclT) (pos : Nat) (p : PProcess) (st : TSite),
    siteOf? ds pos p = .ok st → st.proc = p := fun _ _ _ _ h => siteOf?_proc h

theorem sitesOf?_spec {ds : List DeclT} {tag : String} :
    ∀ {ps : List PProcess} {pos : Nat} {sts : List TSite},
    sitesOf? ds tag pos ps = .ok sts →
      sts.map TSite.proc = ps ∧ ∀ st ∈ sts, ∃ pos' p, siteOf? ds pos' p = .ok st :=
  fun h => sitesOfG_spec siteOf? siteOf?_proc' h

theorem itemOf?_spec {ds : List DeclT} {tag : String} {pos : Nat} {it : GenItem} {x : TItem}
    (h : itemOf? ds tag pos it = .ok x) :
    x.toGen = it ∧ x.Wf ∧ ∀ st ∈ x.stList, ∃ pos' p, siteOf? ds pos' p = .ok st :=
  itemOfG_spec siteOf? siteOf?_proc' h

theorem itemsOf?_spec {ds : List DeclT} {tag : String} :
    ∀ {pos : Nat} {items : List GenItem} {its : List TItem}, itemsOf? ds tag pos items = .ok its →
      its.map TItem.toGen = items ∧ ∀ x ∈ its, x.Wf ∧
        ∀ st ∈ x.stList, ∃ pos' p, siteOf? ds pos' p = .ok st :=
  fun h => itemsOfG_spec siteOf? siteOf?_proc' h

theorem famOf?_spec {ds : List DeclT} {it : GenItem} {f : TFam} (h : famOf? ds it = .ok f) :
    f.toGen = it ∧ f.Wf ∧ ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos' p, siteOf? ds pos' p = .ok st :=
  famOfG_spec siteOf? siteOf?_proc' h

theorem famsOf?_spec {ds : List DeclT} :
    ∀ {gens : List GenItem} {fs : List TFam}, famsOf? ds gens = .ok fs →
      fs.map TFam.toGen = gens ∧ ∀ f ∈ fs, f.Wf ∧
        ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos' p, siteOf? ds pos' p = .ok st :=
  fun h => famsOfG_spec siteOf? siteOf?_proc' h

theorem lpsOf?_names : ∀ {scope : List String} {lps : List PLocalParam} {cs : List (String × CE)},
    lpsOf? scope lps = .ok cs → cs.map Prod.fst = lps.map (·.name)
  | _, [], cs, h => by
      simp only [lpsOf?, Except.ok.injEq] at h
      subst h
      rfl
  | scope, lp :: rest, cs, h => by
      simp only [lpsOf?] at h
      rcases hl : lpOf? scope lp with e | c
      · simp [hl] at h
      · rcases hr : lpsOf? (scope ++ [lp.name]) rest with e | cs'
        · simp [hl, hr] at h
        · simp only [hl, hr, Except.ok.injEq] at h
          subst h
          simp [lpsOf?_names hr]

theorem summaryG_spec (so : List DeclT → Nat → PProcess → Except String TSite)
    (hso : ∀ ds pos p st, so ds pos p = .ok st → st.proc = p) {d : PDesign} {s : Summary}
    (h : d.summaryG so = .ok s) :
    s.lps.map Prod.fst = d.localParams.map (·.name) ∧ d.enums = [] ∧ d.others = [] ∧
    s.params = d.params.map (·.name) ++ s.lps.map Prod.fst ∧
    declsOf? d.decls = .ok s.decls ∧ sitesOfG so s.decls "plain" 0 d.processes = .ok s.statics ∧
    d.generates = s.fams.map TFam.toGen ∧ s.SpecOkG so := by
  unfold PDesign.summaryG at h
  rcases hl : lpsOf? (d.params.map (·.name)) d.localParams with e | lps
  · simp [hl] at h
  simp only [hl] at h
  split at h
  · simp at h
  rename_i h2
  split at h
  · simp at h
  rename_i h3
  have he : d.enums = [] := by simpa using h2
  have ho : d.others = [] := by simpa using h3
  rcases hd : declsOf? d.decls with e | ds
  · simp [hd] at h
  rcases hp : sitesOfG so ds "plain" 0 d.processes with e | sts
  · simp [hd, hp] at h
  rcases hg : famsOfG so ds d.generates with e | fs
  · simp [hd, hp, hg] at h
  simp only [hd, hp, hg, Except.ok.injEq] at h
  subst h
  obtain ⟨k1, k2⟩ := famsOfG_spec so hso hg
  have hnames : lps.map Prod.fst = d.localParams.map (·.name) := lpsOf?_names hl
  exact ⟨hnames, he, ho, rfl, rfl, hp, k1.symm, k2⟩

theorem summary_spec {d : PDesign} {s : Summary} (h : d.summary = .ok s) :
    s.lps.map Prod.fst = d.localParams.map (·.name) ∧ d.enums = [] ∧ d.others = [] ∧
    s.params = d.params.map (·.name) ++ s.lps.map Prod.fst ∧
    declsOf? d.decls = .ok s.decls ∧ sitesOf? s.decls "plain" 0 d.processes = .ok s.statics ∧
    d.generates = s.fams.map TFam.toGen ∧ s.SpecOk :=
  summaryG_spec siteOf? siteOf?_proc' h

theorem surfaceFuel_gt (args : List Int) (x : Nat) (hx : x ≤ 4 * (args.map Int.natAbs).sum + 60) :
    x < PDesign.surfaceFuel args := by
  show x < ((args.map Int.natAbs).sum + 2) * ((args.map Int.natAbs).sum + 2) + 64
  have h : ((args.map Int.natAbs).sum + 2) * ((args.map Int.natAbs).sum + 2) =
      (args.map Int.natAbs).sum * (args.map Int.natAbs).sum + 4 * (args.map Int.natAbs).sum + 4 := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  omega

/-- The environment `paramEnv2` produces: some declaration scope `env2` with its dimension table, and the design's
function declarations (`functions`, which no comb theorem reads). -/
theorem paramEnv2_dims {d : PDesign} {args : List Int} {env : IEnv}
    (h : d.paramEnv2 args = .ok env) :
    ∃ (env2 : IEnv) (fs : List PFunction), env = { env2 with dims := dimTable env2 d.decls, functions := fs } := by
  unfold PDesign.paramEnv2 at h
  simp only [Res.bind_eq_ok] at h
  obtain ⟨_, -, _, -, e0, -, e1, -, e2, -, pws, -, hfin⟩ := h
  exact ⟨{ e2 with pwidths := pws }, d.functions, (Res.ok.inj hfin).symm⟩

theorem dimsOf'_some {s : Summary} {n : String} {dims : List (Aff × Aff)}
    (h : s.dimsOf' n = some dims) :
    ∃ dt, s.find n = some dt ∧ dt ∈ s.decls ∧ dt.dims.map (fun p => (p.2.1, p.2.2)) = dims := by
  unfold Summary.dimsOf' dimsOf at h
  rcases hf : findDecl s.decls n with _ | dt
  · simp [hf] at h
  · simp only [hf, Option.map_some, Option.some.injEq] at h
    refine ⟨dt, ?_, ?_, h⟩
    · unfold Summary.find; exact hf
    · unfold findDecl at hf; exact List.mem_of_find?_eq_some hf

theorem dims0_of {s : Summary} {n : String} (h : s.dimsOf' n = some []) :
    ∃ dt, s.find n = some dt ∧ dt.dims = [] := by
  obtain ⟨dt, hf, -, hd⟩ := dimsOf'_some h
  refine ⟨dt, hf, ?_⟩
  rcases hdd : dt.dims with _ | ⟨p, rest⟩
  · rfl
  · simp [hdd] at hd

theorem dims1_of {s : Summary} {n : String} {M L : Aff} (h : s.dimsOf' n = some [(M, L)]) :
    ∃ dt d, s.find n = some dt ∧ dt ∈ s.decls ∧ dt.dims = [(d, M, L)] := by
  obtain ⟨dt, hf, hm, hd⟩ := dimsOf'_some h
  rcases hdd : dt.dims with _ | ⟨⟨d, M', L'⟩, _ | ⟨q, rest⟩⟩
  · simp [hdd] at hd
  · simp only [hdd, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hd
    obtain ⟨h1, h2⟩ := hd
    subst h1 h2
    exact ⟨dt, d, hf, hm, hdd⟩
  · simp [hdd] at hd

theorem dims2_of {s : Summary} {n : String} {M1 L1 M2 L2 : Aff}
    (h : s.dimsOf' n = some [(M1, L1), (M2, L2)]) :
    ∃ dt d1 d2, s.find n = some dt ∧ dt ∈ s.decls ∧ dt.dims = [(d1, M1, L1), (d2, M2, L2)] := by
  obtain ⟨dt, hf, hm, hd⟩ := dimsOf'_some h
  rcases hdd : dt.dims with _ | ⟨⟨d1, M1', L1'⟩, _ | ⟨⟨d2, M2', L2'⟩, _ | ⟨q, rest⟩⟩⟩
  · simp [hdd] at hd
  · simp [hdd] at hd
  · simp only [hdd, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hd
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hd
    subst h1 h2 h3 h4
    exact ⟨dt, d1, d2, hf, hm, hdd⟩
  · simp [hdd] at hd


/-- Parameters are not rebound by the loops. -/
theorem Reach_params : ∀ {hs : List Hdr} {σ σ' : String → Int}, Reach hs σ σ' →
    ∀ {ps : List String}, (∀ h ∈ hs, h.g ∉ ps) → ∀ n ∈ ps, σ' n = σ n
  | [], σ, σ', h, ps, _, n, hn => by
      have h' : σ' = σ := h
      subst h'; rfl
  | h :: hs, σ, σ', ⟨i, hi, hr⟩, ps, hnot, n, hn => by
      rw [Reach_params hr (fun h' hh' => hnot h' (List.mem_cons_of_mem _ hh')) n hn]
      exact bindσ_ne (fun heq => hnot h (List.mem_cons_self ..) (by rw [← heq]; exact hn)) i σ

theorem aff_eval_eq {s : Summary} {σd σs : String → Int} (hpar : ∀ n ∈ s.params, σs n = σd n)
    {a : Aff} (h : ∀ n ∈ a.names, n ∈ s.params) : a.eval σs = a.eval σd :=
  Aff.eval_congr σs σd a (fun n hn => hpar n (h n hn))

/-- The facts for a 1-D declaration `[M:0]`. -/
theorem decl1_facts {s : Summary} {σd : String → Int} {n : String} {M L : Aff}
    (hdecl : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, n ∈ s.params)
    (h : s.dimsOf' n = some [(M, L)]) (hL : L = Aff.const 0) :
    s.DG σd n = some [(M.eval σd, 0)] ∧ s.dm σd n 0 = M.eval σd ∧
      s.dw σd n = (M.eval σd).natAbs + 1 ∧ (∀ x ∈ M.names, x ∈ s.params) := by
  obtain ⟨dt, d, hf, hm, hdt⟩ := dims1_of h
  subst hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Summary.DG, hf, DeclT.vals, hdt, Aff.eval_const]
  · simp [Summary.dm, hf, hdt]
  · simp [Summary.dw, hf, DeclT.width, hdt, dimsW, Aff.eval_const]
  · intro x hx
    exact hdecl dt hm x (by simp [DeclT.affNames, hdt, hx])

/-- The facts for a 2-D declaration `[M1:0][M2:0]`. -/
theorem decl2_facts {s : Summary} {σd : String → Int} {n : String} {M1 L1 M2 L2 : Aff}
    (hdecl : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, n ∈ s.params)
    (h : s.dimsOf' n = some [(M1, L1), (M2, L2)]) (hL1 : L1 = Aff.const 0)
    (hL2 : L2 = Aff.const 0) :
    s.DG σd n = some [(M1.eval σd, 0), (M2.eval σd, 0)] ∧ s.dm σd n 0 = M1.eval σd ∧
      s.dm σd n 1 = M2.eval σd ∧
      s.dw σd n = ((M1.eval σd).natAbs + 1) * ((M2.eval σd).natAbs + 1) ∧
      (∀ x ∈ M2.names, x ∈ s.params) := by
  obtain ⟨dt, d1, d2, hf, hm, hdt⟩ := dims2_of h
  subst hL1 hL2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Summary.DG, hf, DeclT.vals, hdt, Aff.eval_const]
  · simp [Summary.dm, hf, hdt]
  · simp [Summary.dm, hf, hdt]
  · simp [Summary.dw, hf, DeclT.width, hdt, dimsW, Aff.eval_const]
  · intro x hx
    exact hdecl dt hm x (by simp [DeclT.affNames, hdt, hx])

theorem bit_elemW {s : Summary} {σd : String → Int} {n : String}
    (hok : (match s.dimsOf' n with | some [] => true | some [_] => true | _ => false) = true) :
    s.EW σd n = some 1 := by
  rcases hdn : s.dimsOf' n with _ | dims
  · simp [hdn] at hok
  · rcases dims with _ | ⟨p, _ | ⟨q, rest⟩⟩
    · obtain ⟨dt, hf, hdt⟩ := dims0_of hdn
      simp [Summary.EW, hf, DeclT.elemW, hdt]
    · obtain ⟨M, L⟩ := p
      obtain ⟨dt, d, hf, -, hdt⟩ := dims1_of hdn
      simp [Summary.EW, hf, DeclT.elemW, hdt]
    · simp [hdn] at hok


/-- The player-facing in-range facts give the `Ctx`-level geometry of an access. -/
theorem accGeom_of {s : Summary} {σd σs : String → Int}
    (hpar : ∀ n ∈ s.params, σs n = σd n)
    (hdecl : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, n ∈ s.params)
    {a : Acc} (hok : s.accOk a = true) (hr : s.InR σd σs a) (hd : s.DimNum σd a) :
    AccGeom σs (s.DG σd) (s.EW σd) a := by
  cases a with
  | whole n => trivial
  | bit n x =>
      exact ⟨hr, bit_elemW hok⟩
  | cell1 n x =>
      simp only [Summary.accOk] at hok
      rcases hdn : s.dimsOf' n with _ | dims
      · simp [hdn] at hok
      · rcases dims with _ | ⟨⟨M, L⟩, _ | ⟨q, rest⟩⟩
        · simp [hdn] at hok
        · simp only [hdn, decide_eq_true_eq] at hok
          obtain ⟨hG, hdm, -, -⟩ := decl1_facts (σd := σd) hdecl hdn hok
          simp only [Summary.InR, hdm] at hr
          exact ⟨M.eval σd, hG, hr.1, hr.2⟩
        · simp [hdn] at hok
  | row n w r =>
      simp only [Summary.accOk] at hok
      rcases hdn : s.dimsOf' n with _ | dims
      · simp [hdn] at hok
      · rcases dims with _ | ⟨⟨M1, L1⟩, _ | ⟨⟨M2, L2⟩, _ | ⟨q, rest⟩⟩⟩
        · simp [hdn] at hok
        · simp [hdn] at hok
        · simp only [hdn, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨hL1, hL2⟩, hw⟩ := hok
          obtain ⟨hG, hdm0, hdm1, -, hM2⟩ := decl2_facts (σd := σd) hdecl hdn hL1 hL2
          simp only [Summary.InR, hdm0] at hr
          simp only [Summary.DimNum, hdm1] at hd
          refine ⟨M1.eval σd, M2.eval σd, hG, hd, ?_, hr.1, hr.2⟩
          rw [hw, Aff.eval_add, Aff.eval_const, aff_eval_eq hpar hM2]
        · simp [hdn] at hok
  | cell2 n w r c =>
      simp only [Summary.accOk] at hok
      rcases hdn : s.dimsOf' n with _ | dims
      · simp [hdn] at hok
      · rcases dims with _ | ⟨⟨M1, L1⟩, _ | ⟨⟨M2, L2⟩, _ | ⟨q, rest⟩⟩⟩
        · simp [hdn] at hok
        · simp [hdn] at hok
        · simp only [hdn, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨hL1, hL2⟩, hw⟩ := hok
          obtain ⟨hG, hdm0, hdm1, -, hM2⟩ := decl2_facts (σd := σd) hdecl hdn hL1 hL2
          simp only [Summary.InR, hdm0, hdm1] at hr
          refine ⟨M1.eval σd, M2.eval σd, hG, ?_, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩
          rw [hw, Aff.eval_add, Aff.eval_const, aff_eval_eq hpar hM2]
        · simp [hdn] at hok
  | part1 n hi lo =>
      simp only [Summary.accOk] at hok
      rcases hdn : s.dimsOf' n with _ | dims
      · simp [hdn] at hok
      · rcases dims with _ | ⟨⟨M, L⟩, _ | ⟨q, rest⟩⟩
        · simp [hdn] at hok
        · simp only [hdn, decide_eq_true_eq] at hok
          obtain ⟨hG, hdm, -, -⟩ := decl1_facts (σd := σd) hdecl hdn hok
          simp only [Summary.InR, hdm] at hr
          exact ⟨M.eval σd, hG, hr.1, hr.2.1, hr.2.2⟩
        · simp [hdn] at hok
  | part2 n w r hi lo =>
      simp only [Summary.accOk] at hok
      rcases hdn : s.dimsOf' n with _ | dims
      · simp [hdn] at hok
      · rcases dims with _ | ⟨⟨M1, L1⟩, _ | ⟨⟨M2, L2⟩, _ | ⟨q, rest⟩⟩⟩
        · simp [hdn] at hok
        · simp [hdn] at hok
        · simp only [hdn, Bool.and_eq_true, decide_eq_true_eq] at hok
          obtain ⟨⟨hL1, hL2⟩, hw⟩ := hok
          obtain ⟨hG, hdm0, hdm1, -, hM2⟩ := decl2_facts (σd := σd) hdecl hdn hL1 hL2
          simp only [Summary.InR, hdm0, hdm1] at hr
          refine ⟨M1.eval σd, M2.eval σd, hG, ?_, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2⟩
          rw [hw, Aff.eval_add, Aff.eval_const, aff_eval_eq hpar hM2]
        · simp [hdn] at hok


/-! ## The declaration stage -/

@[simp] theorem toDecl_name (σ : String → Int) (dt : DeclT) : (dt.toDecl σ).name = dt.name := rfl
@[simp] theorem toDecl_width (σ : String → Int) (dt : DeclT) :
    (dt.toDecl σ).width = dt.width σ := rfl
@[simp] theorem toDecl_isInput (σ : String → Int) (dt : DeclT) :
    (dt.toDecl σ).isInput = dt.isInput := rfl
@[simp] theorem toDecl_init (σ : String → Int) (dt : DeclT) : (dt.toDecl σ).init = none := rfl

theorem dimsW_pos (σ : String → Int) : ∀ (dims : List (PDim × Aff × Aff)), 0 < dimsW σ dims
  | [] => by simp [dimsW]
  | (_, m, l) :: rest => by
      simp only [dimsW]
      exact Nat.mul_pos (Nat.succ_pos _) (dimsW_pos σ rest)

theorem DeclT.width_pos (σ : String → Int) (dt : DeclT) : 0 < dt.width σ := dimsW_pos σ dt.dims

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

theorem lookup_elemW (σ : String → Int) :
    ∀ (sd : List DeclT) (n : String),
      (sd.map fun dt => (dt.name, dt.elemW σ)).lookup n =
        (sd.find? fun dt => dt.name == n).map (DeclT.elemW σ)
  | [], n => by simp
  | dt :: rest, n => by
      by_cases h : n = dt.name
      · have h1 : (n == dt.name) = true := beq_iff_eq.2 h
        have h2 : (dt.name == n) = true := beq_iff_eq.2 h.symm
        simp [List.lookup, h1, h2]
      · have h1 : (n == dt.name) = false := beq_eq_false_iff_ne.2 h
        have h2 : (dt.name == n) = false := beq_eq_false_iff_ne.2 (Ne.symm h)
        simp [List.lookup, h1, h2, lookup_elemW σ rest n]

theorem find_isSome_of_mem {s : Summary} {n : String} (h : n ∈ s.declNames) :
    (s.find n).isSome = true := by
  unfold Summary.find findDecl
  rw [List.find?_isSome]
  simp only [Summary.declNames, List.mem_map] at h
  obtain ⟨dt, hdt, rfl⟩ := h
  exact ⟨dt, hdt, by simp⟩

theorem mem_declNames_of_find {s : Summary} {n : String} (h : (s.find n).isSome = true) :
    n ∈ s.declNames := by
  unfold Summary.find findDecl at h
  rw [List.find?_isSome] at h
  obtain ⟨dt, hdt, hn⟩ := h
  simp only [Summary.declNames, List.mem_map]
  exact ⟨dt, hdt, by simpa using hn⟩

/-- The environment facts of the instantiation, from the declaration stage. -/
theorem ctx_of_env {s : Summary} {d : PDesign} (hsd : declsOf? d.decls = .ok s.decls)
    {σ : String → Int} {env : IEnv}
    (hdim : ∃ (env2 : IEnv) (fs : List PFunction), env = { env2 with dims := dimTable env2 d.decls, functions := fs })
    (hag : Agrees σ env s.params)
    (hdecl : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, n ∈ s.params) :
    Ctx σ (env.withDecls (s.decls.map (DeclT.toDecl σ))) (s.decls.map fun dt => (dt.name, dt.elemW σ))
      (s.DW σ) (s.DG σ) (s.EW σ) s.params := by
  obtain ⟨env2, fs, henv⟩ := hdim
  have hagd : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, env2.intVal? n = some (σ n) := by
    intro dt hdt n hn
    have := hag n (hdecl dt hdt n hn)
    rw [henv] at this
    exact this
  refine ⟨hag, ?_, ?_, ?_, ?_⟩
  · intro n
    exact lookup_widths σ s.decls n
  · intro n ds hn
    rw [lookup_elemW σ s.decls n]
    simp only [Summary.DG] at hn
    rcases hf : s.find n with _ | dt
    · simp [hf] at hn
    · have hf' : s.decls.find? (fun dt => dt.name == n) = some dt := hf
      rw [hf']
      simp only [hf, Option.map_some, Option.some.injEq] at hn
      subst hn
      simp [DeclT.elemW_vals]
  · intro n hn
    rw [lookup_elemW σ s.decls n]
    exact hn
  · intro n ds hn
    have h1 := dimTable_summary d.decls s.decls hsd env2 hagd n
    have h2 : env.dims = dimTable env2 d.decls := by rw [henv]
    show env.dims.lookup n = _
    rw [h2, h1]
    exact hn

/-! ## Membership in the closed-form list -/

theorem mem_enum_E {β : Type} (s : Summary) (b : LSite → (String → Int) → IEnv → β)
    (σ : String → Int) (E : IEnv) {x : β} :
    x ∈ s.enum b σ E ↔
      ∃ ls ∈ s.lsites, ∃ σ' E', ReachE ls.hdrs σ E σ' E' ∧ x = b ls σ' E' := by
  unfold Summary.enum Summary.lsites
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, TFam.enum, TFam.lsites, TFam.itemLs, TFam.itemEnum]
  constructor
  · rintro (⟨st, hst, rfl⟩ | ⟨f, hf, i, hi, it, hit, hx⟩)
    · exact ⟨⟨[], "plain", st⟩, Or.inl ⟨st, hst, rfl⟩, σ, E, ⟨rfl, rfl⟩, rfl⟩
    · cases it with
      | site st =>
          simp only [List.mem_singleton] at hx
          exact ⟨⟨[f.hdr], f.hdr.name, st⟩,
            Or.inr ⟨f, hf, TItem.site st, hit, by simp⟩, bindσ f.hdr.g i σ, E.bindVal f.hdr.g i,
            ⟨i, Hdr.mem_range.mp hi, rfl, rfl⟩, hx⟩
      | loop l =>
          simp only [List.mem_flatMap, List.mem_map] at hx
          obtain ⟨j, hj, st, hst, rfl⟩ := hx
          exact ⟨⟨[f.hdr, l.hdr], l.hdr.name, st⟩,
            Or.inr ⟨f, hf, TItem.loop l, hit, by simp [hst]⟩, _, _,
            ⟨i, Hdr.mem_range.mp hi, j, Hdr.mem_range.mp hj, rfl, rfl⟩, rfl⟩
  · rintro ⟨ls, hls, σ', E', hr, rfl⟩
    rcases hls with ⟨st, hst, rfl⟩ | ⟨f, hf, it, hit, hl⟩
    · obtain ⟨h1, h2⟩ := hr
      subst h1 h2
      exact Or.inl ⟨st, hst, rfl⟩
    · cases it with
      | site st =>
          simp only [List.mem_singleton] at hl
          subst hl
          obtain ⟨i, hi, h1, h2⟩ := hr
          subst h1 h2
          exact Or.inr ⟨f, hf, i, Hdr.mem_range.mpr hi, TItem.site st, hit, by simp⟩
      | loop l =>
          simp only [List.mem_map] at hl
          obtain ⟨st, hst, rfl⟩ := hl
          obtain ⟨i, hi, j, hj, h1, h2⟩ := hr
          subst h1 h2
          exact Or.inr ⟨f, hf, i, Hdr.mem_range.mpr hi, TItem.loop l, hit, by
            simp only [List.mem_flatMap, List.mem_map]
            exact ⟨j, Hdr.mem_range.mpr hj, st, hst, rfl⟩⟩

theorem mem_insts {s : Summary} {σ : String → Int} {E : IEnv} {a : SiteInst} :
    a ∈ s.insts σ E ↔ ∃ ls ∈ s.lsites, ∃ σ', Reach ls.hdrs σ σ' ∧ a = ls.inst σ' (s.dw σ) := by
  unfold Summary.insts
  rw [mem_enum_E]
  constructor
  · rintro ⟨ls, hls, σ', E', hr, rfl⟩
    exact ⟨ls, hls, σ', ReachE_Reach hr, rfl⟩
  · rintro ⟨ls, hls, σ', hr, rfl⟩
    obtain ⟨E', hE⟩ := Reach_ReachE E hr
    exact ⟨ls, hls, σ', E', hE, rfl⟩

theorem Ctx.reachE {elems : List (String × Nat)} {DW : String → Option Nat}
    {DG : String → Option (List (Int × Int))} {EW : String → Option Nat} :
    ∀ {hs : List Hdr} {σ : String → Int} {E : IEnv} {σ' : String → Int} {E' : IEnv}
      {ns ns' : List String}, Ctx σ E elems DW DG EW ns → ReachE hs σ E σ' E' →
        (∀ n, n ∈ ns' → n ∈ hs.map (·.g) ++ ns) → Ctx σ' E' elems DW DG EW ns'
  | [], σ, E, σ', E', ns, ns', C, ⟨h1, h2⟩, hsub => by
      subst h1 h2
      exact ⟨C.agree.mono (fun n hn => by simpa using hsub n hn), C.widths, C.elemsG, C.elems, C.dims⟩
  | h :: hs, σ, E, σ', E', ns, ns', C, ⟨i, hi, hr⟩, hsub =>
      Ctx.reachE (C.bindVal h.g i) hr (fun n hn => by
        have h0 := hsub n hn
        simp only [List.map_cons, List.mem_append, List.mem_cons] at h0 ⊢
        rcases h0 with (h1 | h1) | h1 <;> simp [h1])

theorem notin_of_nodup {l1 l2 : List String} (h : (l1 ++ l2).Nodup) {x : String} (hx : x ∈ l1) :
    x ∉ l2 := by
  intro hx2
  have h2 := (List.nodup_append.mp h).2.2
  exact h2 x hx x hx2 rfl

theorem lsite_hdrs {s : Summary} {ls : LSite} (h : ls ∈ s.lsites) :
    ls.hdrs = [] ∨ ls.hdrs ∈ s.hdrPaths := by
  unfold Summary.lsites at h
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, TFam.lsites] at h
  rcases h with ⟨st, hst, rfl⟩ | ⟨f, hf, it, hit, hl⟩
  · exact Or.inl rfl
  · right
    unfold Summary.hdrPaths
    simp only [List.mem_flatMap, List.mem_cons, List.mem_filterMap]
    cases it with
    | site st =>
        simp only [TFam.itemLs, List.mem_singleton] at hl
        subst hl
        exact ⟨f, hf, Or.inl rfl⟩
    | loop l =>
        simp only [TFam.itemLs, List.mem_map] at hl
        obtain ⟨st, hst, rfl⟩ := hl
        exact ⟨f, hf, Or.inr ⟨TItem.loop l, hit, rfl⟩⟩

theorem lsitesG_spec (so : List DeclT → Nat → PProcess → Except String TSite) {s : Summary}
    (hsta : ∀ st ∈ s.statics, ∃ pos p, so s.decls pos p = .ok st) (hspec : s.SpecOkG so) :
    ∀ ls ∈ s.lsites, ∃ pos p, so s.decls pos p = .ok ls.site := by
  intro ls h
  unfold Summary.lsites at h
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, TFam.lsites] at h
  rcases h with ⟨st, hst, rfl⟩ | ⟨f, hf, it, hit, hl⟩
  · exact hsta st hst
  · cases it with
    | site st =>
        simp only [TFam.itemLs, List.mem_singleton] at hl
        subst hl
        exact (hspec f hf).2 (TItem.site st) hit st (by simp [TItem.stList])
    | loop l =>
        simp only [TFam.itemLs, List.mem_map] at hl
        obtain ⟨st, hst, rfl⟩ := hl
        exact (hspec f hf).2 (TItem.loop l) hit st (by simpa [TItem.stList] using hst)

theorem lsites_spec {s : Summary}
    (hsta : ∀ st ∈ s.statics, ∃ pos p, siteOf? s.decls pos p = .ok st) (hspec : s.SpecOk) :
    ∀ ls ∈ s.lsites, ∃ pos p, siteOf? s.decls pos p = .ok ls.site :=
  lsitesG_spec siteOf? hsta hspec

/-! ## One located site -/

/-- The processes a located site contributes: `instProcess2` at the reached environment. -/
def procB (elems : List (String × Nat)) : LSite → (String → Int) → IEnv → Process2 :=
  fun ls _ E' => instProcess2 E' elems ls.site.proc

/-- Everything the per-site proofs read at one located site `ls`, reached at the valuation `σ'` and the
environment `E'`: the context of the reached environment, the declared names, the parameters kept by the reached
valuation, the reach itself, the in-range facts of the site (the head window and the further ones), and the
accessors' `AccOK` (targets, then reads). -/
structure SiteCtx (s : Summary) (σ : String → Int) (elems : List (String × Nat)) (ls : LSite)
    (σ' : String → Int) (E' : IEnv) : Prop where
  ctx : Ctx σ' E' elems (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params)
  nm : ∀ n, (s.DW σ n).isSome = true → n ∈ s.declNames
  par : ∀ n ∈ s.params, σ' n = σ n
  reach : Reach ls.hdrs σ σ'
  inw : s.InWin σ σ' ls.site
  inwMore : ∀ a ∈ ls.site.more, s.InWinAcc σ σ' a
  so : ∀ a ∈ ls.site.tgt :: (ls.site.more ++ ls.site.rds),
    AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) a
  /-- WP-B2 gates 4b and 4c (`R`): the constants of the instance the site's right-hand side mentions are in scope,
  and the counts of its replications are non-negative at this instance. -/
  cn : ls.site.ConstOK σ' (ls.hdrs.map (·.g) ++ s.params)

/-- The constants of the instance a located site's right-hand side mentions are parameters or enclosing loop variables
(the fourth conjunct of `StructOk`, over `TSite.affNames`, which lists them). -/
theorem site_cn {s : Summary} (hok : s.StructOk) {ls : LSite} (hls : ls ∈ s.lsites) :
    ∀ n ∈ ls.site.cnames, n ∈ ls.hdrs.map (·.g) ++ s.params := by
  obtain ⟨-, -, -, haff, -⟩ := hok
  intro n hn
  exact haff ls hls n (by simp only [TSite.affNames, List.mem_append]; exact Or.inr hn)

/-- … and, with the counts of its replications non-negative (the fourth conjunct of `InRangeObl`), `TSite.ConstOK` at every
reached valuation. -/
theorem site_co {s : Summary} {σ : String → Int} (hok : s.StructOk) (hin : s.InRangeObl σ) {ls : LSite}
    (hls : ls ∈ s.lsites) {σ' : String → Int} (hr : Reach ls.hdrs σ σ') :
    ls.site.ConstOK σ' (ls.hdrs.map (·.g) ++ s.params) :=
  ⟨site_cn hok hls, (Loops.all_iff _ _ _).mp (hin.rc_all ls hls) σ' hr⟩

/-- **The `SiteCtx` of a located site at a reached valuation**: everything the per-site proofs read. -/
theorem siteCtx_of_reach {s : Summary} {args : List Int} {σ : String → Int} {envD : IEnv}
    {elems : List (String × Nat)}
    (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) {ls : LSite} (hls : ls ∈ s.lsites)
    {σ' : String → Int} {E' : IEnv} (hr : ReachE ls.hdrs σ envD σ' E') :
    SiteCtx s σ elems ls σ' E' := by
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ := hok
  obtain ⟨hauto1, hauto2, hauto3⟩ := hauto
  have hnm : ∀ n, (s.DW σ n).isSome = true → n ∈ s.declNames := by
    intro n hn
    exact mem_declNames_of_find (by simpa [Summary.DW] using hn)
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
  have hin' := (Loops.all_iff _ _ _).mp (hin.1 ls hls) σ' (ReachE_Reach hr)
  have hauto' := (Loops.all_iff _ _ _).mp (hauto1 ls hls) σ' (ReachE_Reach hr)
  have hinM := (Loops.all_iff _ _ _).mp (hin.more_all ls hls) σ' (ReachE_Reach hr)
  have hInR : ∀ a ∈ ls.site.tgt :: (ls.site.more ++ ls.site.rds), s.InR σ σ' a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hm
    · exact hin'.1
    · rcases List.mem_append.mp hm with hm | hm
      · exact (hinM a hm).1
      · exact hauto' a hm
  have hso : ∀ a ∈ ls.site.tgt :: (ls.site.more ++ ls.site.rds),
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
      · exact Or.inl (Or.inl ⟨x, hx, hn⟩)
      · exact Or.inl (Or.inr ⟨a, List.mem_append.mp hm, x, hx, hn⟩)
  exact ⟨C', hnm, hpar, ReachE_Reach hr, hin', hinM, hso,
    site_co ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ hin hls (ReachE_Reach hr)⟩


/-- **The shared preamble of the per-site description lemmas** (`pairs_desc`, `pairs_descL`): every pair of
`Summary.pairs` is the footprint and the instantiated process of a located site at a reached valuation, with
its `SiteCtx`. -/
theorem pairs_ctx {s : Summary} {args : List Int} {σ : String → Int} {envD : IEnv}
    {elems : List (String × Nat)}
    (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) :
    ∀ q ∈ s.pairs σ envD elems, ∃ ls ∈ s.lsites, ∃ (σ' : String → Int) (E' : IEnv),
      q = (ls.inst σ' (s.dw σ), instProcess2 E' elems ls.site.proc) ∧ SiteCtx s σ elems ls σ' E' := by
  intro q hq
  unfold Summary.pairs at hq
  rw [mem_enum_E] at hq
  obtain ⟨ls, hls, σ', E', hr, rfl⟩ := hq
  exact ⟨ls, hls, σ', E', rfl, siteCtx_of_reach C hok hauto hin hls hr⟩

/-- An old site (the recognizer `siteOf?` accepts its process) satisfies `Desc` at any reached instance. -/
theorem pairs_desc_site {s : Summary} {σ : String → Int} {elems : List (String × Nat)} {ls : LSite}
    {σ' : String → Int} {E' : IEnv} (hc : SiteCtx s σ elems ls σ' E') {pos : Nat} {p : PProcess}
    (hp : siteOf? s.decls pos p = .ok ls.site) :
    Desc s.declNames (ls.inst σ' (s.dw σ)) (instProcess2 E' elems ls.site.proc) := by
  have hweq : ∀ q ∈ p.scmpPairs, q.Holds (s.DW σ) := by
    intro q hq
    rcases siteOf?_cases hp with ⟨t, v, rds, rfl, hrds, -⟩ | ⟨l, v, tg, rds, rfl, -, hrds, -⟩ <;>
    · simp only [PProcess.scmpPairs] at hq
      by_cases hf : ∃ b, v = .fill b
      · obtain ⟨b, rfl⟩ := hf
        simp [PExpr.scmpPairs] at hq
      · have h2 : rdsOfW? s.decls v = .ok rds := by
          cases v <;> first | exact hrds | (exfalso; exact hf ⟨_, rfl⟩)
        exact ScmpReq.holds_of_dimsOk σ (scmpPairs_dims h2 q hq)
  have h := site_desc hc.ctx hc.nm hp (fun a ha => hc.so a (TSite.mem_accs ha)) hc.cn hweq
    (si := ls.inst σ' (s.dw σ)) rfl rfl (by simp [LSite.inst, siteOf?_more hp])
  rw [← siteOf?_proc hp] at h
  exact h

theorem pairs_desc {s : Summary} {args : List Int} {σ : String → Int} {envD : IEnv}
    {elems : List (String × Nat)}
    (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hsites : ∀ ls ∈ s.lsites, ∃ pos p, siteOf? s.decls pos p = .ok ls.site) :
    ∀ q ∈ s.pairs σ envD elems, Desc s.declNames q.1 q.2 := by
  intro q hq
  obtain ⟨ls, hls, σ', E', rfl, hc⟩ := pairs_ctx C hok hauto hin q hq
  obtain ⟨pos, p, hp⟩ := hsites ls hls
  exact pairs_desc_site hc hp

/-! ## The generate tree expands to the closed form -/

theorem Hdr.expand2 {env : IEnv} {elems : List (String × Nat)} {F : Nat} {σ : String → Int}
    {ns : List String} (hag : Agrees σ env ns) {h : Hdr} (hwf : h.Wf)
    (hbn : ∀ n ∈ h.bound.names, n ∈ ns ∧ n ≠ h.g)
    (hF : (h.bound.eval σ - h.c0).toNat < F) (rc : Option Nat) (body : List GenItem)
    {f : Int → List Process2}
    (hf : ∀ v, h.Rng σ v → expandList2 (env.bindVal h.g v) elems F body = .ok (f v)) :
    (h.gen rc body).expand2 env elems F = .ok ((h.range σ).flatMap f) := by
  have hbag : ∀ i : Int, ∀ n ∈ h.bound.names,
      (env.bindVal h.g i).intVal? n = some (σ n) := by
    intro i n hn
    obtain ⟨hnp, hng⟩ := hbn n hn
    have hb' : (n == h.g) = false := beq_eq_false_iff_ne.2 hng
    exact (IEnv.intVal?_bindVal_ne i hng).trans (hag n hnp)
  have hei : ∀ i : Int, h.bndE.isInt (env.bindVal h.g i) = true :=
    fun i => (affOf?_sound h.bndE h.bound hwf (hbag i)).1
  have he : ∀ i : Int, evalInt (env.bindVal h.g i) h.bndE = .ok (h.bound.eval σ) :=
    fun i => (affOf?_sound h.bndE h.bound hwf (hbag i)).2
  exact GenItem.expand2_genFor_ascending_flatMap (evalInt_int h.c0) hei he hF
    (fun v hv1 hv2 => hf v ⟨hv1, hv2⟩)

/-- The processes of one body item of an outer loop, at the outer iteration's valuation and
environment. -/
def itemProcs (elems : List (String × Nat)) (σ1 : String → Int) (E1 : IEnv) : TItem → List Process2
  | .site st => [instProcess2 E1 elems st.proc]
  | .loop l => (l.hdr.range σ1).flatMap fun j =>
      l.body.map fun st => instProcess2 (E1.bindVal l.hdr.g j) elems st.proc

theorem items_expand2 {elems : List (String × Nat)} {F : Nat} {σ1 : String → Int} {E1 : IEnv}
    {ns1 : List String} (hag : Agrees σ1 E1 ns1) :
    ∀ (its : List TItem),
      (∀ l, TItem.loop l ∈ its → l.hdr.Wf ∧ (∀ n ∈ l.hdr.bound.names, n ∈ ns1 ∧ n ≠ l.hdr.g) ∧
        (l.hdr.bound.eval σ1 - l.hdr.c0).toNat < F) →
      expandList2 E1 elems F (its.map TItem.toGen) = .ok (its.flatMap (itemProcs elems σ1 E1))
  | [], _ => by simp
  | it :: rest, hl => by
      have hrest := items_expand2 (elems := elems) hag rest (fun l hm => hl l (List.mem_cons_of_mem _ hm))
      have hit : it.toGen.expand2 E1 elems F = .ok (itemProcs elems σ1 E1 it) := by
        cases it with
        | site st => simp [TItem.toGen, itemProcs]
        | loop l =>
            obtain ⟨hwf, hbn, hF⟩ := hl l (List.mem_cons_self ..)
            have := Hdr.expand2 hag hwf hbn hF l.rc (l.body.map fun st => GenItem.process st.proc)
              (f := fun j => l.body.map fun st => instProcess2 (E1.bindVal l.hdr.g j) elems st.proc)
              (fun v _ => by
                have h := expandList2_processes (env := E1.bindVal l.hdr.g v) (elems := elems)
                  (F := F) (l.body.map TSite.proc)
                simpa [List.map_map, Function.comp_def] using h)
            simpa [TItem.toGen, itemProcs] using this
      rw [List.map_cons, expandList2_cons_ok hit hrest, List.flatMap_cons]


/-- Binding a genvar that is not a parameter does not change a parameter-only bound. -/
theorem bound_eval_bind {ps : List String} {h : Hdr} {g : String} {σ : String → Int} {i : Int}
    (hb : ∀ n ∈ h.bound.names, n ∈ ps) (hg : g ∉ ps) :
    h.bound.eval (bindσ g i σ) = h.bound.eval σ :=
  Aff.eval_congr _ _ _ (fun n hn => bindσ_ne (fun heq => hg (by rw [← heq]; exact hb n hn)) i σ)

/-- The path facts of the structural check, for a loop header path. -/
theorem path_facts {s : Summary} (hok : s.StructOk) {p : List Hdr} (hp : p ∈ s.hdrPaths) :
    (p.map (·.g) ++ s.params).Nodup ∧ ∀ h ∈ p, (∀ n ∈ h.bound.names, n ∈ s.params) ∧ 0 ≤ h.c0 :=
  hok.2.2.2.2.1 p hp

/-- **A top-level generate loop expands to the closed form `TFam.enum`.** -/
theorem fam_expand2 {s : Summary} {σ : String → Int} {env : IEnv} {elems : List (String × Nat)}
    {F : Nat} (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hfuel : ∀ p ∈ s.hdrPaths, ∀ h ∈ p, (h.bound.eval σ - h.c0).toNat < F)
    {f : TFam} (hf : f ∈ s.fams) (hwf : f.Wf) :
    f.toGen.expand2 env elems F = .ok (TFam.enum (procB elems) σ env f) := by
  have hp1 : [f.hdr] ∈ s.hdrPaths := by
    unfold Summary.hdrPaths
    simp only [List.mem_flatMap, List.mem_cons]
    exact ⟨f, hf, Or.inl rfl⟩
  obtain ⟨hnd1, hb1⟩ := path_facts hok hp1
  have hg1 : f.hdr.g ∉ s.params := notin_of_nodup hnd1 (by simp)
  have hbn : ∀ n ∈ f.hdr.bound.names, n ∈ s.params ∧ n ≠ f.hdr.g :=
    fun n hn => ⟨(hb1 f.hdr (List.mem_singleton_self _)).1 n hn,
      fun heq => hg1 (by rw [← heq]; exact (hb1 f.hdr (List.mem_singleton_self _)).1 n hn)⟩
  have := Hdr.expand2 hag hwf.1 hbn (hfuel [f.hdr] hp1 f.hdr (List.mem_singleton_self _))
    f.rc (f.body.map TItem.toGen)
    (f := fun i => f.body.flatMap (itemProcs elems (bindσ f.hdr.g i σ) (env.bindVal f.hdr.g i)))
    (fun v _ => by
      apply items_expand2 (ns1 := f.hdr.g :: s.params) (hag.bindVal f.hdr.g v)
      intro l hl
      have hp2 : [f.hdr, l.hdr] ∈ s.hdrPaths := by
        unfold Summary.hdrPaths
        simp only [List.mem_flatMap, List.mem_cons, List.mem_filterMap]
        exact ⟨f, hf, Or.inr ⟨TItem.loop l, hl, rfl⟩⟩
      obtain ⟨hnd2, hb2⟩ := path_facts hok hp2
      have hg2 : l.hdr.g ∉ s.params := notin_of_nodup hnd2 (by simp)
      have hbl := (hb2 l.hdr (by simp)).1
      refine ⟨hwf.2 (TItem.loop l) hl, fun n hn => ⟨List.mem_cons_of_mem _ (hbl n hn),
        fun heq => hg2 (by rw [← heq]; exact hbl n hn)⟩, ?_⟩
      rw [bound_eval_bind hbl hg1]
      exact hfuel [f.hdr, l.hdr] hp2 l.hdr (by simp))
  exact this


/-- The finite family expansion, from the well-formedness of the families alone (the only part of the spec the
expansion reads): the core of `fams_expand2` (over `SpecOk`) and `fams_expand2P` (over `SpecOkP`). -/
theorem fams_expand2W {s : Summary} {σ : String → Int} {env : IEnv} {elems : List (String × Nat)}
    {F : Nat} (hag : Agrees σ env s.params) (hok : s.StructOk) (hwf : ∀ f ∈ s.fams, f.Wf)
    (hfuel : ∀ p ∈ s.hdrPaths, ∀ h ∈ p, (h.bound.eval σ - h.c0).toNat < F) :
    ∀ (fs : List TFam), (∀ f ∈ fs, f ∈ s.fams) →
      expandList2 env elems F (fs.map TFam.toGen) =
        .ok (fs.flatMap fun f => TFam.enum (procB elems) σ env f)
  | [], _ => by simp
  | f :: fs, hfs => by
      have hf : f ∈ s.fams := hfs f (List.mem_cons_self ..)
      rw [List.map_cons, expandList2_cons_ok (fam_expand2 hag hok hfuel hf (hwf f hf))
        (fams_expand2W hag hok hwf hfuel fs (fun g hg => hfs g (List.mem_cons_of_mem _ hg))),
        List.flatMap_cons]

theorem fams_expand2 {s : Summary} {σ : String → Int} {env : IEnv} {elems : List (String × Nat)}
    {F : Nat} (hag : Agrees σ env s.params) (hok : s.StructOk) (hspec : s.SpecOk)
    (hfuel : ∀ p ∈ s.hdrPaths, ∀ h ∈ p, (h.bound.eval σ - h.c0).toNat < F) :
    ∀ (fs : List TFam), (∀ f ∈ fs, f ∈ s.fams) →
      expandList2 env elems F (fs.map TFam.toGen) =
        .ok (fs.flatMap fun f => TFam.enum (procB elems) σ env f) :=
  fams_expand2W hag hok (fun f hf => (hspec f hf).1) hfuel

/-! ## The soundness theorem -/

/-- `m` realizes the summary at `σ`: its declarations are the summary's, and its process list is
the closed-form `Summary.pairs` — each process an `assign` to the promised window reading only
promised windows. -/
def Realized (s : Summary) (σ : String → Int) (m : Design2) : Prop :=
  m.decls.toList = s.decls.map (DeclT.toDecl σ) ∧
  ∃ (E : IEnv) (L : List (SiteInst × Process2)), L.map Prod.fst = s.insts σ E ∧
    m.processes.toList = L.map Prod.snd ∧ ∀ q ∈ L, Desc s.declNames q.1 q.2

/-- **The shared first half of `Summary.sound` and `Summary.soundL`**: from the parameter stage, the declaration
stage and the generate stage of the recognizer's specification, the real instantiation succeeds with a design `M`
whose declarations are the summary's and whose process list is the second components of `Summary.pairs`, and the
reached context holds. -/
theorem sound_prefix {d : PDesign} {s : Summary} {args : List Int} {σ : String → Int} {env : IEnv}
    (harity : args.length = d.params.length) (h1 : d.paramEnv2 args = .ok env)
    (hag : Agrees σ env s.params) (hok : s.StructOk) (hauto : s.AutoObl σ args)
    (hoth : d.others = []) (hsd : declsOf? d.decls = .ok s.decls)
    (hproc : s.statics.map TSite.proc = d.processes) (hgen : d.generates = s.fams.map TFam.toGen)
    (hwf : ∀ f ∈ s.fams, f.Wf) :
    Ctx σ (env.withDecls (s.decls.map (DeclT.toDecl σ))) (s.decls.map fun dt => (dt.name, dt.elemW σ))
      (s.DW σ) (s.DG σ) (s.EW σ) s.params ∧
    ∃ M, d.instantiate2 args (PDesign.surfaceFuel args) = .ok M ∧
      M.decls.toList = s.decls.map (DeclT.toDecl σ) ∧
      M.processes.toList = (s.pairs σ (env.withDecls (s.decls.map (DeclT.toDecl σ)))
        (s.decls.map fun dt => (dt.name, dt.elemW σ))).map Prod.snd := by
  have hok' := hok
  obtain ⟨-, -, -, -, -, hdecl, -, -⟩ := hok'
  have hagd : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, env.intVal? n = some (σ n) :=
    fun dt hdt n hn => hag n (hdecl dt hdt n hn)
  have h2 := buildDecls_summary (σ := σ) d.decls s.decls hsd env hagd
  have h3 := buildElems_summary (σ := σ) d.decls s.decls hsd env hagd
  have hdim := paramEnv2_dims h1
  obtain ⟨-, -, hauto3⟩ := hauto
  refine ⟨ctx_of_env hsd hdim hag hdecl, ?_⟩
  have hfuel : ∀ p ∈ s.hdrPaths, ∀ h ∈ p,
      (h.bound.eval σ - h.c0).toNat < PDesign.surfaceFuel args :=
    fun p hp h hh => surfaceFuel_gt args _ (hauto3 p hp h hh)
  have h4 : expandList2 (env.withDecls (s.decls.map (DeclT.toDecl σ)))
      (s.decls.map fun dt => (dt.name, dt.elemW σ)) (PDesign.surfaceFuel args) d.generates =
      .ok (s.fams.flatMap fun f => TFam.enum
        (procB (s.decls.map fun dt => (dt.name, dt.elemW σ))) σ
        (env.withDecls (s.decls.map (DeclT.toDecl σ))) f) := by
    rw [hgen]
    exact fams_expand2W (env := env.withDecls (s.decls.map (DeclT.toDecl σ)))
      (elems := s.decls.map fun dt => (dt.name, dt.elemW σ)) hag hok hwf hfuel
      s.fams (fun f hf => hf)
  refine ⟨_, PDesign.instantiate2_of_ok harity h1 h2 h3 h4, by simp, ?_⟩
  rw [PDesign.assemble2_processes, hoth, ← hproc]
  have hmap := Summary.enum_map s
    (fun ls σ' E' => (ls.inst σ' (s.dw σ),
      instProcess2 E' (s.decls.map fun dt => (dt.name, dt.elemW σ)) ls.site.proc))
    Prod.snd σ (env.withDecls (s.decls.map (DeclT.toDecl σ)))
  unfold Summary.pairs
  rw [hmap]
  simp only [Summary.enum, List.map_map, List.map_nil, List.append_nil, Function.comp_def]
  try rfl

/-- **`Summary.sound`: the family summary is sound against `PDesign.instantiate2`.** -/
theorem Summary.sound {d : PDesign} {s : Summary} (hs : d.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) :
    ∃ m, d.instantiate2 args (PDesign.surfaceFuel args) = .ok m ∧ Realized s σ m := by
  obtain ⟨hloc, hens, hoth, hpar, hsd, hsts, hgen, hspec⟩ := summary_spec hs
  obtain ⟨hproc, hsites0⟩ := sitesOf?_spec hsts
  have hsites := lsites_spec hsites0 hspec
  obtain ⟨C, M, hMi, hMd, hMp⟩ :=
    sound_prefix harity h1 hag hok hauto hoth hsd hproc hgen (fun f hf => (hspec f hf).1)
  exact ⟨M, hMi, hMd, env.withDecls (s.decls.map (DeclT.toDecl σ)),
    s.pairs σ (env.withDecls (s.decls.map (DeclT.toDecl σ))) (s.decls.map fun dt => (dt.name, dt.elemW σ)),
    Summary.pairs_map_fst .., hMp, pairs_desc C hok hauto hin hsites⟩

/-! ## Axiom pins of the generic recognizer specifications (WP-G consolidation, Tier A) -/

/-- info: 'LeanModels.Sv.CombView.sitesOfG_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sitesOfG_spec

/-- info: 'LeanModels.Sv.CombView.itemOfG_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms itemOfG_spec

/-- info: 'LeanModels.Sv.CombView.itemsOfG_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms itemsOfG_spec

/-- info: 'LeanModels.Sv.CombView.famOfG_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms famOfG_spec

/-- info: 'LeanModels.Sv.CombView.famsOfG_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms famsOfG_spec

/-- info: 'LeanModels.Sv.CombView.summaryG_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms summaryG_spec

/-- info: 'LeanModels.Sv.CombView.lsitesG_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lsitesG_spec

/-- info: 'LeanModels.Sv.CombView.siteOf?_proc'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms siteOf?_proc'

end CombView
end LeanModels.Sv
