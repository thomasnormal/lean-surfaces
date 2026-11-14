import LeanModels.Sv.CombViewThm
import LeanModels.Sv.CombGenGuard

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

mutual
/-- The sites an item holds (at any depth). -/
def TItem.stList : TItem → List TSite
  | .site st => [st]
  | .loop _ _ body => TItem.stListL body
  | .cond _ _ thn els => TItem.stListL thn ++ TItem.stListL els

def TItem.stListL : List TItem → List TSite
  | [] => []
  | it :: rest => it.stList ++ TItem.stListL rest
end

theorem TItem.mem_stListL {st : TSite} : ∀ {l : List TItem}, st ∈ TItem.stListL l ↔ ∃ it ∈ l, st ∈ it.stList
  | [] => by simp [TItem.stListL]
  | it :: rest => by simp [TItem.stListL, TItem.mem_stListL (l := rest)]

theorem TItem.mem_stList_loop {st : TSite} {h : Hdr} {rc : Option Nat} {body : List TItem} :
    st ∈ (TItem.loop h rc body).stList ↔ ∃ it ∈ body, st ∈ it.stList := by
  rw [TItem.stList, TItem.mem_stListL]

theorem TItem.mem_stList_cond {st : TSite} {c : PExpr} {g : Guard} {thn els : List TItem} :
    st ∈ (TItem.cond c g thn els).stList ↔ (∃ it ∈ thn, st ∈ it.stList) ∨ ∃ it ∈ els, st ∈ it.stList := by
  rw [TItem.stList, List.mem_append, TItem.mem_stListL, TItem.mem_stListL]

mutual
theorem itemOfG_spec (so : List DeclT → Nat → PProcess → Except String TSite)
    (hso : ∀ ds pos p st, so ds pos p = .ok st → st.proc = p) {ds : List DeclT} :
    ∀ {tag : String} {pos : Nat} {it : GenItem} {x : TItem}, itemOfG so ds tag pos it = .ok x →
      x.toGen = it ∧ x.Wf ∧ ∀ st ∈ x.stList, ∃ pos' p, so ds pos' p = .ok st
  | tag, pos, .process p, x, h => by
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
  | tag, pos, .genFor label g initE bound step rc body, x, h => by
      simp only [itemOfG] at h
      rcases hh : hdrOf? label g initE bound step with e | h0
      · simp [hh] at h
      · rcases hit : itemsOfG so ds h0.name 0 body with e | its
        · simp [hh, hit] at h
        · simp only [hh, hit, Except.ok.injEq] at h
          subst h
          obtain ⟨hl, hg, hwf, hi, hb, hst⟩ := hdrOf?_spec hh
          obtain ⟨k1, k2⟩ := itemsOfG_spec so hso hit
          refine ⟨?_, TItem.wf_loop.mpr ⟨hwf, fun y hy => (k2 y hy).1⟩, fun st hst' => ?_⟩
          · rw [TItem.toGen_loop]
            simp only [Hdr.gen]
            rw [← hi, ← hb, ← hst, hl, hg, k1]
          · obtain ⟨y, hy, hsty⟩ := TItem.mem_stList_loop.mp hst'
            exact (k2 y hy).2 st hsty
  | tag, pos, .genIf c thn els, x, h => by
      simp only [itemOfG] at h
      rcases hg : guardOf? c with _ | g
      · simp [hg] at h
      · rcases ht : itemsOfG so ds tag pos thn with e | ts
        · simp [hg, ht] at h
        · rcases he : itemsOfG so ds tag (pos + GenItem.slotsL thn) els with e | es
          · simp [hg, ht, he] at h
          · simp only [hg, ht, he, Except.ok.injEq] at h
            subst h
            obtain ⟨k1, k2⟩ := itemsOfG_spec so hso ht
            obtain ⟨l1, l2⟩ := itemsOfG_spec so hso he
            refine ⟨by rw [TItem.toGen_cond, k1, l1],
              TItem.wf_cond.mpr ⟨hg, fun y hy => (k2 y hy).1, fun y hy => (l2 y hy).1⟩, fun st hst => ?_⟩
            rcases TItem.mem_stList_cond.mp hst with ⟨y, hy, hs⟩ | ⟨y, hy, hs⟩
            · exact (k2 y hy).2 st hs
            · exact (l2 y hy).2 st hs
  | _, _, .inst i, x, h => by simp [itemOfG] at h
  | _, _, .decl d, x, h => by simp [itemOfG] at h
  | _, _, .unsupported k t, x, h => by simp [itemOfG] at h

theorem itemsOfG_spec (so : List DeclT → Nat → PProcess → Except String TSite)
    (hso : ∀ ds pos p st, so ds pos p = .ok st → st.proc = p) {ds : List DeclT} :
    ∀ {tag : String} {pos : Nat} {items : List GenItem} {its : List TItem}, itemsOfG so ds tag pos items = .ok its →
      its.map TItem.toGen = items ∧ ∀ x ∈ its, x.Wf ∧
        ∀ st ∈ x.stList, ∃ pos' p, so ds pos' p = .ok st
  | tag, pos, [], its, h => by
      simp only [itemsOfG, Except.ok.injEq] at h
      subst h
      simp
  | tag, pos, it :: rest, its, h => by
      simp only [itemsOfG] at h
      rcases hx : itemOfG so ds tag pos it with e | x
      · simp [hx] at h
      · rcases hr : itemsOfG so ds tag (pos + it.slots) rest with e | xs
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
end

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
  | decl d => simp [famOfG] at h
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

/-! ### The generate tree, item by item

An item in the body of the loop `cur`, under the loops `outer` around `cur`, lists its located sites (`TItem.lsAt`), its
loop headers (`TItem.stepsAt`), its conditions (`TItem.condsAt`) and its closed form (`TItem.enumAt`). A located site
of the item sits under `outer`, then `cur` with the guards of the arms it is in (`Hdr.guards`), then the item's loops
around it (`TItem.lsAt_shape`). The lemmas below relate the four, by recursion over the tree (any depth). -/

theorem TItem.mem_lsAtL_of {outer : List Hdr} {cur : Hdr} {blk : String} {its : List TItem} {it : TItem}
    {ls : LSite} (hit : it ∈ its) (hls : ls ∈ it.lsAt outer cur blk) : ls ∈ TItem.lsAtL outer cur blk its := by
  induction its with
  | nil => simp at hit
  | cons y ys ih =>
      simp only [TItem.lsAtL, List.mem_append]
      rcases List.mem_cons.mp hit with rfl | h
      · exact Or.inl hls
      · exact Or.inr (ih h)

theorem TItem.mem_enumAtL_item {β : Type} {b : LSite → (String → Int) → IEnv → β} {outer : List Hdr}
    {cur : Hdr} {blk : String} {σ : String → Int} {E : IEnv} {its : List TItem} {x : β}
    (hx : x ∈ TItem.enumAtL b outer cur blk σ E its) : ∃ it ∈ its, x ∈ it.enumAt b outer cur blk σ E := by
  induction its with
  | nil => simp [TItem.enumAtL] at hx
  | cons y ys ih =>
      simp only [TItem.enumAtL, List.mem_append] at hx
      rcases hx with h | h
      · exact ⟨y, List.mem_cons_self .., h⟩
      · obtain ⟨it, hit, h'⟩ := ih h
        exact ⟨it, List.mem_cons_of_mem _ hit, h'⟩

mutual
/-- **The shape of a located site**: under `outer`, then `cur` with further guards, then the item's loops. -/
theorem TItem.lsAt_shape : ∀ (outer : List Hdr) (cur : Hdr) (blk : String) (it : TItem) (ls : LSite),
    ls ∈ it.lsAt outer cur blk → ∃ gs inner, ls.hdrs = outer ++ (cur.guards gs :: inner)
  | outer, cur, blk, .site st, ls, h => by
      simp only [TItem.lsAt, List.mem_singleton] at h
      subst h
      exact ⟨[], [], by simp [Hdr.guards_nil]⟩
  | outer, cur, _, .loop hd _ body, ls, h => by
      simp only [TItem.lsAt] at h
      obtain ⟨gs, inner, e⟩ := TItem.lsAtL_shape (outer ++ [cur]) hd hd.name body ls h
      exact ⟨[], hd.guards gs :: inner, by rw [e, Hdr.guards_nil]; simp⟩
  | outer, cur, blk, .cond _ g thn els, ls, h => by
      simp only [TItem.lsAt, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨gs, inner, e⟩ := TItem.lsAtL_shape outer (cur.guards [(g, true)]) blk thn ls h
        exact ⟨(g, true) :: gs, inner, by rw [e, Hdr.guards_guards]; rfl⟩
      · obtain ⟨gs, inner, e⟩ := TItem.lsAtL_shape outer (cur.guards [(g, false)]) blk els ls h
        exact ⟨(g, false) :: gs, inner, by rw [e, Hdr.guards_guards]; rfl⟩

theorem TItem.lsAtL_shape : ∀ (outer : List Hdr) (cur : Hdr) (blk : String) (its : List TItem) (ls : LSite),
    ls ∈ TItem.lsAtL outer cur blk its → ∃ gs inner, ls.hdrs = outer ++ (cur.guards gs :: inner)
  | _, _, _, [], ls, h => by simp [TItem.lsAtL] at h
  | outer, cur, blk, it :: rest, ls, h => by
      simp only [TItem.lsAtL, List.mem_append] at h
      rcases h with h | h
      · exact TItem.lsAt_shape outer cur blk it ls h
      · exact TItem.lsAtL_shape outer cur blk rest ls h
end

mutual
/-- The genvars along a located site of an item: those of `outer ++ [cur]`, or those along one of the item's loops. -/
theorem TItem.lsAt_gvs : ∀ (outer : List Hdr) (cur : Hdr) (blk : String) (it : TItem) (ls : LSite),
    ls ∈ it.lsAt outer cur blk → ls.hdrs.map (·.g) = (outer ++ [cur]).map (·.g) ∨
      ∃ q ∈ it.stepsAt outer cur, ls.hdrs.map (·.g) = (q.1 ++ [q.2]).map (·.g)
  | outer, cur, blk, .site st, ls, h => by
      simp only [TItem.lsAt, List.mem_singleton] at h
      subst h
      exact Or.inl rfl
  | outer, cur, _, .loop hd _ body, ls, h => by
      simp only [TItem.lsAt] at h
      right
      rcases TItem.lsAtL_gvs (outer ++ [cur]) hd hd.name body ls h with e | ⟨q, hq, e⟩
      · exact ⟨(outer ++ [cur], hd), by simp [TItem.stepsAt], e⟩
      · exact ⟨q, by simp only [TItem.stepsAt, List.mem_cons]; exact Or.inr hq, e⟩
  | outer, cur, blk, .cond _ g thn els, ls, h => by
      simp only [TItem.lsAt, List.mem_append] at h
      rcases h with h | h
      · rcases TItem.lsAtL_gvs outer (cur.guards [(g, true)]) blk thn ls h with e | ⟨q, hq, e⟩
        · exact Or.inl (by rw [e]; simp)
        · exact Or.inr ⟨q, by simp only [TItem.stepsAt, List.mem_append]; exact Or.inl hq, e⟩
      · rcases TItem.lsAtL_gvs outer (cur.guards [(g, false)]) blk els ls h with e | ⟨q, hq, e⟩
        · exact Or.inl (by rw [e]; simp)
        · exact Or.inr ⟨q, by simp only [TItem.stepsAt, List.mem_append]; exact Or.inr hq, e⟩

theorem TItem.lsAtL_gvs : ∀ (outer : List Hdr) (cur : Hdr) (blk : String) (its : List TItem) (ls : LSite),
    ls ∈ TItem.lsAtL outer cur blk its → ls.hdrs.map (·.g) = (outer ++ [cur]).map (·.g) ∨
      ∃ q ∈ TItem.stepsAtL outer cur its, ls.hdrs.map (·.g) = (q.1 ++ [q.2]).map (·.g)
  | _, _, _, [], ls, h => by simp [TItem.lsAtL] at h
  | outer, cur, blk, it :: rest, ls, h => by
      simp only [TItem.lsAtL, List.mem_append] at h
      rcases h with h | h
      · rcases TItem.lsAt_gvs outer cur blk it ls h with e | ⟨q, hq, e⟩
        · exact Or.inl e
        · exact Or.inr ⟨q, by simp only [TItem.stepsAtL, List.mem_append]; exact Or.inl hq, e⟩
      · rcases TItem.lsAtL_gvs outer cur blk rest ls h with e | ⟨q, hq, e⟩
        · exact Or.inl e
        · exact Or.inr ⟨q, by simp only [TItem.stepsAtL, List.mem_append]; exact Or.inr hq, e⟩
end

mutual
/-- The site of a located site of an item is one of the item's sites. -/
theorem TItem.lsAt_site : ∀ (outer : List Hdr) (cur : Hdr) (blk : String) (it : TItem) (ls : LSite),
    ls ∈ it.lsAt outer cur blk → ls.site ∈ it.stList
  | outer, cur, blk, .site st, ls, h => by
      simp only [TItem.lsAt, List.mem_singleton] at h
      subst h
      simp [TItem.stList]
  | outer, cur, _, .loop hd _ body, ls, h => by
      simp only [TItem.lsAt] at h
      rw [TItem.mem_stList_loop]
      exact TItem.lsAtL_site (outer ++ [cur]) hd hd.name body ls h
  | outer, cur, blk, .cond _ g thn els, ls, h => by
      simp only [TItem.lsAt, List.mem_append] at h
      rw [TItem.mem_stList_cond]
      rcases h with h | h
      · exact Or.inl (TItem.lsAtL_site outer _ blk thn ls h)
      · exact Or.inr (TItem.lsAtL_site outer _ blk els ls h)

theorem TItem.lsAtL_site : ∀ (outer : List Hdr) (cur : Hdr) (blk : String) (its : List TItem) (ls : LSite),
    ls ∈ TItem.lsAtL outer cur blk its → ∃ it ∈ its, ls.site ∈ it.stList
  | _, _, _, [], ls, h => by simp [TItem.lsAtL] at h
  | outer, cur, blk, it :: rest, ls, h => by
      simp only [TItem.lsAtL, List.mem_append] at h
      rcases h with h | h
      · exact ⟨it, List.mem_cons_self .., TItem.lsAt_site outer cur blk it ls h⟩
      · obtain ⟨y, hy, hs⟩ := TItem.lsAtL_site outer cur blk rest ls h
        exact ⟨y, List.mem_cons_of_mem _ hy, hs⟩
end

/-- Two shapes of one located site agree (`TItem.lsAt_shape` is unique). -/
theorem shape_inj {outer : List Hdr} {cur : Hdr} {gs gs' : List (Guard × Bool)} {inner inner' : List Hdr}
    (e : outer ++ (cur.guards gs :: inner) = outer ++ (cur.guards gs' :: inner')) : gs = gs' ∧ inner = inner' := by
  have e' := List.append_cancel_left e
  simp only [List.cons.injEq] at e'
  exact ⟨Hdr.guards_inj e'.1, e'.2⟩

mutual
/-- **Membership in an item's closed form**: an entry is the builder at a located site of the item, at a valuation
reached through the item's loops around the site, where the guards of the arms the site is in hold. -/
theorem TItem.mem_enumAt {β : Type} (b : LSite → (String → Int) → IEnv → β) {x : β} :
    ∀ (outer : List Hdr) (cur : Hdr) (blk : String) (σ : String → Int) (E : IEnv) (it : TItem),
      x ∈ it.enumAt b outer cur blk σ E ↔
        ∃ ls ∈ it.lsAt outer cur blk, ∃ gs inner σ' E', ls.hdrs = outer ++ (cur.guards gs :: inner) ∧
          Guard.All gs σ ∧ ReachE inner σ E σ' E' ∧ x = b ls σ' E'
  | outer, cur, blk, σ, E, .site st => by
      simp only [TItem.enumAt, TItem.lsAt, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨_, rfl, [], [], σ, E, by simp [Hdr.guards_nil], trivial, ⟨rfl, rfl⟩, rfl⟩
      · rintro ⟨ls, rfl, gs, inner, σ', E', he, -, hr, rfl⟩
        have e0 : outer ++ [cur] = outer ++ (cur.guards [] :: []) := by rw [Hdr.guards_nil]
        obtain ⟨-, rfl⟩ := shape_inj (e0.symm.trans he)
        obtain ⟨rfl, rfl⟩ := hr
        rfl
  | outer, cur, blk, σ, E, .loop hd _ body => by
      simp only [TItem.enumAt, TItem.lsAt, List.mem_flatMap]
      constructor
      · rintro ⟨j, hj, hx⟩
        obtain ⟨ls, hls, gs, inner, σ', E', he, hg, hr, rfl⟩ :=
          (TItem.mem_enumAtL b (outer ++ [cur]) hd hd.name (bindσ hd.g j σ) (E.bindVal hd.g j) body).mp hx
        refine ⟨ls, hls, [], hd.guards gs :: inner, σ', E', by rw [he, Hdr.guards_nil]; simp, trivial,
          ⟨j, Hdr.rng_guards.mpr ⟨Hdr.mem_range.mp hj, hg⟩, hr⟩, rfl⟩
      · rintro ⟨ls, hls, gs, inner, σ', E', he, -, hr, rfl⟩
        obtain ⟨gs0, inner0, he0⟩ := TItem.lsAtL_shape (outer ++ [cur]) hd hd.name body ls hls
        have e1 : (outer ++ [cur]) ++ (hd.guards gs0 :: inner0) =
            outer ++ (cur.guards [] :: hd.guards gs0 :: inner0) := by rw [Hdr.guards_nil]; simp
        obtain ⟨-, rfl⟩ := shape_inj (he.symm.trans (he0.trans e1))
        obtain ⟨j, hj, hr'⟩ := hr
        obtain ⟨hj1, hj2⟩ := Hdr.rng_guards.mp hj
        exact ⟨j, Hdr.mem_range.mpr hj1,
          (TItem.mem_enumAtL b (outer ++ [cur]) hd hd.name (bindσ hd.g j σ) (E.bindVal hd.g j) body).mpr
            ⟨ls, hls, gs0, inner0, σ', E', he0, hj2, hr', rfl⟩⟩
  | outer, cur, blk, σ, E, .cond _ g thn els => by
      simp only [TItem.enumAt, TItem.lsAt, List.mem_append]
      constructor
      · intro hx
        split at hx
        · rename_i hgd
          obtain ⟨ls, hls, gs, inner, σ', E', he, hg, hr, rfl⟩ :=
            (TItem.mem_enumAtL b outer (cur.guards [(g, true)]) blk σ E thn).mp hx
          exact ⟨ls, Or.inl hls, (g, true) :: gs, inner, σ', E', by rw [he, Hdr.guards_guards]; rfl,
            ⟨hgd, hg⟩, hr, rfl⟩
        · rename_i hgd
          obtain ⟨ls, hls, gs, inner, σ', E', he, hg, hr, rfl⟩ :=
            (TItem.mem_enumAtL b outer (cur.guards [(g, false)]) blk σ E els).mp hx
          exact ⟨ls, Or.inr hls, (g, false) :: gs, inner, σ', E', by rw [he, Hdr.guards_guards]; rfl,
            ⟨hgd, hg⟩, hr, rfl⟩
      · rintro ⟨ls, hls | hls, gs, inner, σ', E', he, hg, hr, rfl⟩
        · obtain ⟨gs0, inner0, he0⟩ := TItem.lsAtL_shape outer (cur.guards [(g, true)]) blk thn ls hls
          rw [Hdr.guards_guards] at he0
          obtain ⟨rfl, rfl⟩ := shape_inj (he.symm.trans he0)
          obtain ⟨hgd, hg0⟩ := hg
          rw [if_pos hgd]
          exact (TItem.mem_enumAtL b outer (cur.guards [(g, true)]) blk σ E thn).mpr
            ⟨ls, hls, gs0, inner, σ', E', by rw [he, Hdr.guards_guards], hg0, hr, rfl⟩
        · obtain ⟨gs0, inner0, he0⟩ := TItem.lsAtL_shape outer (cur.guards [(g, false)]) blk els ls hls
          rw [Hdr.guards_guards] at he0
          obtain ⟨rfl, rfl⟩ := shape_inj (he.symm.trans he0)
          obtain ⟨hgd, hg0⟩ := hg
          rw [if_neg hgd]
          exact (TItem.mem_enumAtL b outer (cur.guards [(g, false)]) blk σ E els).mpr
            ⟨ls, hls, gs0, inner, σ', E', by rw [he, Hdr.guards_guards], hg0, hr, rfl⟩

theorem TItem.mem_enumAtL {β : Type} (b : LSite → (String → Int) → IEnv → β) {x : β} :
    ∀ (outer : List Hdr) (cur : Hdr) (blk : String) (σ : String → Int) (E : IEnv) (its : List TItem),
      x ∈ TItem.enumAtL b outer cur blk σ E its ↔
        ∃ ls ∈ TItem.lsAtL outer cur blk its, ∃ gs inner σ' E', ls.hdrs = outer ++ (cur.guards gs :: inner) ∧
          Guard.All gs σ ∧ ReachE inner σ E σ' E' ∧ x = b ls σ' E'
  | _, _, _, _, _, [] => by simp [TItem.enumAtL, TItem.lsAtL]
  | outer, cur, blk, σ, E, it :: rest => by
      simp only [TItem.enumAtL, TItem.lsAtL, List.mem_append]
      rw [TItem.mem_enumAt b outer cur blk σ E it, TItem.mem_enumAtL b outer cur blk σ E rest]
      constructor
      · rintro (⟨ls, hls, rest'⟩ | ⟨ls, hls, rest'⟩)
        · exact ⟨ls, Or.inl hls, rest'⟩
        · exact ⟨ls, Or.inr hls, rest'⟩
      · rintro ⟨ls, hls | hls, rest'⟩
        · exact Or.inl ⟨ls, hls, rest'⟩
        · exact Or.inr ⟨ls, hls, rest'⟩
end

theorem TFam.mem_enum {β : Type} (b : LSite → (String → Int) → IEnv → β) (σ : String → Int) (E : IEnv)
    (f : TFam) {x : β} :
    x ∈ TFam.enum b σ E f ↔ ∃ ls ∈ f.lsites, ∃ σ' E', ReachE ls.hdrs σ E σ' E' ∧ x = b ls σ' E' := by
  unfold TFam.enum TFam.lsites
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨i, hi, hx⟩
    obtain ⟨ls, hls, gs, inner, σ', E', he, hg, hr, rfl⟩ :=
      (TItem.mem_enumAtL b [] f.hdr f.hdr.name (bindσ f.hdr.g i σ) (E.bindVal f.hdr.g i) f.body).mp hx
    refine ⟨ls, hls, σ', E', ?_, rfl⟩
    rw [he, List.nil_append]
    exact ⟨i, Hdr.rng_guards.mpr ⟨Hdr.mem_range.mp hi, hg⟩, hr⟩
  · rintro ⟨ls, hls, σ', E', hr, rfl⟩
    obtain ⟨gs, inner, he⟩ := TItem.lsAtL_shape [] f.hdr f.hdr.name f.body ls hls
    rw [he, List.nil_append] at hr
    obtain ⟨i, hi, hr'⟩ := hr
    obtain ⟨hi1, hi2⟩ := Hdr.rng_guards.mp hi
    exact ⟨i, Hdr.mem_range.mpr hi1,
      (TItem.mem_enumAtL b [] f.hdr f.hdr.name (bindσ f.hdr.g i σ) (E.bindVal f.hdr.g i) f.body).mpr
        ⟨ls, hls, gs, inner, σ', E', he, hi2, hr', rfl⟩⟩

theorem mem_enum_E {β : Type} (s : Summary) (b : LSite → (String → Int) → IEnv → β)
    (σ : String → Int) (E : IEnv) {x : β} :
    x ∈ s.enum b σ E ↔
      ∃ ls ∈ s.lsites, ∃ σ' E', ReachE ls.hdrs σ E σ' E' ∧ x = b ls σ' E' := by
  unfold Summary.enum Summary.lsites
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, TFam.mem_enum]
  constructor
  · rintro (⟨st, hst, rfl⟩ | ⟨f, hf, ls, hls, σ', E', hr, rfl⟩)
    · exact ⟨⟨[], "plain", st⟩, Or.inl ⟨st, hst, rfl⟩, σ, E, ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨ls, Or.inr ⟨f, hf, hls⟩, σ', E', hr, rfl⟩
  · rintro ⟨ls, (⟨st, hst, rfl⟩ | ⟨f, hf, hls⟩), σ', E', hr, rfl⟩
    · obtain ⟨h1, h2⟩ := hr
      subst h1 h2
      exact Or.inl ⟨st, hst, rfl⟩
    · exact Or.inr ⟨f, hf, ls, hls, σ', E', hr, rfl⟩

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

/-- The genvars along a located site: none for a plain site, else those of one of the generate tree's header paths. -/
theorem lsite_hdrs {s : Summary} {ls : LSite} (h : ls ∈ s.lsites) :
    ls.hdrs = [] ∨ ∃ p ∈ s.hdrPaths, ls.hdrs.map (·.g) = p.map (·.g) := by
  unfold Summary.lsites at h
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, TFam.lsites] at h
  rcases h with ⟨st, hst, rfl⟩ | ⟨f, hf, hl⟩
  · exact Or.inl rfl
  · right
    unfold Summary.hdrPaths Summary.hdrSteps
    simp only [List.mem_map, List.mem_flatMap, List.mem_cons]
    rcases TItem.lsAtL_gvs [] f.hdr f.hdr.name f.body ls hl with e | ⟨q, hq, e⟩
    · exact ⟨_, ⟨([], f.hdr), ⟨f, hf, Or.inl rfl⟩, rfl⟩, e⟩
    · exact ⟨_, ⟨q, ⟨f, hf, Or.inr hq⟩, rfl⟩, e⟩

/-- Along a located site the genvars are distinct from the parameters (the structural check's path condition). -/
theorem lsite_g_notin {s : Summary} (hok : s.StructOk) {ls : LSite} (hls : ls ∈ s.lsites) :
    ∀ h ∈ ls.hdrs, h.g ∉ s.params := by
  intro h hh
  rcases lsite_hdrs hls with e | ⟨p, hp, e⟩
  · rw [e] at hh; simp at hh
  · have hm : h.g ∈ p.map (·.g) := by rw [← e]; exact List.mem_map.mpr ⟨h, hh, rfl⟩
    exact notin_of_nodup (hok.2.2.2.2.1 p hp).1 hm

/-- Along a located site the genvars are distinct (the structural check's path condition). -/
theorem lsite_nodup {s : Summary} (hok : s.StructOk) {ls : LSite} (hls : ls ∈ s.lsites) :
    (ls.hdrs.map (·.g)).Nodup := by
  rcases lsite_hdrs hls with e | ⟨p, hp, e⟩
  · rw [e]; exact List.nodup_nil
  · rw [e]; exact (List.nodup_append.mp (hok.2.2.2.2.1 p hp).1).1

theorem lsitesG_spec (so : List DeclT → Nat → PProcess → Except String TSite) {s : Summary}
    (hsta : ∀ st ∈ s.statics, ∃ pos p, so s.decls pos p = .ok st) (hspec : s.SpecOkG so) :
    ∀ ls ∈ s.lsites, ∃ pos p, so s.decls pos p = .ok ls.site := by
  intro ls h
  unfold Summary.lsites at h
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, TFam.lsites] at h
  rcases h with ⟨st, hst, rfl⟩ | ⟨f, hf, hl⟩
  · exact hsta st hst
  · obtain ⟨it, hit, hst⟩ := TItem.lsAtL_site [] f.hdr f.hdr.name f.body ls hl
    exact (hspec f hf).2 it hit ls.site hst

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
    exact Reach_params (ReachE_Reach hr) (lsite_g_notin ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ hls)
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
    fun i => (affOf?_sound h.bndE h.bound hwf.1 (hbag i)).1
  have he : ∀ i : Int, evalInt (env.bindVal h.g i) h.bndE = .ok (h.bound.eval σ) :=
    fun i => (affOf?_sound h.bndE h.bound hwf.1 (hbag i)).2
  rw [Hdr.range_of_wf hwf]
  exact GenItem.expand2_genFor_ascending_flatMap (evalInt_int h.c0) hei he hF
    (fun v hv1 hv2 => hf v ⟨hv1, hv2, by rw [hwf.2]; trivial⟩)

/-- The genvars `gvs` have their values in the environment's `vals` (where `evalAt` reads a genvar). -/
def AgreesV (σ : String → Int) (E : IEnv) (gvs : List String) : Prop := ∀ n ∈ gvs, E.vals.lookup n = some (σ n)

theorem AgreesV.bindVal {σ : String → Int} {E : IEnv} {gvs : List String} (h : AgreesV σ E gvs) (g : String)
    (i : Int) : AgreesV (bindσ g i σ) (E.bindVal g i) (g :: gvs) := by
  intro n hn
  by_cases hng : n = g
  · subst hng; simp
  · rw [vals_lookup_bindVal_ne i hng, bindσ_ne hng]
    exact h n (by simpa [hng] using hn)

mutual
/-- The side conditions of the expansion of an item at the valuation `σ`, the genvars `gvs` bound in `vals` and the
names `ns` agreed on: every loop inside it has its recognized bound (`Hdr.Wf`), a bound naming agreed names other than
its own genvar, and a count within the fuel `F`; every condition its recognized guard, operands reading bound genvars
and agreed parameters with 32-bit values, and the side conditions of the arm it selects; at every valuation of the loops
around them. -/
def TItem.ExpOk (F : Nat) : List String → List String → (String → Int) → TItem → Prop
  | _, _, _, .site _ => True
  | gvs, ns, σ, .loop h _ body => h.Wf ∧ (∀ n ∈ h.bound.names, n ∈ ns ∧ n ≠ h.g) ∧
      (h.bound.eval σ - h.c0).toNat < F ∧
      ∀ j, h.Rng σ j → TItem.ExpOkL F (h.g :: gvs) (h.g :: ns) (bindσ h.g j σ) body
  | gvs, ns, σ, .cond c g thn els => guardOf? c = some g ∧ (∀ n ∈ c.gvLeaves, n ∈ gvs) ∧
      (∀ n ∈ c.pLeaves, n ∈ ns) ∧ (∀ a ∈ g.rngs, -2147483648 ≤ a.eval σ ∧ a.eval σ < 2147483648) ∧
      (g.holds σ → TItem.ExpOkL F gvs ns σ thn) ∧ (¬ g.holds σ → TItem.ExpOkL F gvs ns σ els)

def TItem.ExpOkL (F : Nat) : List String → List String → (String → Int) → List TItem → Prop
  | _, _, _, [] => True
  | gvs, ns, σ, it :: rest => TItem.ExpOk F gvs ns σ it ∧ TItem.ExpOkL F gvs ns σ rest
end

mutual
/-- **An item expands to its closed form** (`GenItem.expand2` of the envelope's item IS `TItem.enumAt`), at any depth:
a loop by `Hdr.expand2`, its body under each index's binding; a condition by `guard_eval`, the arm it selects. -/
theorem TItem.expand2_eq {elems : List (String × Nat)} {F : Nat} :
    ∀ (gvs ns : List String) (σ : String → Int) (E : IEnv) (outer : List Hdr) (cur : Hdr) (blk : String)
      (it : TItem), AgreesV σ E gvs → Agrees σ E ns → it.ExpOk F gvs ns σ →
      it.toGen.expand2 E elems F = .ok (it.enumAt (procB elems) outer cur blk σ E)
  | _, _, _, _, _, _, _, .site st, _, _, _ => by simp [TItem.toGen, TItem.enumAt, procB]
  | gvs, ns, σ, E, outer, cur, blk, .loop hd rc body, hav, hag, hok => by
      simp only [TItem.ExpOk] at hok
      obtain ⟨hwf, hbn, hF, hb⟩ := hok
      rw [TItem.toGen_loop]
      simp only [TItem.enumAt]
      exact Hdr.expand2 hag hwf hbn hF rc (body.map TItem.toGen)
        (fun v hv => TItem.expandL_eq (hd.g :: gvs) (hd.g :: ns) (bindσ hd.g v σ) (E.bindVal hd.g v)
          (outer ++ [cur]) hd hd.name body (hav.bindVal hd.g v) (hag.bindVal hd.g v) (hb v hv))
  | gvs, ns, σ, E, outer, cur, blk, .cond c g thn els, hav, hag, hok => by
      simp only [TItem.ExpOk] at hok
      obtain ⟨hg, hgv, hpv, hr, ht, he⟩ := hok
      have hc := guard_eval (E := E) (σ := σ) hg (fun n hn => hav n (hgv n hn)) (fun n hn => hag n (hpv n hn)) hr
      rw [TItem.toGen_cond]
      simp only [TItem.enumAt]
      by_cases hh : g.holds σ
      · rw [if_pos hh] at hc ⊢
        rw [GenItem.expand2_genIf_of_ne hc (by decide)]
        exact TItem.expandL_eq gvs ns σ E outer _ blk thn hav hag (ht hh)
      · rw [if_neg hh] at hc ⊢
        rw [GenItem.expand2_genIf_of_eq hc]
        exact TItem.expandL_eq gvs ns σ E outer _ blk els hav hag (he hh)

theorem TItem.expandL_eq {elems : List (String × Nat)} {F : Nat} :
    ∀ (gvs ns : List String) (σ : String → Int) (E : IEnv) (outer : List Hdr) (cur : Hdr) (blk : String)
      (its : List TItem), AgreesV σ E gvs → Agrees σ E ns → TItem.ExpOkL F gvs ns σ its →
      expandList2 E elems F (its.map TItem.toGen) = .ok (TItem.enumAtL (procB elems) outer cur blk σ E its)
  | _, _, _, _, _, _, _, [], _, _, _ => by simp [TItem.enumAtL]
  | gvs, ns, σ, E, outer, cur, blk, it :: rest, hav, hag, hok => by
      simp only [TItem.ExpOkL] at hok
      obtain ⟨h1, h2⟩ := hok
      rw [List.map_cons, expandList2_cons_ok (TItem.expand2_eq gvs ns σ E outer cur blk it hav hag h1)
        (TItem.expandL_eq gvs ns σ E outer cur blk rest hav hag h2)]
      rfl
end

/-- A reach through the loops `pre`, then one more index. -/
theorem Reach_snoc : ∀ {pre : List Hdr} {σ0 σ1 : String → Int} {h : Hdr} {j : Int},
    Reach pre σ0 σ1 → h.Rng σ1 j → Reach (pre ++ [h]) σ0 (bindσ h.g j σ1)
  | [], σ0, σ1, h, j, hr, hj => by
      have e : σ1 = σ0 := hr
      subst e
      exact ⟨j, hj, rfl⟩
  | _ :: pre, _, _, _, _, ⟨i, hi, hr⟩, hj => ⟨i, hi, Reach_snoc hr hj⟩

/-- A reach through the loops `outer ++ [cur]` to a valuation where further guards hold reaches it through `cur` under
those guards. -/
theorem Reach_guards : ∀ {outer : List Hdr} {cur : Hdr} {σ0 σ1 : String → Int} {gs : List (Guard × Bool)},
    Reach (outer ++ [cur]) σ0 σ1 → Guard.All gs σ1 → Reach (outer ++ [cur.guards gs]) σ0 σ1
  | [], cur, σ0, σ1, gs, ⟨i, hi, hr⟩, hg => by
      have e : σ1 = bindσ cur.g i σ0 := hr
      subst e
      exact ⟨i, Hdr.rng_guards.mpr ⟨hi, hg⟩, rfl⟩
  | _ :: outer, _, _, _, _, ⟨i, hi, hr⟩, hg => ⟨i, hi, Reach_guards hr hg⟩

/-- The per-loop facts the expansion of an item needs: for a loop header `q.2` under the loops `q.1`, its genvar
distinct from the genvars around it and from the constants `ps`, a bound naming the constants and the genvars around it,
and its count within the fuel at every valuation of the loops around it. -/
def StepFacts (ps : List String) (σ0 : String → Int) (F : Nat) (q : List Hdr × Hdr) : Prop :=
  ((q.1 ++ [q.2]).map (·.g) ++ ps).Nodup ∧
    (∀ n ∈ q.2.bound.names, n ∈ ps ∨ (n ∈ (q.1 ++ [q.2]).map (·.g) ∧ n ≠ q.2.g)) ∧
    Loops.all q.1 σ0 (fun σ' => (q.2.bound.eval σ' - q.2.c0).toNat < F)

/-- The per-condition facts the expansion needs: for a condition under the loops `c.1`, its operands reading the
genvars of those loops and the constants `ps`, their subterms' values 32-bit at every valuation of the loops around it. -/
def CondFacts (ps : List String) (σ0 : String → Int) (c : List Hdr × PExpr × Guard) : Prop :=
  (∀ n ∈ c.2.1.gvLeaves, n ∈ c.1.map (·.g)) ∧ (∀ n ∈ c.2.1.pLeaves, n ∈ ps) ∧
    Loops.all c.1 σ0 (fun σ' => ∀ a ∈ c.2.2.rngs, -2147483648 ≤ a.eval σ' ∧ a.eval σ' < 2147483648)

mutual
/-- The expansion side conditions of an item in the body of `cur` (under `outer`), from the facts about its loop
headers (`StepFacts`) and its conditions (`CondFacts`). -/
theorem TItem.expOk_of {ps : List String} {σ0 : String → Int} {F : Nat} :
    ∀ (outer : List Hdr) (cur : Hdr) (σ1 : String → Int) (gvs ns : List String) (it : TItem),
      Reach (outer ++ [cur]) σ0 σ1 → (∀ n ∈ (outer ++ [cur]).map (·.g), n ∈ gvs) →
      (∀ n, n ∈ (outer ++ [cur]).map (·.g) ++ ps → n ∈ ns) → it.Wf →
      (∀ q ∈ it.stepsAt outer cur, StepFacts ps σ0 F q) → (∀ c ∈ it.condsAt outer cur, CondFacts ps σ0 c) →
      it.ExpOk F gvs ns σ1
  | _, _, _, _, _, .site _, _, _, _, _, _, _ => by simp [TItem.ExpOk]
  | outer, cur, σ1, gvs, ns, .loop hd rc body, hr, hgv, hns, hwf, hst, hcd => by
      rw [TItem.wf_loop] at hwf
      have hq : StepFacts ps σ0 F (outer ++ [cur], hd) := hst _ (by simp [TItem.stepsAt])
      obtain ⟨hnd, hbn, hfu⟩ := hq
      have hgps : hd.g ∉ ps := notin_of_nodup hnd (by simp)
      have hgpre : hd.g ∉ (outer ++ [cur]).map (·.g) := by
        intro hm
        have h2 := (List.nodup_append.mp hnd).1
        rw [List.map_append (l₁ := outer ++ [cur])] at h2
        exact (List.nodup_append.mp h2).2.2 hd.g hm hd.g (by simp) rfl
      simp only [TItem.ExpOk]
      refine ⟨hwf.1, fun n hn => ?_, (Loops.all_iff _ _ _).mp hfu σ1 hr, fun j hj => ?_⟩
      · rcases hbn n hn with h | ⟨h1, h2⟩
        · exact ⟨hns n (List.mem_append_right _ h), fun e => hgps (e ▸ h)⟩
        · refine ⟨hns n (List.mem_append_left _ ?_), h2⟩
          rw [List.map_append (l₁ := outer ++ [cur]), List.mem_append] at h1
          rcases h1 with h1 | h1
          · exact h1
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h1
            exact absurd h1 h2
      · refine TItem.expOkL_of (outer ++ [cur]) hd (bindσ hd.g j σ1) (hd.g :: gvs) (hd.g :: ns) body
          (Reach_snoc hr hj) (fun n hn => ?_) (fun n hn => ?_) hwf.2
          (fun q hq => hst q (by simp only [TItem.stepsAt, List.mem_cons]; exact Or.inr hq))
          (fun c hc => hcd c (by simpa [TItem.condsAt] using hc))
        · rw [List.map_append, List.mem_append] at hn
          rcases hn with hn | hn
          · exact List.mem_cons_of_mem _ (hgv n hn)
          · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hn
            rw [hn]; exact List.mem_cons_self ..
        · rw [List.map_append, List.append_assoc, List.mem_append] at hn
          rcases hn with hn | hn
          · exact List.mem_cons_of_mem _ (hns n (List.mem_append_left _ hn))
          · simp only [List.map_cons, List.map_nil, List.singleton_append, List.mem_cons] at hn
            rcases hn with hn | hn
            · rw [hn]; exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (hns n (List.mem_append_right _ hn))
  | outer, cur, σ1, gvs, ns, .cond c g thn els, hr, hgv, hns, hwf, hst, hcd => by
      rw [TItem.wf_cond] at hwf
      obtain ⟨hgw, hwt, hwe⟩ := hwf
      have hc : CondFacts ps σ0 (outer ++ [cur], c, g) := hcd _ (by simp [TItem.condsAt])
      obtain ⟨hcg, hcp, hcr⟩ := hc
      have hgmap : ∀ gs : List (Guard × Bool), (outer ++ [cur.guards gs]).map (·.g) = (outer ++ [cur]).map (·.g) :=
        fun gs => by simp
      simp only [TItem.ExpOk]
      refine ⟨hgw, fun n hn => hgv n (hcg n hn), fun n hn => hns n (List.mem_append_right _ (hcp n hn)),
        (Loops.all_iff _ _ _).mp hcr σ1 hr, fun hh => ?_, fun hh => ?_⟩
      · refine TItem.expOkL_of outer (cur.guards [(g, true)]) σ1 gvs ns thn
          (Reach_guards hr ⟨hh, trivial⟩) (fun n hn => hgv n (by rwa [hgmap] at hn))
          (fun n hn => hns n (by rwa [hgmap] at hn)) hwt
          (fun q hq => hst q (by simp only [TItem.stepsAt, List.mem_append]; exact Or.inl hq))
          (fun c' hc' => hcd c' (by
            simp only [TItem.condsAt, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hc')))
      · refine TItem.expOkL_of outer (cur.guards [(g, false)]) σ1 gvs ns els
          (Reach_guards hr ⟨hh, trivial⟩) (fun n hn => hgv n (by rwa [hgmap] at hn))
          (fun n hn => hns n (by rwa [hgmap] at hn)) hwe
          (fun q hq => hst q (by simp only [TItem.stepsAt, List.mem_append]; exact Or.inr hq))
          (fun c' hc' => hcd c' (by
            simp only [TItem.condsAt, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hc')))

theorem TItem.expOkL_of {ps : List String} {σ0 : String → Int} {F : Nat} :
    ∀ (outer : List Hdr) (cur : Hdr) (σ1 : String → Int) (gvs ns : List String) (its : List TItem),
      Reach (outer ++ [cur]) σ0 σ1 → (∀ n ∈ (outer ++ [cur]).map (·.g), n ∈ gvs) →
      (∀ n, n ∈ (outer ++ [cur]).map (·.g) ++ ps → n ∈ ns) → (∀ it ∈ its, it.Wf) →
      (∀ q ∈ TItem.stepsAtL outer cur its, StepFacts ps σ0 F q) →
      (∀ c ∈ TItem.condsAtL outer cur its, CondFacts ps σ0 c) → TItem.ExpOkL F gvs ns σ1 its
  | _, _, _, _, _, [], _, _, _, _, _, _ => by simp [TItem.ExpOkL]
  | outer, cur, σ1, gvs, ns, it :: rest, hr, hgv, hns, hwf, hst, hcd => by
      simp only [TItem.ExpOkL]
      exact ⟨TItem.expOk_of outer cur σ1 gvs ns it hr hgv hns (hwf it (List.mem_cons_self ..))
          (fun q hq => hst q (by simp only [TItem.stepsAtL, List.mem_append]; exact Or.inl hq))
          (fun c hc => hcd c (by simp only [TItem.condsAtL, List.mem_append]; exact Or.inl hc)),
        TItem.expOkL_of outer cur σ1 gvs ns rest hr hgv hns (fun y hy => hwf y (List.mem_cons_of_mem _ hy))
          (fun q hq => hst q (by simp only [TItem.stepsAtL, List.mem_append]; exact Or.inr hq))
          (fun c hc => hcd c (by simp only [TItem.condsAtL, List.mem_append]; exact Or.inr hc))⟩
end

/-- Binding a genvar that is not a parameter does not change a parameter-only bound. -/
theorem bound_eval_bind {ps : List String} {h : Hdr} {g : String} {σ : String → Int} {i : Int}
    (hb : ∀ n ∈ h.bound.names, n ∈ ps) (hg : g ∉ ps) :
    h.bound.eval (bindσ g i σ) = h.bound.eval σ :=
  Aff.eval_congr _ _ _ (fun n hn => bindσ_ne (fun heq => hg (by rw [← heq]; exact hb n hn)) i σ)

/-- The path facts of the structural check, for a loop header path. -/
theorem path_facts {s : Summary} (hok : s.StructOk) {p : List Hdr} (hp : p ∈ s.hdrPaths) :
    (p.map (·.g) ++ s.params).Nodup ∧
      ∀ h ∈ p, (∀ n ∈ h.bound.names, n ∈ s.params ∨ (n ∈ p.map (·.g) ∧ n ≠ h.g)) ∧ 0 ≤ h.c0 :=
  hok.2.2.2.2.1 p hp

/-- `Loops.all` is monotone in its predicate. -/
theorem Loops.all_imp : ∀ (hs : List Hdr) (σ : String → Int) {P Q : (String → Int) → Prop},
    (∀ σ', P σ' → Q σ') → Loops.all hs σ P → Loops.all hs σ Q
  | [], σ, _, _, himp, hp => himp σ hp
  | _ :: hs, _, _, _, himp, hp => fun i hi => Loops.all_imp hs _ himp (hp i hi)

/-- **The generate fuel** `F` exceeds the count of every loop, at every valuation of the loops around it; and the
operands of every condition have 32-bit values wherever it is evaluated (the third conjunct of `AutoObl`). -/
def Summary.FuelOk (s : Summary) (σ : String → Int) (F : Nat) : Prop :=
  (∀ q ∈ s.hdrSteps, Loops.all q.1 σ fun σ' => (q.2.bound.eval σ' - q.2.c0).toNat < F) ∧
  (∀ c ∈ s.condSteps, Loops.all c.1 σ fun σ' =>
    ∀ a ∈ c.2.2.rngs, -2147483648 ≤ a.eval σ' ∧ a.eval σ' < 2147483648)

/-- The fuel of the instantiation (`PDesign.surfaceFuel`) is enough, by the third conjunct of `AutoObl`. -/
theorem Summary.fuelOk_of_auto {s : Summary} {σ : String → Int} {args : List Int} (h : s.AutoObl σ args) :
    s.FuelOk σ (PDesign.surfaceFuel args) :=
  ⟨fun q hq => Loops.all_imp q.1 σ (fun _ h' => surfaceFuel_gt args _ h') (h.2.2.1 q hq), h.2.2.2⟩

/-- **A top-level generate loop expands to the closed form `TFam.enum`**, at any depth of nesting, with conditional
generate constructs. An inner loop's bound may name the genvars of the loops around it: it is read under their binding,
and its fuel is owed at every valuation of them (`FuelOk`). -/
theorem fam_expand2 {s : Summary} {σ : String → Int} {env : IEnv} {elems : List (String × Nat)}
    {F : Nat} (hag : Agrees σ env s.params) (hok : s.StructOk) (hfuel : s.FuelOk σ F)
    {f : TFam} (hf : f ∈ s.fams) (hwf : f.Wf) :
    f.toGen.expand2 env elems F = .ok (TFam.enum (procB elems) σ env f) := by
  have hp1 : [f.hdr] ∈ s.hdrPaths := by
    unfold Summary.hdrPaths Summary.hdrSteps
    simp only [List.mem_map, List.mem_flatMap, List.mem_cons]
    exact ⟨([], f.hdr), ⟨f, hf, Or.inl rfl⟩, rfl⟩
  have hs1 : (([] : List Hdr), f.hdr) ∈ s.hdrSteps := by
    unfold Summary.hdrSteps
    simp only [List.mem_flatMap, List.mem_cons]
    exact ⟨f, hf, Or.inl rfl⟩
  obtain ⟨hnd1, hb1⟩ := path_facts hok hp1
  have hg1 : f.hdr.g ∉ s.params := notin_of_nodup hnd1 (by simp)
  have hbp : ∀ n ∈ f.hdr.bound.names, n ∈ s.params := by
    intro n hn
    rcases (hb1 f.hdr (List.mem_singleton_self _)).1 n hn with h | ⟨h1, h2⟩
    · exact h
    · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h1
      exact absurd h1 h2
  have hbn : ∀ n ∈ f.hdr.bound.names, n ∈ s.params ∧ n ≠ f.hdr.g :=
    fun n hn => ⟨hbp n hn, fun heq => hg1 (by rw [← heq]; exact hbp n hn)⟩
  have hsteps : ∀ q ∈ TItem.stepsAtL [] f.hdr f.body, StepFacts s.params σ F q := by
    intro q hq
    have hq' : q ∈ s.hdrSteps := by
      unfold Summary.hdrSteps
      simp only [List.mem_flatMap, List.mem_cons]
      exact ⟨f, hf, Or.inr hq⟩
    have hp : q.1 ++ [q.2] ∈ s.hdrPaths := List.mem_map.mpr ⟨q, hq', rfl⟩
    obtain ⟨hnd, hb⟩ := path_facts hok hp
    exact ⟨hnd, (hb q.2 (by simp)).1, hfuel.1 q hq'⟩
  have hconds : ∀ c ∈ TItem.condsAtL [] f.hdr f.body, CondFacts s.params σ c := by
    intro c hc
    have hc' : c ∈ s.condSteps := by
      unfold Summary.condSteps
      simp only [List.mem_flatMap]
      exact ⟨f, hf, hc⟩
    obtain ⟨h1, h2⟩ := hok.2.2.2.2.2.2.2.2 c hc'
    exact ⟨h1, h2, hfuel.2 c hc'⟩
  have := Hdr.expand2 hag hwf.1 hbn (hfuel.1 _ hs1) f.rc (f.body.map TItem.toGen)
    (f := fun i => TItem.enumAtL (procB elems) [] f.hdr f.hdr.name (bindσ f.hdr.g i σ) (env.bindVal f.hdr.g i)
      f.body)
    (fun v hv => TItem.expandL_eq [f.hdr.g] (f.hdr.g :: s.params) (bindσ f.hdr.g v σ) (env.bindVal f.hdr.g v)
      [] f.hdr f.hdr.name f.body (fun n hn => by simp at hn; subst hn; simp) (hag.bindVal f.hdr.g v)
      (TItem.expOkL_of [] f.hdr (bindσ f.hdr.g v σ) [f.hdr.g] (f.hdr.g :: s.params) f.body
        ⟨v, hv, rfl⟩ (fun n hn => by simpa using hn) (fun n hn => by simpa using hn) hwf.2 hsteps hconds))
  exact this


/-- The finite family expansion, from the well-formedness of the families alone (the only part of the spec the
expansion reads): the core of `fams_expand2` (over `SpecOk`) and `fams_expand2P` (over `SpecOkP`). -/
theorem fams_expand2W {s : Summary} {σ : String → Int} {env : IEnv} {elems : List (String × Nat)}
    {F : Nat} (hag : Agrees σ env s.params) (hok : s.StructOk) (hwf : ∀ f ∈ s.fams, f.Wf)
    (hfuel : s.FuelOk σ F) :
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
    (hfuel : s.FuelOk σ F) :
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
  refine ⟨ctx_of_env hsd hdim hag hdecl, ?_⟩
  have hfuel := Summary.fuelOk_of_auto hauto
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
