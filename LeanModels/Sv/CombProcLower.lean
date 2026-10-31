import LeanModels.Sv.CombProcSummary
import LeanModels.Sv.CombEqThm

/-!
# `always_comb` bodies in the `sv_comb` fragment, stage 4: soundness of the proc-aware summary (WP-G, G2.2)

`CombViewSound.lean` proves that a design `m` instantiated from a summary REALIZES it: every process of `m`
is an `assign` to the promised window reading only promised windows (`Realized`). For a summary with a
procedural site (`PDesign.summaryP`, `CombProcSummary.lean`) the process of the instantiated design `m` is the
guarded `always_comb`; the settle theory (`CombDesign`, `Acyclic`, `CombEqs`) is about its LOWERING
`d' = m.lowerComb` (`Comb2Proc.lean`), whose processes are assigns again. This file proves, for the first
fragment (`CombProc.lean`):

| theorem | statement |
|---|---|
| `pairs_descL` | for every located site: the process `q.2` lowers (`lowerComb`) to an assign `r` that `DescL`-describes the footprint (an old site: as before; a proc site: `assign {W} = {E}` with `E` reading only the site's promised windows), and `LowKind` says how `r` relates to `q.2` |
| `Summary.soundL` | `summaryP` ok + the parameter stage + the structural / auto / in-range / **no-self-read** obligations ⇒ `instantiate2` succeeds with `m`, `m.lowerComb = some d'`, `d'` realizes the summary (`RealizedL`) and `LowRel m d'` relates the two process lists position by position |
| `realizedL_comb`, `realizedL_acyclic` | the comb profile and acyclicity of `d'` from `RealizedL` (the proofs of `realized_comb` / `realized_acyclic` with `descL_facts` for `Desc`) |
| `driversOk_of_lowered`, `PDesign.instantiateGD2_of_lowered` | the one-driver rule of `m` (so `name.sem N = m`, the driver guard passes) from the comb profile of `d'` and `LowRel` |
| `struct_of_summaryL` (+ `struct_of_rankL`, `struct_of_lexL`) | **`∃ d', (name.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d'`** |

## Soundness story

Nothing is trusted: every theorem is kernel-checked plain Lean (axioms: `propext`, `Classical.choice`,
`Quot.sound` only, pinned at the end). The new obligation is `Summary.NoSelfRead`: for every procedural site,
at every valuation of its loops, no read access of the body overlaps the window the body writes. It is what
`lower_site` (`CombProc.lean`) needs for the self-read guard and for `selfReadFree`; the tactic closes it by
`omega` like the other index obligations. A body that fails it is refused by the loader's own guard
(`AlwaysComb:self-read`), so the obligation is not an extra trust assumption but the proof-side reflection of
that check.

COPY NOTE: `pairs_descL`, `Summary.soundL`, `realizedL_comb`, `realizedL_acyclic` and `fams_expand2P` are
copies of the old chain (`G22-NOTE.md` section 3 lists them with the old names); the old chain is untouched.
-/

namespace LeanModels.Sv
namespace CombView
open CombEq CombProc

/-! ## `RdOK` for the lowered expression -/

theorem RdOK.mono {σ : String → Int} {rs rs' : List Acc} {x : Expr2} (h : RdOK σ rs x)
    (hs : ∀ a ∈ rs, a ∈ rs') : RdOK σ rs' x := by
  refine ⟨h.1, fun r hr => ?_, fun i hi => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (h.2.1 r hr)
    exact List.mem_map.mpr ⟨a, hs a ha, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (h.2.2 i hi)
    exact List.mem_map.mpr ⟨a, hs a ha, rfl⟩

theorem RdOK.ifGuard {σ : String → Int} {rs : List Acc} {c : Expr2} (h : RdOK σ rs c) :
    RdOK σ rs (Expr2.ifGuard c) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun r hr => ?_, fun i hi => ?_⟩
  · simp [Expr2.ifGuard, Expr2.unsupportedFree, h1]
  · simp only [Expr2.ifGuard, Expr2.reads, List.append_nil] at hr
    exact h2 r hr
  · simp only [Expr2.ifGuard, Expr2.idents, List.append_nil] at hi
    exact h3 i hi

theorem RdOK.ternary {σ : String → Int} {ra rb rc : List Acc} {g a b : Expr2} (hg : RdOK σ ra g)
    (ha : RdOK σ rb a) (hb : RdOK σ rc b) : RdOK σ (ra ++ rb ++ rc) (.ternary g a b) := by
  obtain ⟨g1, g2, g3⟩ := hg
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨?_, fun r hr => ?_, fun i hi => ?_⟩
  · simp [Expr2.unsupportedFree, g1, a1, b1]
  · simp only [Expr2.reads, List.mem_append] at hr
    simp only [List.map_append, List.mem_append]
    rcases hr with (h | h) | h
    · exact Or.inl (Or.inl (g2 r h))
    · exact Or.inl (Or.inr (a2 r h))
    · exact Or.inr (b2 r h)
  · simp only [Expr2.idents, List.mem_append] at hi
    simp only [List.map_append, List.mem_append]
    rcases hi with (h | h) | h
    · exact Or.inl (Or.inl (g3 i h))
    · exact Or.inl (Or.inr (a3 i h))
    · exact Or.inr (b3 i h)

section site
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- **The lowered right-hand side reads only the site's promised accesses** (`RdOK`): the guard `(|c) === 1`,
the two branches (or one, when they are syntactically equal) and the `resize`s of the leaves. -/
theorem low_rdOK (C : Ctx σ E elems DW DG EW ns) {ds : List DeclT} {tg : Acc} :
    ∀ (ptr : PTR), ptr.Ok ds tg → (∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a) → ∀ tw,
      RdOK σ ptr.rds ((ptr.pt.low E elems tw).low tw)
  | .leafL t v rs, hok, hacc, tw => by
      simpa [PTR.pt, PT.low, PTree.low, PTR.rds] using RdOK.resize tw (rhs_ok C hok.2.1 hacc tw)
  | .leafW n v rs, hok, hacc, tw => by
      simpa [PTR.pt, PT.low, PTree.low, PTR.rds] using RdOK.resize tw (rhs_ok C hok.2.1 hacc tw)
  | .ite c rc a b, ⟨⟨hc, _⟩, ha, hb⟩, hacc, tw => by
      have hcr := inst_rd C c rc hc (fun x hx => hacc x (by simp [PTR.rds, hx])) none
      have iha := low_rdOK C a ha (fun x hx => hacc x (by simp [PTR.rds, hx])) tw
      have ihb := low_rdOK C b hb (fun x hx => hacc x (by simp [PTR.rds, hx])) tw
      simp only [PTR.pt, PT.low, PTree.low, Expr2.joinIte]
      split
      · exact iha.mono (fun x hx => by simp [PTR.rds, hx])
      · exact RdOK.ternary (RdOK.ifGuard hcr) iha ihb
  | .blk a, hok, hacc, tw => by
      simpa [PTR.pt, PT.low, PTree.low, PTR.rds] using low_rdOK C a hok hacc tw

/-- **The instantiated procedural process IS the guarded tree statement** (the self-read guard admits it, so
`combGuardProc` is the identity): the companion of `lower_site` that keeps the process (and so its driven
windows, `drvWins_tree`) rather than its lowering. -/
theorem proc_site_eq (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n)) {d : Design2}
    (hd : ∀ n, d.declWidth n = DW n) {ds : List DeclT} {tg : Acc}
    (hatg : AccOK σ DW DG EW ns tg)
    (hin : (tg.win σ dw).2.1 + (tg.win σ dw).2.2 ≤ dw tg.name)
    (ptr : PTR) (hok : ptr.Ok ds tg) (hacc : ∀ a ∈ ptr.rds, AccOK σ DW DG EW ns a)
    (hself : ∀ a ∈ ptr.rds, (a.rd σ).overlaps (tg.win σ dw) = false) :
    instProcess2 E elems ptr.pt.toProc =
      .alwaysComb ((ptr.pt.low E elems (tg.win σ dw).2.2).toStmt (tg.lhs σ)) := by
  rw [instProcess2_tree ptr.pt (tree_tgt C hdw hatg ptr hok)]
  obtain ⟨hsw, hm, hr⟩ := tgt_facts C hdw hd hatg hin
  exact combGuardProc_of_admits (combAdmits_tree _ (tg.lhs σ) (tg.win σ dw) hm hr _
    (noRdW_of_noRead _ _ _ (low_idxFree C hdw ptr hok hacc _)
      (low_noRead C (tg.win σ dw) ptr hok hacc hself _)))

end site

/-! ## The lowered realization -/

/-- A pair `(footprint, process)` of the LOWERED design: an old assign site (`Desc`), or a proc site's lowered
process, the continuous assign of the site's window. -/
def DescL (names : List String) (si : SiteInst) (p : Process2) : Prop :=
  Desc names si p ∨
    ∃ e, p = .assign (.concat [si.win.lhs]) e ∧ (∀ r ∈ e.reads, r ∈ si.rd) ∧
      e.unsupportedFree = true ∧ ∀ x ∈ e.idents, x ∈ names

/-- `d'` realizes the summary at `σ` in the lowered sense: the declarations are the summary's and the process
list is the closed-form `Summary.pairs` with each process replaced by its lowering. -/
def RealizedL (s : Summary) (σ : String → Int) (d' : Design2) : Prop :=
  d'.decls.toList = s.decls.map (DeclT.toDecl σ) ∧
  ∃ (E : IEnv) (L : List (SiteInst × Process2)), L.map Prod.fst = s.insts σ E ∧
    d'.processes.toList = L.map Prod.snd ∧ ∀ q ∈ L, DescL s.declNames q.1 q.2

/-- The process is an `always_comb` (so a procedural site). -/
def isCombProc : PProcess → Bool
  | .alwaysComb _ => true
  | _ => false

/-- The no-self-read obligation of the proc sites (the summary's `noSelfRead_k`): no read access of the body
overlaps the window the body writes. -/
def Summary.NoSelfRead (s : Summary) (σ : String → Int) : Prop :=
  ∀ ls ∈ s.lsites, isCombProc ls.site.proc = true →
    Loops.all ls.hdrs σ fun σ' =>
      ∀ r ∈ ls.site.rds, (r.rd σ').overlaps (ls.site.tgt.win σ' (s.dw σ)) = false

/-- The lowered process of the list: the process itself when it does not lower. -/
def lowP (m : Design2) (p : Process2) : Process2 := (p.lowerComb m).getD p

/-- The lowered target `{W}` has the one window `W`, in every design. -/
theorem windows_concat_win (d : Design2) (W : Win) : (Lhs2.concat [W.lhs]).windows? d = some [W] := by
  obtain ⟨n, lo, w⟩ := W
  simp [Lhs2.listWindows?, Win.lhs]

theorem wins_concat_win (d : Design2) (W : Win) : (Lhs2.concat [W.lhs]).wins d = [W] :=
  Lhs2.wins_of_windows? (windows_concat_win d W)

/-- How the lowered process `r` of `q` relates to `q`: it is `q` (an assign), or `q` is a procedural body whose
driven windows all match the window `W` of the footprint, and `r` is the assign of that window. -/
def LowKind (M : Design2) (si : SiteInst) (q r : Process2) : Prop :=
  r = q ∨ ∃ (body : Stmt2) (e : Expr2), q = .alwaysComb body ∧ r = .assign (.concat [si.win.lhs]) e ∧
    ∀ x ∈ body.drvWins, DrvWin.Matches M x si.win

/-- The process lists of the design and of its lowering, position by position: the same process, or the
procedural body and the assign of the window its driven windows match. This is the hypothesis of
`driversOk_of_lowered`. -/
def LowRel (M d' : Design2) : Prop :=
  M.processes.toList.length = d'.processes.toList.length ∧
  ∀ (i : Nat) (h1 : i < M.processes.toList.length) (h2 : i < d'.processes.toList.length),
    M.processes.toList[i] = d'.processes.toList[i] ∨
    ∃ (body : Stmt2) (t : Lhs2) (e : Expr2), M.processes.toList[i] = .alwaysComb body ∧
      d'.processes.toList[i] = .assign t e ∧
      ∀ x ∈ body.drvWins, ∃ a ∈ t.wins d', DrvWin.Matches d' x a

theorem lowerProcs_map {d : Design2} :
    ∀ {ps : List Process2}, (∀ p ∈ ps, ∃ r, p.lowerComb d = some r) →
      d.lowerProcs ps = some (ps.map (lowP d))
  | [], _ => rfl
  | p :: ps, h => by
      obtain ⟨r, hr⟩ := h p (List.mem_cons_self ..)
      have := lowerProcs_map (d := d) (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp [Design2.lowerProcs, hr, this, lowP]

/-! ## One located site, lowered -/

theorem pairs_descL {s : Summary} {args : List Int} {σ : String → Int} {envD : IEnv}
    {elems : List (String × Nat)} {M : Design2}
    (hdecl : M.decls.toList = s.decls.map (DeclT.toDecl σ))
    (C : Ctx σ envD elems (s.DW σ) (s.DG σ) (s.EW σ) s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hself : s.NoSelfRead σ)
    (hsites : ∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site) :
    ∀ q ∈ s.pairs σ envD elems,
      ∃ r, q.2.lowerComb M = some r ∧ DescL s.declNames q.1 r ∧ LowKind M q.1 q.2 r := by
  intro q hq
  unfold Summary.pairs at hq
  rw [mem_enum_E] at hq
  obtain ⟨ls, hls, σ', E', hr, rfl⟩ := hq
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl', hacc, hkeys⟩ := hok
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
    refine ⟨?_, accGeom_of hpar hdecl' (hacc ls hls a ha) (hInR a ha) (hauto2 ls hls a ha), ?_⟩
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
  obtain ⟨pos, p, hp⟩ := hsites ls hls
  rcases siteOfP?_cases hp with hp0 | ⟨b, tg, ptr, rfl, htree, hst⟩
  · -- an old site: the process is an assign, lowering keeps it
    have h := site_desc C' hnm hp0 hso (si := ls.inst σ' (s.dw σ)) rfl rfl
    rw [← siteOf?_proc hp0] at h
    obtain ⟨e, hpe, -⟩ := id h
    refine ⟨instProcess2 E' elems ls.site.proc, ?_, Or.inl h, Or.inl rfl⟩
    rw [hpe]
    rfl
  · -- a procedural site: `lower_site`
    have hproc : ls.site.proc = .alwaysComb b := congrArg TSite.proc hst
    have htg : ls.site.tgt = tg := congrArg TSite.tgt hst
    have hrds : ls.site.rds = ptr.rds := congrArg TSite.rds hst
    obtain ⟨hb, hpok⟩ := treeStmt?_spec s.decls b tg ptr htree
    have hproc2 : instProcess2 E' elems ls.site.proc = instProcess2 E' elems ptr.pt.toProc := by
      rw [hproc, PT.toProc, hb]
    have hatg := hso ls.site.tgt (List.mem_cons_self ..)
    have haccP : ∀ a ∈ ptr.rds,
        AccOK σ' (s.DW σ) (s.DG σ) (s.EW σ) (ls.hdrs.map (·.g) ++ s.params) a :=
      fun a ha => hso a (List.mem_cons_of_mem _ (by rw [hrds]; exact ha))
    have hg : AccGeom σ' (s.DG σ) (s.EW σ) ls.site.tgt :=
      accGeom_of hpar hdecl' (hacc ls hls _ (List.mem_cons_self ..)) hin'.1
        (hauto2 ls hls _ (List.mem_cons_self ..))
    have hdn : (s.find ls.site.tgt.name).isSome = true :=
      find_isSome_of_mem (hnames ls hls _ (by simp [TSite.names]))
    obtain ⟨-, hle⟩ := acc_win_facts (σd := σ) hdn hg
      (fun n x h => by have := hin'.2; rw [h] at this; exact this)
    have hself1 := (Loops.all_iff _ _ _).mp (hself ls hls (by rw [hproc]; rfl)) σ' (ReachE_Reach hr)
    have hself' : ∀ a ∈ ptr.rds,
        (a.rd σ').overlaps (ls.site.tgt.win σ' (s.dw σ)) = false :=
      fun a ha => hself1 a (by rw [hrds]; exact ha)
    have hpok' : ptr.Ok s.decls ls.site.tgt := by rw [htg]; exact hpok
    have hL := lower_site C' (dw := s.dw σ) (fun n h => dw_some n h) (declWidth_eq hdecl) hatg hle
      ptr hpok' haccP hself'
    have hlow := low_rdOK C' ptr hpok' haccP (ls.site.tgt.win σ' (s.dw σ)).2.2
    have hrd := RdOK.concat_cons hlow RdOK.concat_nil
    have hP := proc_site_eq C' (dw := s.dw σ) (fun n h => dw_some n h) (declWidth_eq hdecl) hatg hle
      ptr hpok' haccP hself'
    rw [hproc2, hL, hP]
    refine ⟨_, rfl, Or.inr ⟨_, rfl, ?_, hrd.1, ?_⟩, Or.inr ⟨_, _, rfl, rfl, ?_⟩⟩
    · intro r hr'
      have := hrd.2.1 r hr'
      show r ∈ ls.site.rds.map (Acc.rd σ')
      rw [hrds]
      simpa using this
    · intro x hx
      obtain ⟨r, hr', rfl⟩ := List.mem_map.mp (by simpa using hrd.2.2 x hx)
      exact hnm _ (haccP r hr').1
    · intro x hx
      have hx1 := drvWins_tree (ls.site.tgt.lhs σ') _ x hx
      have hw := acc_windows (σs := σ') hdecl ls.site.tgt hdn
      obtain ⟨a, ha, hm⟩ := (Lhs2.drvWins_matchList _ _ hw).exists_mem x hx1
      rw [List.mem_singleton] at ha
      subst ha
      exact hm

/-! ## The finite family expansion over `SpecOkP` -/

theorem fams_expand2P {s : Summary} {σ : String → Int} {env : IEnv} {elems : List (String × Nat)}
    {F : Nat} (hag : Agrees σ env s.params) (hok : s.StructOk) (hspec : s.SpecOkP)
    (hfuel : ∀ p ∈ s.hdrPaths, ∀ h ∈ p, (h.bound.eval σ - h.c0).toNat < F) :
    ∀ (fs : List TFam), (∀ f ∈ fs, f ∈ s.fams) →
      expandList2 env elems F (fs.map TFam.toGen) =
        .ok (fs.flatMap fun f => TFam.enum (procB elems) σ env f)
  | [], _ => by simp
  | f :: fs, hfs => by
      have hf : f ∈ s.fams := hfs f (List.mem_cons_self ..)
      rw [List.map_cons, expandList2_cons_ok (fam_expand2 hag hok hfuel hf (hspec f hf).1)
        (fams_expand2P hag hok hspec hfuel fs (fun g hg => hfs g (List.mem_cons_of_mem _ hg))),
        List.flatMap_cons]

/-! ## `Summary.soundL` -/

/-- **`Summary.soundL`: the proc-aware family summary is sound against `PDesign.instantiate2` followed by
the lowering.** The instantiation succeeds with `m`, `m` lowers to `d'`, and `d'` realizes the summary in
the lowered sense: its declarations are the summary's and its processes are the summary's footprints, each
with an assign (an old site as instantiated, a proc site as `assign {W} = {E}`). -/
theorem Summary.soundL {d : PDesign} {s : Summary} (hs : d.summaryP = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hself : s.NoSelfRead σ) :
    ∃ (m d' : Design2) (E : IEnv) (elems : List (String × Nat)),
      d.instantiate2 args (PDesign.surfaceFuel args) = .ok m ∧ m.lowerComb = some d' ∧
      m.decls.toList = s.decls.map (DeclT.toDecl σ) ∧ d'.decls = m.decls ∧ LowRel m d' ∧
      RealizedL s σ d' ∧
      d'.processes.toList = (s.pairs σ E elems).map (fun q => lowP m q.2) ∧
      Ctx σ E elems (s.DW σ) (s.DG σ) (s.EW σ) s.params ∧
      (∀ q ∈ s.pairs σ E elems,
        ∃ r, q.2.lowerComb m = some r ∧ DescL s.declNames q.1 r ∧ LowKind m q.1 q.2 r) ∧
      (∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site) := by
  obtain ⟨hloc, hens, hoth, hpar, hsd, hsts, hgen, hspec⟩ := summaryP_spec hs
  have hok' := hok
  obtain ⟨hnodup, hnames, hinput, haff, hpaths, hdecl, hacc, hkeys⟩ := hok'
  have hagd : ∀ dt ∈ s.decls, ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n) :=
    fun dt hdt n hn => hag n (hdecl dt hdt n hn)
  have h2 := buildDecls_summary (σ := σ) d.decls s.decls hsd env hagd
  have h3 := buildElems_summary (σ := σ) d.decls s.decls hsd env hagd
  have hdim := paramEnv2_dims h1
  have C := ctx_of_env hsd hdim hag hdecl
  obtain ⟨hproc, hsites0⟩ := sitesOfP?_spec hsts
  have hsites := lsitesP_spec hsites0 hspec
  have hfuel : ∀ p ∈ s.hdrPaths, ∀ h ∈ p,
      (h.bound.eval σ - h.c0).toNat < PDesign.surfaceFuel args :=
    fun p hp h hh => surfaceFuel_gt args _ (hauto.2.2 p hp h hh)
  have h4 : expandList2 (env.withDecls (s.decls.map (DeclT.toDecl σ)))
      (s.decls.map fun dt => (dt.name, dt.elemW σ)) (PDesign.surfaceFuel args) d.generates =
      .ok (s.fams.flatMap fun f => TFam.enum
        (procB (s.decls.map fun dt => (dt.name, dt.elemW σ))) σ
        (env.withDecls (s.decls.map (DeclT.toDecl σ))) f) := by
    rw [hgen]
    exact fams_expand2P (env := env.withDecls (s.decls.map (DeclT.toDecl σ)))
      (elems := s.decls.map fun dt => (dt.name, dt.elemW σ)) hag hok hspec hfuel
      s.fams (fun f hf => hf)
  obtain ⟨M, hMi, hMd, hMp⟩ : ∃ M, d.instantiate2 args (PDesign.surfaceFuel args) = .ok M ∧
      M.decls.toList = s.decls.map (DeclT.toDecl σ) ∧
      M.processes.toList = (s.pairs σ (env.withDecls (s.decls.map (DeclT.toDecl σ)))
        (s.decls.map fun dt => (dt.name, dt.elemW σ))).map Prod.snd := by
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
  have hC := pairs_descL hMd C hok hauto hin hself hsites
  obtain ⟨E0, hE0⟩ : ∃ E0, E0 = env.withDecls (s.decls.map (DeclT.toDecl σ)) := ⟨_, rfl⟩
  obtain ⟨el0, hel0⟩ : ∃ el0, el0 = s.decls.map (fun dt => (dt.name, dt.elemW σ)) := ⟨_, rfl⟩
  rw [← hE0, ← hel0] at hMp hC
  have hlow : M.lowerComb = some { M with processes :=
      ((s.pairs σ E0 el0).map fun q => lowP M q.2).toArray } := by
    unfold Design2.lowerComb
    rw [hMp, lowerProcs_map (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨r, hr, -⟩ := hC q hq
      exact ⟨r, hr⟩)]
    simp [List.map_map, Function.comp_def]
  have hrel : LowRel M { M with processes := ((s.pairs σ E0 el0).map fun q => lowP M q.2).toArray } := by
    refine ⟨by simp [hMp], fun i h1 h2 => ?_⟩
    have hi : i < (s.pairs σ E0 el0).length := by simpa [hMp] using h1
    have e1 : M.processes.toList[i] = ((s.pairs σ E0 el0)[i]).2 := by simp [hMp]
    have e2 : ({ M with processes := ((s.pairs σ E0 el0).map fun q => lowP M q.2).toArray } :
        Design2).processes.toList[i] = lowP M ((s.pairs σ E0 el0)[i]).2 := by simp
    obtain ⟨r, hr, -, hk⟩ := hC _ (List.getElem_mem hi)
    have hlp : lowP M ((s.pairs σ E0 el0)[i]).2 = r := by simp [lowP, hr]
    rw [e1, e2, hlp]
    rcases hk with hk | ⟨body, e, hq, hrr, hm⟩
    · exact Or.inl hk.symm
    · refine Or.inr ⟨body, _, e, hq, hrr, fun x hx => ⟨_, ?_, hm x hx⟩⟩
      · rw [wins_concat_win]; exact List.mem_singleton_self _
  have hreal : RealizedL s σ { M with processes :=
      ((s.pairs σ E0 el0).map fun q => lowP M q.2).toArray } := by
    refine ⟨hMd, E0, (s.pairs σ E0 el0).map fun q => (q.1, lowP M q.2), ?_, ?_, ?_⟩
    · rw [List.map_map]
      exact Summary.pairs_map_fst ..
    · simp [List.map_map, Function.comp_def]
    · intro q hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      obtain ⟨r, hr, hD, -⟩ := hC q0 hq0
      simpa [lowP, hr] using hD
  have hC' : Ctx σ E0 el0 (s.DW σ) (s.DG σ) (s.EW σ) s.params := by
    rw [hE0, hel0]; exact C
  exact ⟨M, _, E0, el0, hMi, hlow, hMd, rfl, hrel, hreal, by simp, hC', hC, hsites⟩

/-! ## Facts about the lowered realization -/

/-- The facts the structural proofs read off one lowered footprint, for an old site and a proc site alike: the
lowered process is an assign whose target has the one window of the footprint, which is positive and not an
input; its right-hand side is loud-free and reads only the footprint's promised windows and declared names. -/
theorem descL_facts {s : Summary} {σ : String → Int} {E : IEnv} {args : List Int} {d' : Design2}
    (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hdecl : d'.decls.toList = s.decls.map (DeclT.toDecl σ)) {a : SiteInst}
    (ha : a ∈ s.insts σ E) {p : Process2} (hD : DescL s.declNames a p) :
    ∃ (t : Lhs2) (e : Expr2), p = .assign t e ∧ t.windows? d' = some [a.win] ∧ 0 < a.win.2.2 ∧
      a.win.1 ∉ s.inputNames ∧ e.unsupportedFree = true ∧ (∀ r ∈ e.reads, r ∈ a.rd) ∧
      ∀ x ∈ e.idents, x ∈ s.declNames := by
  obtain ⟨-, hwin, hpos, hni⟩ := inst_facts hok hauto hin hdecl ha
  rcases hD with ⟨e, hpe, hrd, hfree, hid⟩ | ⟨e, hpe, hrd, hfree, hid⟩
  · exact ⟨a.tgt, e, hpe, hwin, hpos, hni, hfree, hrd, hid⟩
  · exact ⟨_, e, hpe, windows_concat_win d' a.win, hpos, hni, hfree, hrd, hid⟩

/-- `RealizedL` + obligations ⇒ the comb profile of the lowered design (and positive write windows). -/
theorem realizedL_comb {s : Summary} {σ : String → Int} {d' : Design2} {args : List Int}
    (hR : RealizedL s σ d') (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hd : s.DisjObl σ) :
    CombDesign d' ∧ ∀ i n lo w, d'.Writes i (n, lo, w) → 0 < w := by
  obtain ⟨hdecl, E, L, hLf, hP, hdesc⟩ := hR
  have hok' := hok
  obtain ⟨hnodup, -, -, -, -, -, -, -⟩ := hok'
  have hget : ∀ (i : Nat) (p : Process2), d'.processes[i]? = some p ↔
      ∃ q : SiteInst × Process2, L[i]? = some q ∧ p = q.2 := by
    intro i p
    rw [← Array.getElem?_toList, hP, List.getElem?_map]
    cases hL : L[i]? with
    | none => simp
    | some q => simp [eq_comm]
  have hmemL : ∀ q : SiteInst × Process2, q ∈ L → q.1 ∈ s.insts σ E :=
    fun q hq => hLf ▸ List.mem_map.2 ⟨q, hq, rfl⟩
  have hdf := fun (q : SiteInst × Process2) (hq : q ∈ L) =>
    descL_facts (E := E) hok hauto hin hdecl (hmemL q hq) (hdesc q hq)
  have hpw : L.Pairwise fun p q => Win.overlaps p.1.win q.1.win = false := by
    have h1 : (L.map Prod.fst).Pairwise (fun a b => a.id ≠ b.id) := by
      rw [hLf]; exact ids_pairwise hok
    rw [List.pairwise_map] at h1
    exact h1.imp_of_mem (fun {p q} hp hq hne => insts_disj hd _ (hmemL p hp) _ (hmemL q hq) hne)
  have hwr : ∀ {i wn}, d'.Writes i wn → ∃ q, L[i]? = some q ∧ wn = q.1.win := by
    rintro i wn ⟨t, e, hp, hw⟩
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨t', e', hpe, hwin, -⟩ := hdf q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    refine ⟨q, hq, ?_⟩
    rw [Lhs2.wins_of_windows? hwin] at hw
    simpa using hw
  have hpos : ∀ i n lo w, d'.Writes i (n, lo, w) → 0 < w := by
    intro i n lo w hw
    obtain ⟨q, hq, hwq⟩ := hwr hw
    obtain ⟨-, -, -, -, hp, -⟩ := hdf q (List.mem_of_getElem? hq)
    obtain ⟨-, -, hw'⟩ := win_eq hwq
    rw [hw']
    exact hp
  refine ⟨?_, hpos⟩
  refine
    { nodup := ?_, assign := ?_, inWidth := ?_, notInput := ?_, disjoint := ?_,
      selfDisjoint := ?_, rhsFree := ?_, rhsDeclared := ?_, initWidth := ?_,
      inFourState := ?_ }
  · rw [hdecl]
    simpa [List.map_map, Function.comp_def, Summary.declNames] using hnodup
  · intro i p hp
    obtain ⟨q, hq, rfl⟩ := (hget i p).mp hp
    obtain ⟨t, e, hpe, hwin, -⟩ := hdf q (List.mem_of_getElem? hq)
    exact ⟨t, e, [q.1.win], hpe, hwin⟩
  · intro i n lo w hw
    obtain ⟨q, hq, hwq⟩ := hwr hw
    obtain ⟨dw, hdw, hle⟩ := inrange_insts hok hauto hin (hmemL q (List.mem_of_getElem? hq))
    obtain ⟨h1, h2, h3⟩ := win_eq hwq
    refine ⟨dw, by rw [declWidth_eq hdecl, h1]; exact hdw, ?_⟩
    rw [h2, h3]
    exact hle
  · intro n hn
    obtain ⟨i, lo, w, hw⟩ := hn
    obtain ⟨q, hq, hwq⟩ := hwr hw
    obtain ⟨-, -, -, -, -, hni, -⟩ := hdf q (List.mem_of_getElem? hq)
    obtain ⟨h1, -, -⟩ := win_eq hwq
    rw [Realized.inputNames hdecl, h1]
    exact hni
  · intro i j wi wj hij hi hj
    obtain ⟨qi, hqi, rfl⟩ := hwr hi
    obtain ⟨qj, hqj, rfl⟩ := hwr hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact pairwise_getElem? hpw h hqi hqj
    · rw [Win.overlaps_comm]
      exact pairwise_getElem? hpw h hqj hqi
  · intro i t e hp
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨t', e', hpe, hwin, -⟩ := hdf q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    rw [Lhs2.wins_of_windows? hwin]
    exact List.pairwise_singleton _ _
  · intro i t e hp
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨t', e', hpe, -, -, -, hfree, -⟩ := hdf q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    exact hfree
  · intro i t e hp x hx
    obtain ⟨q, hq, hqe⟩ := (hget i _).mp hp
    obtain ⟨t', e', hpe, -, -, -, -, -, hid⟩ := hdf q (List.mem_of_getElem? hq)
    rw [hpe] at hqe
    simp only [Process2.assign.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    have := hid x hx
    rw [hdecl]
    simpa [List.map_map, Function.comp_def, Summary.declNames] using this
  · intro n _ dc hdc _ v hv
    rw [hdecl] at hdc
    obtain ⟨dt, -, rfl⟩ := List.mem_map.mp hdc
    simp at hv
  · intro dc hdc _
    rw [hdecl] at hdc
    obtain ⟨dt, -, rfl⟩ := List.mem_map.mp hdc
    rfl

theorem realizedL_acyclic {s : Summary} {σ : String → Int} {d' : Design2} {args : List Int}
    {R : SiteId → SiteId → Prop}
    (hR : RealizedL s σ d') (hok : s.StructOk) (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hr : s.RankObl' R σ)
    (hrank : ∀ L : List SiteId, ∃ rk : SiteId → Nat, ∀ a ∈ L, ∀ b ∈ L, R b a → rk b < rk a) :
    Acyclic d' := by
  obtain ⟨hdecl, E, L, hLf, hP, hdesc⟩ := hR
  have hget : ∀ (i : Nat) (p : Process2), d'.processes[i]? = some p ↔
      ∃ q : SiteInst × Process2, L[i]? = some q ∧ p = q.2 := by
    intro i p
    rw [← Array.getElem?_toList, hP, List.getElem?_map]
    cases hL : L[i]? with
    | none => simp
    | some q => simp [eq_comm]
  have hmemL : ∀ q : SiteInst × Process2, q ∈ L → q.1 ∈ s.insts σ E :=
    fun q hq => hLf ▸ List.mem_map.2 ⟨q, hq, rfl⟩
  have hdf := fun (q : SiteInst × Process2) (hq : q ∈ L) =>
    descL_facts (E := E) hok hauto hin hdecl (hmemL q hq) (hdesc q hq)
  obtain ⟨rk, hrk⟩ := hrank (L.map fun q => q.1.id)
  refine ⟨fun j => match L[j]? with | some q => rk q.1.id | none => 0, ?_⟩
  intro i j ti ei tj ej wj hpi hpj hwj ⟨r, hrE, hov⟩
  obtain ⟨qi, hqi, hqie⟩ := (hget i _).mp hpi
  obtain ⟨qj, hqj, hqje⟩ := (hget j _).mp hpj
  obtain ⟨ti', ei', hpei, -, -, -, -, hrd, -⟩ := hdf qi (List.mem_of_getElem? hqi)
  obtain ⟨tj', ej', hpej, hwinj, -⟩ := hdf qj (List.mem_of_getElem? hqj)
  rw [hpei] at hqie
  rw [hpej] at hqje
  simp only [Process2.assign.injEq] at hqie hqje
  obtain ⟨rfl, rfl⟩ := hqie
  obtain ⟨rfl, rfl⟩ := hqje
  have hw : wj = qj.1.win := by
    rw [Lhs2.wins_of_windows? hwinj] at hwj
    simpa using hwj
  subst hw
  simp only [hqi, hqj]
  have hR' := rank_insts hr (hmemL qi (List.mem_of_getElem? hqi))
    (hmemL qj (List.mem_of_getElem? hqj)) (hrd r hrE) hov
  exact hrk qi.1.id (List.mem_map.2 ⟨qi, List.mem_of_getElem? hqi, rfl⟩) qj.1.id
    (List.mem_map.2 ⟨qj, List.mem_of_getElem? hqj, rfl⟩) hR'

/-! ## The one-driver rule of the design from its lowering -/

/-- **The one-driver rule of a design with procedural `always_comb` processes, from the comb profile of its
lowering.** `d'` is a `CombDesign` with positive write windows; `M`'s processes are, position by position,
`d'`'s (assigns) or a guarded body whose driven windows all match the lowered window (`LowRel`). Then
`driversOk` holds at any signal list `names` and any list `inputs` of input ports: the continuous windows are
`d'`'s, the procedural windows are the windows `d'` writes, and `d'.disjoint` / `selfDisjoint` / `notInput` are
the rule's clauses (the exclusivity clause, §9.2.2.2, because two procedural processes write disjoint windows
by `d'.disjoint`). -/
theorem driversOk_of_lowered {M d' : Design2} {names inputs : List String}
    (hc : CombDesign d') (hpos : ∀ i n lo w, d'.Writes i (n, lo, w) → 0 < w)
    (hin : ∀ n ∈ inputs, n ∈ d'.inputNames.toList) (hrel : LowRel M d') :
    driversOk names inputs M.processes.toList = true := by
  obtain ⟨hlen, hR⟩ := hrel
  -- per position: `d'` has an assign `t`, and `M`'s process is that assign or a guarded body on its windows
  have hproc : ∀ (i : Nat) (hi : i < M.processes.toList.length), ∃ (t : Lhs2) (e : Expr2) (ws : List Win),
      d'.processes[i]? = some (.assign t e) ∧ t.wins d' = ws ∧ DrvWin.MatchList d' t.drvWins ws ∧
      ((M.processes.toList[i].drvWins = t.drvWins ∧ M.processes.toList[i].procWins = []) ∨
       (M.processes.toList[i].drvWins = [] ∧
         ∀ x ∈ M.processes.toList[i].procWins, ∃ a ∈ ws, DrvWin.Matches d' x a)) := by
    intro i hi
    have hi' : i < d'.processes.toList.length := hlen ▸ hi
    have hget : d'.processes[i]? = some d'.processes.toList[i] := by
      rw [← Array.getElem?_toList]
      exact List.getElem?_eq_getElem hi'
    obtain ⟨t, e, ws, hp, hw⟩ := hc.assign i _ hget
    have hws : t.wins d' = ws := Lhs2.wins_of_windows? hw
    refine ⟨t, e, ws, by rw [← hp]; exact hget, hws, Lhs2.drvWins_matchList t ws hw, ?_⟩
    rcases hR i hi hi' with h | ⟨body, t', e', hM, hq, hx⟩
    · left
      rw [h, hp]
      exact ⟨rfl, rfl⟩
    · right
      rw [hq] at hp
      simp only [Process2.assign.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨by rw [hM]; rfl, ?_⟩
      rw [hM]
      intro x hx'
      obtain ⟨a, ha, hm⟩ := hx x hx'
      exact ⟨a, hws ▸ ha, hm⟩
  -- facts about one comb window of process `i`
  have hwin : ∀ (i : Nat) (t : Lhs2) (e : Expr2) (a : Win),
      d'.processes[i]? = some (.assign t e) → a ∈ t.wins d' →
        d'.Writes i a ∧ 0 < a.2.2 ∧ ∃ dw, d'.declWidth a.1 = some dw ∧ a.2.1 + a.2.2 ≤ dw := by
    intro i t e a hp ha
    have hW : d'.Writes i a := ⟨t, e, hp, ha⟩
    obtain ⟨n, lo, w⟩ := a
    exact ⟨hW, hpos i n lo w hW, hc.inWidth i n lo w hW⟩
  -- a continuous window comes from a process of the first kind
  have hdrv : ∀ (x : DrvWin) (i : Nat) (hi : i < M.processes.toList.length),
      x ∈ M.processes.toList[i].drvWins →
        ∃ (t : Lhs2) (e : Expr2) (ws : List Win) (a : Win), d'.processes[i]? = some (.assign t e) ∧
          t.wins d' = ws ∧ a ∈ ws ∧ DrvWin.Matches d' x a := by
    intro x i hi hx
    obtain ⟨t, e, ws, hpi, hws, hml, hk⟩ := hproc i hi
    rcases hk with ⟨hd, -⟩ | ⟨hd, -⟩
    · rw [hd] at hx
      obtain ⟨a, ha, hm⟩ := hml.exists_mem x hx
      exact ⟨t, e, ws, a, hpi, hws, ha, hm⟩
    · rw [hd] at hx
      simp at hx
  -- a procedural window comes from a process of the second kind
  have hprc : ∀ (x : DrvWin) (i : Nat) (hi : i < M.processes.toList.length),
      x ∈ M.processes.toList[i].procWins →
        ∃ (t : Lhs2) (e : Expr2) (ws : List Win) (a : Win), d'.processes[i]? = some (.assign t e) ∧
          t.wins d' = ws ∧ a ∈ ws ∧ DrvWin.Matches d' x a ∧ M.processes.toList[i].drvWins = [] := by
    intro x i hi hx
    obtain ⟨t, e, ws, hpi, hws, hml, hk⟩ := hproc i hi
    rcases hk with ⟨-, hd⟩ | ⟨hd, hm⟩
    · rw [hd] at hx
      simp at hx
    · obtain ⟨a, ha, hm'⟩ := hm x hx
      exact ⟨t, e, ws, a, hpi, hws, ha, hm', hd⟩
  have hsrc : ∀ x ∈ driverWins names M.processes.toList,
      ∃ (i : Nat) (hi : i < M.processes.toList.length), x ∈ M.processes.toList[i].drvWins := by
    intro x hx
    simp only [driverWins, List.mem_flatMap, List.mem_filter] at hx
    obtain ⟨p, hp, hxp, -⟩ := hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    exact ⟨i, hi, hxp⟩
  have hA : ∀ (i : Nat) (hi : i < M.processes.toList.length),
      (M.processes.toList[i].drvWins.filter (fun w => names.contains w.1)).Pairwise
        (fun a b => a.overlaps b = false) := by
    intro i hi
    obtain ⟨t, e, ws, hpi, hws, hml, hk⟩ := hproc i hi
    rcases hk with ⟨hd, -⟩ | ⟨hd, -⟩
    · rw [hd]
      apply List.Pairwise.filter
      have hsd := hc.selfDisjoint i t e hpi
      rw [hws] at hsd
      exact hml.pairwise hsd fun x a y b ha hb hxa hyb hab => by
        obtain ⟨-, hpa, hia⟩ := hwin i t e a hpi (hws ▸ ha)
        obtain ⟨-, hpb, hib⟩ := hwin i t e b hpi (hws ▸ hb)
        exact DrvWin.overlaps_eq_false_of_matches hxa hyb hpa hpb hia hib hab
    · rw [hd]
      exact List.Pairwise.nil
  have hB : ∀ (i j : Nat) (hi : i < M.processes.toList.length) (hj : j < M.processes.toList.length),
      i < j → ∀ x ∈ M.processes.toList[i].drvWins.filter (fun w => names.contains w.1),
        ∀ y ∈ M.processes.toList[j].drvWins.filter (fun w => names.contains w.1),
          x.overlaps y = false := by
    intro i j hi hj hij x hx y hy
    obtain ⟨t, e, ws, a, hpi, hws, ha, hxa⟩ := hdrv x i hi (List.mem_filter.mp hx).1
    obtain ⟨t', e', ws', b, hpj, hws', hb, hyb⟩ := hdrv y j hj (List.mem_filter.mp hy).1
    obtain ⟨hWa, hpa, hia⟩ := hwin i t e a hpi (hws ▸ ha)
    obtain ⟨hWb, hpb, hib⟩ := hwin j t' e' b hpj (hws' ▸ hb)
    exact DrvWin.overlaps_eq_false_of_matches hxa hyb hpa hpb hia hib
      (hc.disjoint i j a b (Nat.ne_of_lt hij) hWa hWb)
  rw [driversOk_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the continuous windows are pairwise disjoint
    simp only [driverWins]
    rw [List.pairwise_flatMap]
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      exact hA i hi
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij x hx y hy
      exact hB i j hi hj hij x hx y hy
  · -- no continuous window on an input port or under a procedural window
    intro w hw
    obtain ⟨i, hi, hwi⟩ := hsrc w hw
    obtain ⟨t, e, ws, a, hpi, hws, ha, hwa⟩ := hdrv w i hi hwi
    obtain ⟨hWa, hpa, hia⟩ := hwin i t e a hpi (hws ▸ ha)
    refine ⟨?_, fun v hv => ?_⟩
    · have hni := hc.notInput a.1 ⟨i, a.2.1, a.2.2, hWa⟩
      rw [Bool.eq_false_iff]
      intro hcont
      rw [List.contains_iff_mem, hwa.1] at hcont
      exact hni (hin _ hcont)
    · simp only [List.mem_flatMap] at hv
      obtain ⟨p, hp, hvp⟩ := hv
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
      obtain ⟨t', e', ws', b, hpj, hws', hb, hvb, hdj⟩ := hprc v j hj hvp
      obtain ⟨hWb, hpb, hib⟩ := hwin j t' e' b hpj (hws' ▸ hb)
      have hij : i ≠ j := by
        rintro rfl
        rw [hdj] at hwi
        simp at hwi
      exact DrvWin.overlaps_eq_false_of_matches hwa hvb hpa hpb hia hib
        (hc.disjoint i j a b hij hWa hWb)
  · -- no procedural process writes an input port
    intro n hn
    simp only [List.mem_flatMap] at hn
    obtain ⟨p, hp, hnp⟩ := hn
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    rw [Process2.procWrites_eq, List.mem_map] at hnp
    obtain ⟨v, hv, rfl⟩ := hnp
    obtain ⟨t', e', ws', b, hpj, hws', hb, hvb, -⟩ := hprc v j hj hv
    obtain ⟨hWb, -, -⟩ := hwin j t' e' b hpj (hws' ▸ hb)
    have hni := hc.notInput b.1 ⟨j, b.2.1, b.2.2, hWb⟩
    rw [Bool.eq_false_iff]
    intro hcont
    rw [List.contains_iff_mem, hvb.1] at hcont
    exact hni (hin _ hcont)
  · -- exclusivity: two procedural processes write disjoint windows
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hY : ((M.processes.toList[i].procWinsOn names).any fun a =>
        (M.processes.toList[j].procWinsOn names).any fun b => a.overlaps b) = false := by
      rw [Bool.eq_false_iff]
      intro h
      obtain ⟨a, ha, h2⟩ := List.any_eq_true.mp h
      obtain ⟨b, hb, hab⟩ := List.any_eq_true.mp h2
      obtain ⟨t, e, ws, a', hpi, hws, haa, hma, -⟩ := hprc a i hi (List.mem_filter.mp ha).1
      obtain ⟨t', e', ws', b', hpj, hws', hbb, hmb, -⟩ := hprc b j hj (List.mem_filter.mp hb).1
      obtain ⟨hWa, hpa, hia⟩ := hwin i t e a' hpi (hws ▸ haa)
      obtain ⟨hWb, hpb, hib⟩ := hwin j t' e' b' hpj (hws' ▸ hbb)
      have := DrvWin.overlaps_eq_false_of_matches hma hmb hpa hpb hia hib
        (hc.disjoint i j a' b' (Nat.ne_of_lt hij) hWa hWb)
      rw [this] at hab
      exact absurd hab (by simp)
    unfold Process2.exclClash
    rw [hY, Bool.and_false]

/-- **`name.sem` of a design with procedural `always_comb` processes from the comb profile of its lowering**:
the instantiation, the comb profile `hc` of the lowered design `d'`, positive windows and the process
correspondence give `d.instantiateGD2 args = m` (the driver guard passes). -/
theorem PDesign.instantiateGD2_of_lowered {d : PDesign} {args : List Int} {M d' : Design2}
    (h : d.instantiate2 args (PDesign.surfaceFuel args) = .ok M) (hdec : d'.decls = M.decls)
    (hc : CombDesign d') (hpos : ∀ i n lo w, d'.Writes i (n, lo, w) → 0 < w) (hrel : LowRel M d') :
    d.instantiateGD2 args = M := by
  refine PDesign.instantiateGD2_of_ok h
    (driversOk_of_lowered hc hpos (fun n hn => ?_) hrel)
  have := PDesign.instantiate2_inputNames h n hn
  simpa [Design2.inputNames, hdec] using this

/-! ## The structure theorems for the lowered design -/

/-- **`∃ d', (name.sem N).lowerComb = some d' ∧ CombDesign d'`** from the summary and the obligations. -/
theorem comb_of_summaryL {d : PDesign} {s : Summary} (hs : d.summaryP = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ) (hself : s.NoSelfRead σ) :
    ∃ d', (d.instantiateGD2 args).lowerComb = some d' ∧ CombDesign d' := by
  obtain ⟨m, d', -, -, hm, hl, hdm, hdd, hrel, hR, -⟩ := Summary.soundL hs harity h1 hag hok hauto hin hself
  obtain ⟨hc, hpos⟩ := realizedL_comb hR hok hauto hin hdisj
  rw [PDesign.instantiateGD2_of_lowered hm hdd hc hpos hrel]
  exact ⟨d', hl, hc⟩

/-- **`∃ d', (name.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d'`** from a `Nat`-valued rank. -/
theorem struct_of_summaryL {d : PDesign} {s : Summary} (hs : d.summaryP = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ) (hself : s.NoSelfRead σ)
    {R : SiteId → SiteId → Prop} (hr : s.RankObl' R σ)
    (hrank : ∀ L : List SiteId, ∃ rk : SiteId → Nat, ∀ a ∈ L, ∀ b ∈ L, R b a → rk b < rk a) :
    ∃ d', (d.instantiateGD2 args).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  obtain ⟨m, d', -, -, hm, hl, hdm, hdd, hrel, hR, -⟩ := Summary.soundL hs harity h1 hag hok hauto hin hself
  obtain ⟨hc, hpos⟩ := realizedL_comb hR hok hauto hin hdisj
  rw [PDesign.instantiateGD2_of_lowered hm hdd hc hpos hrel]
  exact ⟨d', hl, hc, realizedL_acyclic hR hok hauto hin hr hrank⟩

/-- … with a `Nat`-valued rank over site identities. -/
theorem struct_of_rankL {d : PDesign} {s : Summary} (hs : d.summaryP = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ) (hself : s.NoSelfRead σ)
    {ρ : SiteId → Nat} (hrank : s.RankObl ρ σ) :
    ∃ d', (d.instantiateGD2 args).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' :=
  struct_of_summaryL hs harity h1 hag hok hauto hin hdisj hself hrank
    (fun _ => ⟨ρ, fun _ _ _ _ h => h⟩)

/-- … with a LEXICOGRAPHIC key. -/
theorem struct_of_lexL {d : PDesign} {s : Summary} (hs : d.summaryP = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ) (hdisj : s.DisjObl σ) (hself : s.NoSelfRead σ)
    {κ : SiteId → Key} (hrank : s.LexObl κ σ) :
    ∃ d', (d.instantiateGD2 args).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' :=
  struct_of_summaryL hs harity h1 hag hok hauto hin hdisj hself hrank
    (fun L => ⟨countRank L κ, fun _ _ _ hb h => countRank_lt L κ hb h⟩)

/-! ## The forms the tactic uses (valuation `s.val args`, environment check in a `rfl`-provable form) -/

theorem comb_viewL {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (hself : s.NoSelfRead (s.val args)) :
    ∃ d', (d.instantiateGD2 args).lowerComb = some d' ∧ CombDesign d' :=
  comb_of_summaryL hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hself

theorem struct_viewL {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (hself : s.NoSelfRead (s.val args))
    (ρ : SiteId → Nat) (hrank : s.RankObl ρ (s.val args)) :
    ∃ d', (d.instantiateGD2 args).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' :=
  struct_of_rankL hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hself hrank

theorem struct_lex_viewL {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.summaryP = .ok s) (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.vals.lookup n) =
      s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args)
    (hin : s.InRangeObl (s.val args)) (hdisj : s.DisjObl (s.val args))
    (hself : s.NoSelfRead (s.val args))
    (κ : SiteId → Key) (hrank : s.LexObl κ (s.val args)) :
    ∃ d', (d.instantiateGD2 args).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' :=
  struct_of_lexL hs harity h1 (Agrees_of_map hag) hok hauto hin hdisj hself hrank

/-! ## Axiom pins (standard axioms only) -/

/-- info: 'LeanModels.Sv.CombView.RdOK.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RdOK.mono

/-- info: 'LeanModels.Sv.CombView.RdOK.ifGuard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RdOK.ifGuard

/-- info: 'LeanModels.Sv.CombView.RdOK.ternary' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms RdOK.ternary

/-- info: 'LeanModels.Sv.CombView.low_rdOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms low_rdOK

/-- info: 'LeanModels.Sv.CombView.proc_site_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proc_site_eq

/-- info: 'LeanModels.Sv.CombView.windows_concat_win' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms windows_concat_win

/-- info: 'LeanModels.Sv.CombView.wins_concat_win' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms wins_concat_win

/-- info: 'LeanModels.Sv.CombView.lowerProcs_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerProcs_map

/-- info: 'LeanModels.Sv.CombView.pairs_descL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pairs_descL

/-- info: 'LeanModels.Sv.CombView.fams_expand2P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fams_expand2P

/-- info: 'LeanModels.Sv.CombView.Summary.soundL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Summary.soundL

/-- info: 'LeanModels.Sv.CombView.descL_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms descL_facts

/-- info: 'LeanModels.Sv.CombView.realizedL_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realizedL_comb

/-- info: 'LeanModels.Sv.CombView.realizedL_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms realizedL_acyclic

/-- info: 'LeanModels.Sv.CombView.driversOk_of_lowered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms driversOk_of_lowered

/-- info: 'LeanModels.Sv.CombView.PDesign.instantiateGD2_of_lowered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PDesign.instantiateGD2_of_lowered

/-- info: 'LeanModels.Sv.CombView.comb_of_summaryL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comb_of_summaryL

/-- info: 'LeanModels.Sv.CombView.struct_of_summaryL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_of_summaryL

/-- info: 'LeanModels.Sv.CombView.struct_of_rankL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_of_rankL

/-- info: 'LeanModels.Sv.CombView.struct_of_lexL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_of_lexL

/-- info: 'LeanModels.Sv.CombView.comb_viewL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms comb_viewL

/-- info: 'LeanModels.Sv.CombView.struct_viewL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_viewL

/-- info: 'LeanModels.Sv.CombView.struct_lex_viewL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms struct_lex_viewL

end CombView
end LeanModels.Sv
