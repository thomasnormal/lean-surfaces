import LeanModels.Sv.CombProc
import LeanModels.Sv.CombViewSound

/-!
# `always_comb` bodies in the `sv_comb` fragment, stage 3: the proc-aware summary (WP-G, G2.2)

`PDesign.summary` (`CombView.lean`) refuses every `always_comb` (`siteOf?`: "procedural process"), and the
whole soundness chain built on it (`pairs_desc`, `Summary.sound`, `realized_comb`, `eq_of_summary`, …) concludes
that every instantiated process is an `assign`. For a summary with a procedural site that conclusion is false, so
the chain cannot simply be given one more case: its theorems are called with their current statements by the
Examples proofs and the migrated references. This file starts a PARALLEL, proc-aware layer, and leaves the old
one untouched:

* `siteOfP?` is `siteOf?` plus the `always_comb` arm: the body is recognized as a tree (`CombProc.treeStmt?`,
  fragment S1) and becomes ONE site whose target is the single written access and whose reads are the tree's
  (`TSite.proc` keeps the whole `alwaysComb` process);
* `sitesOfP?`, `itemOfP?`, `itemsOfP?`, `famOfP?`, `famsOfP?`, `PDesign.summaryP` and their specification
  lemmas are GENERATED COPIES of the old ones with `siteOf?` replaced by `siteOfP?` (same proofs): the
  declarations of the rest of the summary (`Summary`, `TSite`, `LSite`, the obligations `StructOk`,
  `InRangeObl`, `DisjObl`, `RankObl'`, `AutoObl`, `CoverObl`) are SHARED, they only read the site's
  target and reads.

For a design without `always_comb`, `siteOfP? = siteOf?` and `summaryP = summary` (`summaryP_of_noProc` below is
the statement for sites; the designs are checked by the `#guard`s). Consolidation later: delete the copies,
give `siteOf?` the arm, and add the "no procedural site" hypothesis the old theorems then need.
-/

namespace LeanModels.Sv
namespace CombView

/-- `siteOf?` plus the `always_comb` arm. -/
def siteOfP? (ds : List DeclT) (pos : Nat) : PProcess → Except String TSite
  | .alwaysComb b =>
      match CombProc.treeStmt? ds b with
      | .error e => .error e
      | .ok (tg, ptr) => .ok ⟨pos, tg, ptr.rds, .alwaysComb b⟩
  | p => siteOf? ds pos p

/-- Inversion: a site of `siteOfP?` is an old site, or the site of a recognized `always_comb` body. -/
theorem siteOfP?_cases {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOfP? ds pos p = .ok st) :
    siteOf? ds pos p = .ok st ∨
      ∃ b tg ptr, p = .alwaysComb b ∧ CombProc.treeStmt? ds b = .ok (tg, ptr) ∧
        st = ⟨pos, tg, ptr.rds, p⟩ := by
  cases p with
  | alwaysComb b =>
      right
      simp only [siteOfP?] at h
      rcases ht : CombProc.treeStmt? ds b with e | ⟨tg, ptr⟩
      · simp [ht] at h
      · simp only [ht, Except.ok.injEq] at h
        exact ⟨b, tg, ptr, rfl, ht, h.symm⟩
  | assign t v => left; exact h
  | assignL l v => left; exact h
  | alwaysFF _ _ => left; exact h
  | alwaysPlain _ _ => left; exact h
  | alwaysFFR _ _ _ => left; exact h
  | unsupported _ _ => left; exact h

theorem siteOfP?_proc {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOfP? ds pos p = .ok st) : st.proc = p := by
  rcases siteOfP?_cases h with h | ⟨b, tg, ptr, rfl, -, rfl⟩
  · exact siteOf?_proc h
  · rfl

/-! ## The recognizers (generated copies of `CombView.lean`'s, over `siteOfP?`) -/

def sitesOfP? (ds : List DeclT) (tag : String) : Nat → List PProcess → Except String (List TSite)
  | _, [] => .ok []
  | pos, p :: ps =>
      match siteOfP? ds pos p with
      | .error e => .error s!"site `{tag}#{pos}`: {e}"
      | .ok st =>
          match sitesOfP? ds tag (pos + 1) ps with
          | .error e => .error e
          | .ok sts => .ok (st :: sts)

/-- An item of an outer loop's body at position `pos`. -/
def itemOfP? (ds : List DeclT) (tag : String) (pos : Nat) : GenItem → Except String TItem
  | .process p =>
      match siteOfP? ds pos p with
      | .error e => .error s!"site `{tag}#{pos}`: {e}"
      | .ok st => .ok (.site st)
  | .genFor label g initE bound step rc body =>
      match hdrOf? label g initE bound step with
      | .error e => .error e
      | .ok h =>
          match procsOf? body with
          | none => .error "an inner generate loop holds a nested generate, a conditional generate or an instance (the v1 fragment nests generate loops two deep)"
          | some ps =>
              match sitesOfP? ds h.name 0 ps with
              | .error e => .error e
              | .ok sts => .ok (.loop ⟨h, rc, sts⟩)
  | .genIf .. => .error "conditional generate inside a generate loop (outside the v1 fragment)"
  | .inst _ => .error "module instance inside a generate loop (outside the v1 fragment)"
  | .unsupported k _ => .error s!"unsupported generate item `{k}`"

def itemsOfP? (ds : List DeclT) (tag : String) : Nat → List GenItem → Except String (List TItem)
  | _, [] => .ok []
  | pos, it :: rest =>
      match itemOfP? ds tag pos it with
      | .error e => .error e
      | .ok x =>
          match itemsOfP? ds tag (pos + 1) rest with
          | .error e => .error e
          | .ok xs => .ok (x :: xs)

def famOfP? (ds : List DeclT) : GenItem → Except String TFam
  | .genFor label g initE bound step rc body =>
      match hdrOf? label g initE bound step with
      | .error e => .error e
      | .ok h =>
          match itemsOfP? ds h.name 0 body with
          | .error e => .error e
          | .ok its => .ok ⟨h, rc, its⟩
  | .genIf .. => .error "conditional generate (outside the v1 fragment)"
  | .inst _ => .error "module instance (outside the v1 fragment)"
  | .process _ => .error "process item in the generate list"
  | .unsupported k _ => .error s!"unsupported generate item `{k}`"

def famsOfP? (ds : List DeclT) : List GenItem → Except String (List TFam)
  | [] => .ok []
  | it :: rest =>
      match famOfP? ds it with
      | .error e => .error e
      | .ok f =>
          match famsOfP? ds rest with
          | .error e => .error e
          | .ok fs => .ok (f :: fs)

def _root_.LeanModels.Sv.PDesign.summaryP (d : PDesign) : Except String Summary :=
  match lpsOf? (d.params.map (·.name)) d.localParams with
  | .error e => .error e
  | .ok lps =>
      if !d.enums.isEmpty then .error "enums are outside the v1 fragment"
      else if !d.others.isEmpty then .error "out-of-tier module members are present"
      else
        match declsOf? d.decls with
        | .error e => .error e
        | .ok ds =>
            match sitesOfP? ds "plain" 0 d.processes with
            | .error e => .error e
            | .ok sts =>
                match famsOfP? ds d.generates with
                | .error e => .error e
                | .ok fs =>
                    .ok { params := d.params.map (·.name) ++ lps.map Prod.fst, decls := ds,
                          statics := sts, fams := fs, lps := lps }

theorem sitesOfP?_spec {ds : List DeclT} {tag : String} :
    ∀ {ps : List PProcess} {pos : Nat} {sts : List TSite},
    sitesOfP? ds tag pos ps = .ok sts →
      sts.map TSite.proc = ps ∧ ∀ st ∈ sts, ∃ pos' p, siteOfP? ds pos' p = .ok st
  | [], pos, sts, h => by
      simp only [sitesOfP?, Except.ok.injEq] at h
      subst h
      simp
  | p :: ps, pos, sts, h => by
      simp only [sitesOfP?] at h
      rcases hs : siteOfP? ds pos p with e | st
      · simp [hs] at h
      · rcases hr : sitesOfP? ds tag (pos + 1) ps with e | sts'
        · simp [hs, hr] at h
        · simp only [hs, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨h1, h2⟩ := sitesOfP?_spec hr
          refine ⟨?_, ?_⟩
          · simp [h1, siteOfP?_proc hs]
          · intro st' hst'
            rcases List.mem_cons.mp hst' with rfl | hm
            · exact ⟨pos, p, hs⟩
            · exact h2 st' hm


theorem itemOfP?_spec {ds : List DeclT} {tag : String} {pos : Nat} {it : GenItem} {x : TItem}
    (h : itemOfP? ds tag pos it = .ok x) :
    x.toGen = it ∧ x.Wf ∧ ∀ st ∈ x.stList, ∃ pos' p, siteOfP? ds pos' p = .ok st := by
  cases it with
  | process p =>
      simp only [itemOfP?] at h
      rcases hs : siteOfP? ds pos p with e | st
      · simp [hs] at h
      · simp only [hs, Except.ok.injEq] at h
        subst h
        refine ⟨?_, trivial, ?_⟩
        · simp [TItem.toGen, siteOfP?_proc hs]
        · intro st' hst'
          simp only [TItem.stList, List.mem_singleton] at hst'
          subst hst'
          exact ⟨pos, p, hs⟩
  | genFor label g initE bound step rc body =>
      simp only [itemOfP?] at h
      rcases hh : hdrOf? label g initE bound step with e | h0
      · simp [hh] at h
      · rcases hp : procsOf? body with _ | ps
        · simp [hh, hp] at h
        · rcases hsx : sitesOfP? ds h0.name 0 ps with e | sts
          · simp [hh, hp, hsx] at h
          · simp only [hh, hp, hsx, Except.ok.injEq] at h
            subst h
            obtain ⟨hl, hg, hwf, hi, hb, hst⟩ := hdrOf?_spec hh
            obtain ⟨hmap, hsites⟩ := sitesOfP?_spec hsx
            refine ⟨?_, hwf, hsites⟩
            have hbody : (sts.map fun st => GenItem.process st.proc) = body := by
              rw [procsOf?_eq hp, ← hmap, List.map_map]; rfl
            simp only [TItem.toGen, Hdr.gen]
            rw [← hi, ← hb, ← hst, hl, hg, hbody]
  | genIf c t e => simp [itemOfP?] at h
  | inst i => simp [itemOfP?] at h
  | unsupported k t => simp [itemOfP?] at h

theorem itemsOfP?_spec {ds : List DeclT} {tag : String} :
    ∀ {pos : Nat} {items : List GenItem} {its : List TItem}, itemsOfP? ds tag pos items = .ok its →
      its.map TItem.toGen = items ∧ ∀ x ∈ its, x.Wf ∧
        ∀ st ∈ x.stList, ∃ pos' p, siteOfP? ds pos' p = .ok st
  | pos, [], its, h => by
      simp only [itemsOfP?, Except.ok.injEq] at h
      subst h
      simp
  | pos, it :: rest, its, h => by
      simp only [itemsOfP?] at h
      rcases hx : itemOfP? ds tag pos it with e | x
      · simp [hx] at h
      · rcases hr : itemsOfP? ds tag (pos + 1) rest with e | xs
        · simp [hx, hr] at h
        · simp only [hx, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨h1, h2, h3⟩ := itemOfP?_spec hx
          obtain ⟨k1, k2⟩ := itemsOfP?_spec hr
          refine ⟨by simp [h1, k1], ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hm
          · exact ⟨h2, h3⟩
          · exact k2 y hm

theorem famOfP?_spec {ds : List DeclT} {it : GenItem} {f : TFam} (h : famOfP? ds it = .ok f) :
    f.toGen = it ∧ f.Wf ∧ ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos' p, siteOfP? ds pos' p = .ok st := by
  cases it with
  | genFor label g initE bound step rc body =>
      simp only [famOfP?] at h
      rcases hh : hdrOf? label g initE bound step with e | h0
      · simp [hh] at h
      · rcases hit : itemsOfP? ds h0.name 0 body with e | its
        · simp [hh, hit] at h
        · simp only [hh, hit, Except.ok.injEq] at h
          subst h
          obtain ⟨hl, hg, hwf, hi, hb, hst⟩ := hdrOf?_spec hh
          obtain ⟨k1, k2⟩ := itemsOfP?_spec hit
          refine ⟨?_, ⟨hwf, fun x hx => (k2 x hx).1⟩, fun x hx => (k2 x hx).2⟩
          simp only [TFam.toGen, Hdr.gen]
          rw [← hi, ← hb, ← hst, hl, hg, k1]
  | process p => simp [famOfP?] at h
  | genIf c t e => simp [famOfP?] at h
  | inst i => simp [famOfP?] at h
  | unsupported k t => simp [famOfP?] at h

/-- The generate tree of a recognized design: every loop is the envelope's, with recognized
bounds, and every site was recognized from a process. -/
def Summary.SpecOkP (s : Summary) : Prop :=
  ∀ f ∈ s.fams, f.Wf ∧ ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos p, siteOfP? s.decls pos p = .ok st

theorem famsOfP?_spec {ds : List DeclT} :
    ∀ {gens : List GenItem} {fs : List TFam}, famsOfP? ds gens = .ok fs →
      fs.map TFam.toGen = gens ∧ ∀ f ∈ fs, f.Wf ∧
        ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos' p, siteOfP? ds pos' p = .ok st
  | [], fs, h => by
      simp only [famsOfP?, Except.ok.injEq] at h
      subst h
      simp
  | it :: rest, fs, h => by
      simp only [famsOfP?] at h
      rcases hf : famOfP? ds it with e | f
      · simp [hf] at h
      · rcases hr : famsOfP? ds rest with e | fs'
        · simp [hf, hr] at h
        · simp only [hf, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨h1, h2, h3⟩ := famOfP?_spec hf
          obtain ⟨k1, k2⟩ := famsOfP?_spec hr
          refine ⟨by simp [h1, k1], ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hm
          · exact ⟨h2, h3⟩
          · exact k2 y hm


theorem summaryP_spec {d : PDesign} {s : Summary} (h : d.summaryP = .ok s) :
    s.lps.map Prod.fst = d.localParams.map (·.name) ∧ d.enums = [] ∧ d.others = [] ∧
    s.params = d.params.map (·.name) ++ s.lps.map Prod.fst ∧
    declsOf? d.decls = .ok s.decls ∧ sitesOfP? s.decls "plain" 0 d.processes = .ok s.statics ∧
    d.generates = s.fams.map TFam.toGen ∧ s.SpecOkP := by
  unfold PDesign.summaryP at h
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
  rcases hp : sitesOfP? ds "plain" 0 d.processes with e | sts
  · simp [hd, hp] at h
  rcases hg : famsOfP? ds d.generates with e | fs
  · simp [hd, hp, hg] at h
  simp only [hd, hp, hg, Except.ok.injEq] at h
  subst h
  obtain ⟨k1, k2⟩ := famsOfP?_spec hg
  have hnames : lps.map Prod.fst = d.localParams.map (·.name) := lpsOf?_names hl
  exact ⟨hnames, he, ho, rfl, rfl, hp, k1.symm, k2⟩

theorem lsitesP_spec {s : Summary}
    (hsta : ∀ st ∈ s.statics, ∃ pos p, siteOfP? s.decls pos p = .ok st) (hspec : s.SpecOkP) :
    ∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site := by
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

/-! ## Axiom pins (standard axioms only) -/

/-- info: 'LeanModels.Sv.CombView.siteOfP?_cases' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms siteOfP?_cases

/-- info: 'LeanModels.Sv.CombView.siteOfP?_proc' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms siteOfP?_proc

/-- info: 'LeanModels.Sv.CombView.sitesOfP?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sitesOfP?_spec

/-- info: 'LeanModels.Sv.CombView.itemOfP?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms itemOfP?_spec

/-- info: 'LeanModels.Sv.CombView.itemsOfP?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms itemsOfP?_spec

/-- info: 'LeanModels.Sv.CombView.famOfP?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms famOfP?_spec

/-- info: 'LeanModels.Sv.CombView.famsOfP?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms famsOfP?_spec

/-- info: 'LeanModels.Sv.CombView.summaryP_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms summaryP_spec

/-- info: 'LeanModels.Sv.CombView.lsitesP_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lsitesP_spec

end CombView
end LeanModels.Sv
