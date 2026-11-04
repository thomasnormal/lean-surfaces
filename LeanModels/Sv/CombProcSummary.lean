import LeanModels.Sv.CombProc
import LeanModels.Sv.CombProcBody
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
  (`TSite.proc` keeps the whole `alwaysComb` process); a body of SEVERAL windows (`CombProc.multiSegs?`, S1b gate b)
  becomes ONE site too, with the further target accessors in `TSite.more` and the reads of every segment;
* `sitesOfP?`, `itemOfP?`, `itemsOfP?`, `famOfP?`, `famsOfP?`, `PDesign.summaryP` and their specification
  lemmas are INSTANCES (with `siteOfP?`) of the recognizers and specifications of `CombView.lean` /
  `CombViewSound.lean`, which are generic in the process recognizer (`sitesOfG`, ..., `PDesign.summaryG`,
  `sitesOfG_spec`, ...; the old `siteOf?` names are the `siteOf?` instances, statements unchanged): the
  declarations of the rest of the summary (`Summary`, `TSite`, `LSite`, the obligations `StructOk`,
  `InRangeObl`, `DisjObl`, `RankObl'`, `AutoObl`, `CoverObl`) are SHARED, they only read the site's
  target and reads.

For a design without `always_comb`, `siteOfP? = siteOf?` and `summaryP = summary` (`summaryP_of_noProc` below is
the statement for sites; the designs are checked by the `#guard`s).
-/

namespace LeanModels.Sv
namespace CombView

/-- The reads of all the segments of a body, in order. -/
def segsRds (segs : List (Acc × CombProc.PTR)) : List Acc := segs.flatMap fun s => s.2.rds

/-- The site of a recognized body of SEVERAL windows (at least two segments, `CombProc.multiSegs?`): the first
segment's target is the head window, the others' targets are `more`, in source order; the reads are those of all
the segments. -/
def multiSite (pos : Nat) (b : PStmt) : List (Acc × CombProc.PTR) → Option TSite
  | segs@((tg, _) :: (tg2, _) :: rest) =>
      some ⟨pos, tg, segs.flatMap (fun s => s.2.rds), .alwaysComb b, tg2 :: rest.map Prod.fst, [], []⟩
  | _ => none

/-- `siteOf?` plus the `always_comb` arm: a body that `CombProc.treeStmt?` reads is ONE site of one window (`more =
[]`, as before); otherwise a block of several windows (`CombProc.multiSegs?`, at least two segments) is ONE site
with further windows. A refused body keeps the message of `treeStmt?`, except the new refusal of a window written in
two separate groups of statements. -/
def siteOfP? (ds : List DeclT) (pos : Nat) : PProcess → Except String TSite
  | .alwaysComb b =>
      match CombProc.treeStmt? ds b with
      | .ok (tg, ptr) => .ok ⟨pos, tg, ptr.rds, .alwaysComb b, [], [], []⟩
      | .error e =>
          match CombProc.multiSegs? ds b with
          | .ok segs =>
              match multiSite pos b segs with
              | some st => .ok st
              | none => .error e
          | .error e' => .error (if e' == CombProc.interleaveMsg then e' else e)
  | p => siteOf? ds pos p

theorem multiSite_shape {pos : Nat} {b : PStmt} {segs : List (Acc × CombProc.PTR)} {st : TSite}
    (h : multiSite pos b segs = some st) :
    st.proc = .alwaysComb b ∧ st.rds = segsRds segs ∧ st.tgt :: st.more = segs.map Prod.fst ∧ st.more ≠ [] := by
  match segs, h with
  | (tg, p1) :: (tg2, p2) :: rest, h =>
      simp only [multiSite, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, by simp, by simp⟩
  | [], h => simp [multiSite] at h
  | [_], h => simp [multiSite] at h

/-- Inversion: a site of `siteOfP?` is an old site, the site of a body one tree reads, or the site of a body of
several windows. -/
theorem siteOfP?_cases {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOfP? ds pos p = .ok st) :
    siteOf? ds pos p = .ok st ∨
      (∃ b tg ptr, p = .alwaysComb b ∧ CombProc.treeStmt? ds b = .ok (tg, ptr) ∧
        st = ⟨pos, tg, ptr.rds, p, [], [], []⟩) ∨
      (∃ b segs, p = .alwaysComb b ∧ CombProc.multiSegs? ds b = .ok segs ∧ multiSite pos b segs = some st) := by
  cases p with
  | alwaysComb b =>
      right
      simp only [siteOfP?] at h
      rcases ht : CombProc.treeStmt? ds b with e | ⟨tg, ptr⟩
      · rw [ht] at h
        simp only at h
        rcases hm : CombProc.multiSegs? ds b with e' | segs
        · rw [hm] at h
          simp at h
        · rw [hm] at h
          simp only at h
          rcases hs : multiSite pos b segs with _ | st'
          · rw [hs] at h
            simp at h
          · rw [hs] at h
            simp only [Except.ok.injEq] at h
            subst h
            exact Or.inr ⟨b, segs, rfl, hm, hs⟩
      · rw [ht] at h
        simp only [Except.ok.injEq] at h
        exact Or.inl ⟨b, tg, ptr, rfl, ht, h.symm⟩
  | assign t v => left; exact h
  | assignL l v => left; exact h
  | alwaysFF _ _ => left; exact h
  | alwaysPlain _ _ => left; exact h
  | alwaysFFR _ _ _ _ => left; exact h
  | unsupported _ _ => left; exact h

theorem siteOfP?_proc {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOfP? ds pos p = .ok st) : st.proc = p := by
  rcases siteOfP?_cases h with h | ⟨b, tg, ptr, rfl, -, rfl⟩ | ⟨b, segs, rfl, -, hs⟩
  · exact siteOf?_proc h
  · rfl
  · exact (multiSite_shape hs).1

/-! ## The recognizers (the generic ones of `CombView.lean`, instantiated with `siteOfP?`)

`sitesOfG`, `itemOfG`, `itemsOfG`, `famOfG`, `famsOfG`, `PDesign.summaryG` and their specification lemmas
(`CombViewSound.lean`) are generic in the process recognizer; the old chain instantiates them with `siteOf?`,
this layer with `siteOfP?` (Tier A of the consolidation, WP-G): there are no copies left. -/

def sitesOfP? (ds : List DeclT) (tag : String) : Nat → List PProcess → Except String (List TSite) :=
  sitesOfG siteOfP? ds tag

/-- An item of an outer loop's body at position `pos`. -/
def itemOfP? (ds : List DeclT) (tag : String) (pos : Nat) : GenItem → Except String TItem :=
  itemOfG siteOfP? ds tag pos

def itemsOfP? (ds : List DeclT) (tag : String) : Nat → List GenItem → Except String (List TItem) :=
  itemsOfG siteOfP? ds tag

def famOfP? (ds : List DeclT) : GenItem → Except String TFam :=
  famOfG siteOfP? ds

def famsOfP? (ds : List DeclT) : List GenItem → Except String (List TFam) :=
  famsOfG siteOfP? ds

def _root_.LeanModels.Sv.PDesign.summaryP (d : PDesign) : Except String Summary :=
  d.summaryG siteOfP?

/-! ## Their specifications -/

theorem siteOfP?_proc' : ∀ (ds : List DeclT) (pos : Nat) (p : PProcess) (st : TSite),
    siteOfP? ds pos p = .ok st → st.proc = p := fun _ _ _ _ h => siteOfP?_proc h

theorem sitesOfP?_spec {ds : List DeclT} {tag : String} :
    ∀ {ps : List PProcess} {pos : Nat} {sts : List TSite},
    sitesOfP? ds tag pos ps = .ok sts →
      sts.map TSite.proc = ps ∧ ∀ st ∈ sts, ∃ pos' p, siteOfP? ds pos' p = .ok st :=
  fun h => sitesOfG_spec siteOfP? siteOfP?_proc' h

theorem itemOfP?_spec {ds : List DeclT} {tag : String} {pos : Nat} {it : GenItem} {x : TItem}
    (h : itemOfP? ds tag pos it = .ok x) :
    x.toGen = it ∧ x.Wf ∧ ∀ st ∈ x.stList, ∃ pos' p, siteOfP? ds pos' p = .ok st :=
  itemOfG_spec siteOfP? siteOfP?_proc' h

theorem itemsOfP?_spec {ds : List DeclT} {tag : String} :
    ∀ {pos : Nat} {items : List GenItem} {its : List TItem}, itemsOfP? ds tag pos items = .ok its →
      its.map TItem.toGen = items ∧ ∀ x ∈ its, x.Wf ∧
        ∀ st ∈ x.stList, ∃ pos' p, siteOfP? ds pos' p = .ok st :=
  fun h => itemsOfG_spec siteOfP? siteOfP?_proc' h

theorem famOfP?_spec {ds : List DeclT} {it : GenItem} {f : TFam} (h : famOfP? ds it = .ok f) :
    f.toGen = it ∧ f.Wf ∧ ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos' p, siteOfP? ds pos' p = .ok st :=
  famOfG_spec siteOfP? siteOfP?_proc' h

/-- The generate tree of a recognized design: every loop is the envelope's, with recognized
bounds, and every site was recognized from a process. -/
def Summary.SpecOkP (s : Summary) : Prop := s.SpecOkG siteOfP?

theorem famsOfP?_spec {ds : List DeclT} :
    ∀ {gens : List GenItem} {fs : List TFam}, famsOfP? ds gens = .ok fs →
      fs.map TFam.toGen = gens ∧ ∀ f ∈ fs, f.Wf ∧
        ∀ x ∈ f.body, ∀ st ∈ x.stList, ∃ pos' p, siteOfP? ds pos' p = .ok st :=
  fun h => famsOfG_spec siteOfP? siteOfP?_proc' h

theorem summaryP_spec {d : PDesign} {s : Summary} (h : d.summaryP = .ok s) :
    s.lps.map Prod.fst = d.localParams.map (·.name) ∧ d.enums = [] ∧ d.others = [] ∧
    s.params = d.params.map (·.name) ++ s.lps.map Prod.fst ∧
    declsOf? d.decls = .ok s.decls ∧ sitesOfP? s.decls "plain" 0 d.processes = .ok s.statics ∧
    d.generates = s.fams.map TFam.toGen ∧ s.SpecOkP :=
  summaryG_spec siteOfP? siteOfP?_proc' h

theorem lsitesP_spec {s : Summary}
    (hsta : ∀ st ∈ s.statics, ∃ pos p, siteOfP? s.decls pos p = .ok st) (hspec : s.SpecOkP) :
    ∀ ls ∈ s.lsites, ∃ pos p, siteOfP? s.decls pos p = .ok ls.site :=
  lsitesG_spec siteOfP? hsta hspec

/-! ## Axiom pins (standard axioms only) -/

/-- info: 'LeanModels.Sv.CombView.siteOfP?_cases' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms siteOfP?_cases

/-- info: 'LeanModels.Sv.CombView.siteOfP?_proc' depends on axioms: [propext, Quot.sound] -/
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

/-- info: 'LeanModels.Sv.CombView.siteOfP?_proc'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms siteOfP?_proc'

end CombView
end LeanModels.Sv
