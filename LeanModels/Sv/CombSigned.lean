import LeanModels.Sv.CombEqShape
import LeanModels.Sv.CombEqThm

/-!
# Signed reads: a design and its unsigned twin instantiate to the same design

`PDesign.unsign` (`CombView.lean`) removes the cast marker of every signed read the recognizer reads as a value leaf,
and from the base of a bit or part select in those positions (a select is unsigned, IEEE 1800-2023 §11.8.1; it lowers as
the select of the plain signal, `instExpr2_bitSel_castU`/`instExpr2_partSel_castU`).
This file proves that, under the width contract of `sv_equations` (`Summary.WidthObl`: every bare access exactly as
wide as its context, so no signed operand is ever implicitly widened), the design as written and its unsigned twin
instantiate to the SAME `Design2` (`instantiateGD2_unsign`). The `sv_comb` tactics summarize the twin and rewrite the
goal along this equation, so every theorem they produce remains a theorem about ls-sv's semantics of the design as
written: nothing is assumed about signedness, and the width obligation is a goal the player closes.

Why the equation holds: `instExpr2` lets the cast marker vanish, and `fitExpr2` treats a marked operand differently only
when it is narrower than its context (`Resize:signed`, loud), which the width contract excludes. The per-site statement
is `proc_shapeCU` (built on the shape theorems of `CombEqShape.lean`): a process and its twin instantiate to the same assign. The rest of this file
carries that through the generate expansion: the summary of the design as written is the twin's summary with the
original processes put back (`siteOfU?`, `summaryG_unsign`), and the realized process lists agree site by site
(`Summary.enum_congr`).

A signed comparison of two signed signals declared with the same dimensions, or of a signed signal with a constant (a
sized literal as wide as the signal's constant width, an unsized constant against a signal of a constant width of at
least 32 bits: no operand is extended), is read as written: the twin keeps it (`PExpr.unsign` does not enter `s<` …),
and the shape theorems lower it to `Expr2.scmp` of the two fitted operands (`Sk.scmp` over `rd`, `lit` and `const`).
So is the left operand of a shift: the twin does not enter a shift, and the reader of a shift operand (`rdsOfD?`, the
mirror of `instDivOperand2`) reads a signed read there as the plain read and the `SignedResize` marker as the sign
extension it is (`Sk.fit true`, `XF.sext`), at the signedness of the shift; `Sk.sh` with the signed flag lowers `>>>` to
`BinOp.ashr true` (`XF.ashrBits`). What else signedness changes is outside the fragment and stays refused: a sign
extension outside a shift operand (the extractor marks it `ConversionExpression:width`), a signed comparison of other
operands, a signed shift amount, signed `/` and `%`, a signed read in an index, and a signed read other than in a shift
operand, or a signed comparison, in an `always_comb` body (the twin is defined on continuous assigns; an `always_comb`
body would need a statement-level twin and its instantiation theorem through the procedural lowering).
-/

namespace LeanModels.Sv
namespace CombView

/-! ## Relabelling the processes of a summary -/

def TSite.mapProc (g : PProcess → PProcess) (st : TSite) : TSite := { st with proc := g st.proc }

def TInner.mapProcs (g : PProcess → PProcess) (l : TInner) : TInner :=
  { l with body := l.body.map (TSite.mapProc g) }

def TItem.mapProcs (g : PProcess → PProcess) : TItem → TItem
  | .site st => .site (st.mapProc g)
  | .loop l => .loop (l.mapProcs g)

def TFam.mapProcs (g : PProcess → PProcess) (f : TFam) : TFam :=
  { f with body := f.body.map (TItem.mapProcs g) }

def Summary.mapProcs (g : PProcess → PProcess) (s : Summary) : Summary :=
  { s with statics := s.statics.map (TSite.mapProc g), fams := s.fams.map (TFam.mapProcs g) }

def LSite.mapProc (g : PProcess → PProcess) (ls : LSite) : LSite := { ls with site := ls.site.mapProc g }

theorem TFam.lsites_mapProcs (g : PProcess → PProcess) (f : TFam) :
    (f.mapProcs g).lsites = f.lsites.map (LSite.mapProc g) := by
  unfold TFam.lsites TFam.mapProcs
  simp only [List.flatMap_map, List.map_flatMap]
  congr 1
  funext it
  cases it with
  | site st => rfl
  | loop l => simp [TFam.itemLs, TItem.mapProcs, TInner.mapProcs, LSite.mapProc, Function.comp_def]

theorem Summary.lsites_mapProcs (g : PProcess → PProcess) (s : Summary) :
    (s.mapProcs g).lsites = s.lsites.map (LSite.mapProc g) := by
  unfold Summary.lsites Summary.mapProcs
  simp only [List.map_append, List.map_map, List.flatMap_map, List.map_flatMap, TFam.lsites_mapProcs]
  rfl

theorem Summary.hdrPaths_mapProcs (g : PProcess → PProcess) (s : Summary) :
    (s.mapProcs g).hdrPaths = s.hdrPaths := by
  unfold Summary.hdrPaths Summary.mapProcs
  simp only [List.flatMap_map]
  congr 1
  funext f
  simp only [TFam.mapProcs, List.filterMap_map]
  congr 1
  congr 1
  funext it
  cases it <;> rfl

theorem Summary.enum_mapProcs {β : Type} (g : PProcess → PProcess) (s : Summary)
    (b : LSite → (String → Int) → IEnv → β) (σ : String → Int) (E : IEnv) :
    (s.mapProcs g).enum b σ E = s.enum (fun ls σ' E' => b (ls.mapProc g) σ' E') σ E := by
  unfold Summary.enum Summary.mapProcs
  simp only [List.map_map, List.flatMap_map]
  congr 1
  congr 1
  funext f
  unfold TFam.enum TFam.mapProcs
  simp only [List.flatMap_map]
  congr 1
  funext i
  congr 1
  funext it
  cases it with
  | site st => rfl
  | loop l => simp [TFam.itemEnum, TItem.mapProcs, TInner.mapProcs, LSite.mapProc, List.map_map, Function.comp_def]

theorem TFam.wf_mapProcs (g : PProcess → PProcess) (f : TFam) (h : (f.mapProcs g).Wf) : f.Wf := by
  revert h
  unfold TFam.Wf TFam.mapProcs
  simp only [List.forall_mem_map]
  intro h
  refine ⟨h.1, fun it hit => ?_⟩
  have := h.2 it hit
  cases it with
  | site st => trivial
  | loop l => exact this

theorem Summary.structOk_of_mapProcs {g : PProcess → PProcess} {s : Summary}
    (h : (s.mapProcs g).StructOk) : s.StructOk := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  rw [Summary.lsites_mapProcs] at h2 h3 h4 h7 h8
  rw [Summary.hdrPaths_mapProcs] at h5
  simp only [List.forall_mem_map] at h2 h3 h4 h7
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
  rw [List.pairwise_map] at h8
  exact h8

theorem Summary.autoObl_of_mapProcs {g : PProcess → PProcess} {s : Summary} {σ : String → Int} {args : List Int}
    (h : (s.mapProcs g).AutoObl σ args) : s.AutoObl σ args := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [Summary.lsites_mapProcs] at h1 h2
  rw [Summary.hdrPaths_mapProcs] at h3
  simp only [List.forall_mem_map] at h1 h2
  exact ⟨h1, h2, h3⟩

/-! ## The recognizer of the design as written -/

/-- The site of a process as written: the twin's site, with the process as written stored. -/
def siteOfU? (ds : List DeclT) (pos : Nat) (p : PProcess) : Except String TSite :=
  match siteOf? ds pos p.unsign with
  | .ok st => .ok { st with proc := p }
  | .error e => .error e

theorem siteOfU?_proc : ∀ (ds : List DeclT) (pos : Nat) (p : PProcess) (st : TSite),
    siteOfU? ds pos p = .ok st → st.proc = p := by
  intro ds pos p st h
  unfold siteOfU? at h
  split at h
  · cases h; rfl
  · cases h

theorem siteOfU?_of {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite}
    (h : siteOf? ds pos p.unsign = .ok st) :
    siteOfU? ds pos p = .ok { st with proc := p } ∧ ({ st with proc := p } : TSite).mapProc PProcess.unsign = st := by
  refine ⟨by simp [siteOfU?, h], ?_⟩
  have hp := siteOf?_proc h
  cases st
  simp only [TSite.mapProc] at hp ⊢
  rw [hp]

theorem sitesOfG_unsign {ds : List DeclT} {tag : String} :
    ∀ {ps : List PProcess} {pos : Nat} {sts : List TSite},
      sitesOfG siteOf? ds tag pos (ps.map PProcess.unsign) = .ok sts →
      ∃ sts', sitesOfG siteOfU? ds tag pos ps = .ok sts' ∧ sts'.map (TSite.mapProc PProcess.unsign) = sts
  | [], pos, sts, h => by
      simp only [List.map_nil, sitesOfG, Except.ok.injEq] at h
      subst h
      exact ⟨[], rfl, rfl⟩
  | p :: ps, pos, sts, h => by
      simp only [List.map_cons, sitesOfG] at h
      rcases hs : siteOf? ds pos p.unsign with e | st
      · simp [hs] at h
      · rcases hr : sitesOfG siteOf? ds tag (pos + 1) (ps.map PProcess.unsign) with e | sts1
        · simp [hs, hr] at h
        · simp only [hs, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨hu, hm⟩ := siteOfU?_of hs
          obtain ⟨sts', h1, h2⟩ := sitesOfG_unsign hr
          refine ⟨{ st with proc := p } :: sts', ?_, by simp [hm, h2]⟩
          simp [sitesOfG, hu, h1]

theorem procsOf?_unsignL : ∀ {l : List GenItem} {ps : List PProcess},
    procsOf? (GenItem.unsignL l) = some ps → ∃ ps0, procsOf? l = some ps0 ∧ ps = ps0.map PProcess.unsign
  | [], ps, h => by simp [GenItem.unsignL, procsOf?] at h; subst h; exact ⟨[], rfl, rfl⟩
  | .process p :: rest, ps, h => by
      simp only [GenItem.unsignL, GenItem.unsign, procsOf?] at h
      rcases hr : procsOf? (GenItem.unsignL rest) with _ | qs
      · simp [hr] at h
      · simp only [hr, Option.some.injEq] at h
        subst h
        obtain ⟨q0, hq0, rfl⟩ := procsOf?_unsignL hr
        exact ⟨p :: q0, by simp [procsOf?, hq0], rfl⟩
  | .genFor .. :: _, _, h => by simp [GenItem.unsignL, GenItem.unsign, procsOf?] at h
  | .genIf .. :: _, _, h => by simp [GenItem.unsignL, GenItem.unsign, procsOf?] at h
  | .unsupported .. :: _, _, h => by simp [GenItem.unsignL, GenItem.unsign, procsOf?] at h
  | .inst _ :: _, _, h => by simp [GenItem.unsignL, GenItem.unsign, procsOf?] at h

theorem itemOfG_unsign {ds : List DeclT} {tag : String} {pos : Nat} {it : GenItem} {x : TItem}
    (h : itemOfG siteOf? ds tag pos it.unsign = .ok x) :
    ∃ x', itemOfG siteOfU? ds tag pos it = .ok x' ∧ x'.mapProcs PProcess.unsign = x := by
  cases it with
  | process p =>
      simp only [GenItem.unsign, itemOfG] at h
      rcases hs : siteOf? ds pos p.unsign with e | st
      · simp [hs] at h
      · simp only [hs, Except.ok.injEq] at h
        subst h
        obtain ⟨hu, hm⟩ := siteOfU?_of hs
        exact ⟨.site { st with proc := p }, by simp [itemOfG, hu], by simp [TItem.mapProcs, hm]⟩
  | genFor label g initE bound step rc body =>
      simp only [GenItem.unsign, itemOfG] at h
      rcases hh : hdrOf? label g initE bound step with e | h0
      · simp [hh] at h
      · simp only [hh] at h
        rcases hp : procsOf? (GenItem.unsignL body) with _ | ps
        · simp [hp] at h
        · simp only [hp] at h
          obtain ⟨ps0, hp0, rfl⟩ := procsOf?_unsignL hp
          rcases hsx : sitesOfG siteOf? ds h0.name 0 (ps0.map PProcess.unsign) with e | sts
          · simp [hsx] at h
          · simp only [hsx, Except.ok.injEq] at h
            subst h
            obtain ⟨sts', h1, h2⟩ := sitesOfG_unsign hsx
            exact ⟨.loop ⟨h0, rc, sts'⟩, by simp [itemOfG, hh, hp0, h1],
              by simp [TItem.mapProcs, TInner.mapProcs, h2]⟩
  | genIf c t e => simp [GenItem.unsign, itemOfG] at h
  | unsupported k t => simp [GenItem.unsign, itemOfG] at h
  | inst i => simp [GenItem.unsign, itemOfG] at h

theorem itemsOfG_unsign {ds : List DeclT} {tag : String} :
    ∀ {its : List GenItem} {pos : Nat} {xs : List TItem},
      itemsOfG siteOf? ds tag pos (GenItem.unsignL its) = .ok xs →
      ∃ xs', itemsOfG siteOfU? ds tag pos its = .ok xs' ∧ xs'.map (TItem.mapProcs PProcess.unsign) = xs
  | [], pos, xs, h => by
      simp only [GenItem.unsignL, itemsOfG, Except.ok.injEq] at h
      subst h
      exact ⟨[], rfl, rfl⟩
  | it :: rest, pos, xs, h => by
      simp only [GenItem.unsignL, itemsOfG] at h
      rcases hx : itemOfG siteOf? ds tag pos it.unsign with e | x
      · simp [hx] at h
      · rcases hr : itemsOfG siteOf? ds tag (pos + 1) (GenItem.unsignL rest) with e | xs1
        · simp [hx, hr] at h
        · simp only [hx, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨x', h1, h2⟩ := itemOfG_unsign hx
          obtain ⟨xs', k1, k2⟩ := itemsOfG_unsign hr
          exact ⟨x' :: xs', by simp [itemsOfG, h1, k1], by simp [h2, k2]⟩

theorem famOfG_unsign {ds : List DeclT} {it : GenItem} {f : TFam}
    (h : famOfG siteOf? ds it.unsign = .ok f) :
    ∃ f', famOfG siteOfU? ds it = .ok f' ∧ f'.mapProcs PProcess.unsign = f := by
  cases it with
  | genFor label g initE bound step rc body =>
      simp only [GenItem.unsign, famOfG] at h
      rcases hh : hdrOf? label g initE bound step with e | h0
      · simp [hh] at h
      · simp only [hh] at h
        rcases hi : itemsOfG siteOf? ds h0.name 0 (GenItem.unsignL body) with e | its
        · simp [hi] at h
        · simp only [hi, Except.ok.injEq] at h
          subst h
          obtain ⟨its', h1, h2⟩ := itemsOfG_unsign hi
          exact ⟨⟨h0, rc, its'⟩, by simp [famOfG, hh, h1], by simp [TFam.mapProcs, h2]⟩
  | process p => simp [GenItem.unsign, famOfG] at h
  | genIf c t e => simp [GenItem.unsign, famOfG] at h
  | unsupported k t => simp [GenItem.unsign, famOfG] at h
  | inst i => simp [GenItem.unsign, famOfG] at h

theorem famsOfG_unsign {ds : List DeclT} :
    ∀ {gens : List GenItem} {fs : List TFam},
      famsOfG siteOf? ds (GenItem.unsignL gens) = .ok fs →
      ∃ fs', famsOfG siteOfU? ds gens = .ok fs' ∧ fs'.map (TFam.mapProcs PProcess.unsign) = fs
  | [], fs, h => by
      simp only [GenItem.unsignL, famsOfG, Except.ok.injEq] at h
      subst h
      exact ⟨[], rfl, rfl⟩
  | it :: rest, fs, h => by
      simp only [GenItem.unsignL, famsOfG] at h
      rcases hf : famOfG siteOf? ds it.unsign with e | f
      · simp [hf] at h
      · rcases hr : famsOfG siteOf? ds (GenItem.unsignL rest) with e | fs1
        · simp [hf, hr] at h
        · simp only [hf, hr, Except.ok.injEq] at h
          subst h
          obtain ⟨f', h1, h2⟩ := famOfG_unsign hf
          obtain ⟨fs', k1, k2⟩ := famsOfG_unsign hr
          exact ⟨f' :: fs', by simp [famsOfG, h1, k1], by simp [h2, k2]⟩

/-- **The summary of the design as written** is the twin's, with the processes as written put back. -/
theorem summaryG_unsign {d : PDesign} {s : Summary} (hs : d.unsign.summary = .ok s) :
    ∃ s', d.summaryG siteOfU? = .ok s' ∧ s'.mapProcs PProcess.unsign = s := by
  unfold PDesign.summary PDesign.summaryG at hs
  unfold PDesign.summaryG
  have hpar : d.unsign.params = d.params := rfl
  have hlp : d.unsign.localParams = d.localParams := rfl
  have hen : d.unsign.enums = d.enums := rfl
  have hot : d.unsign.others = d.others := rfl
  have hde : d.unsign.decls = d.decls := rfl
  have hpr : d.unsign.processes = d.processes.map PProcess.unsign := rfl
  have hge : d.unsign.generates = GenItem.unsignL d.generates := rfl
  rw [hpar, hlp, hen, hot, hde, hpr, hge] at hs
  rcases hl : lpsOf? (d.params.map (·.name)) d.localParams with e | lps
  · simp [hl] at hs
  simp only [hl] at hs ⊢
  by_cases h2 : d.enums.isEmpty = false
  · simp [h2] at hs
  have h2' : d.enums.isEmpty = true := by simpa using h2
  by_cases h3 : d.others.isEmpty = false
  · simp [h2', h3] at hs
  have h3' : d.others.isEmpty = true := by simpa using h3
  simp only [h2', h3', Bool.not_true, Bool.false_eq_true, if_false] at hs ⊢
  rcases hd : declsOf? d.decls with e | ds
  · simp [hd] at hs
  simp only [hd] at hs ⊢
  rcases hp : sitesOfG siteOf? ds "plain" 0 (d.processes.map PProcess.unsign) with e | sts
  · simp [hp] at hs
  rcases hg : famsOfG siteOf? ds (GenItem.unsignL d.generates) with e | fs
  · simp [hp, hg] at hs
  simp only [hp, hg, Except.ok.injEq] at hs
  subst hs
  obtain ⟨sts', h1, h2⟩ := sitesOfG_unsign hp
  obtain ⟨fs', k1, k2⟩ := famsOfG_unsign hg
  refine ⟨Summary.mk (d.params.map (·.name) ++ lps.map Prod.fst) ds sts' fs' lps, by simp only [h1, k1], ?_⟩
  simp [Summary.mapProcs, h2, k2]

/-! ## Enumerations that agree at every reached site -/

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem Summary.enum_congr {β : Type} (s : Summary) (b₁ b₂ : LSite → (String → Int) → IEnv → β)
    (σ : String → Int) (E : IEnv)
    (h : ∀ ls ∈ s.lsites, ∀ σ' E', ReachE ls.hdrs σ E σ' E' → b₁ ls σ' E' = b₂ ls σ' E') :
    s.enum b₁ σ E = s.enum b₂ σ E := by
  unfold Summary.enum
  congr 1
  · apply List.map_congr_left
    intro st hst
    exact h _ (by simp [Summary.lsites, hst]) σ E ⟨rfl, rfl⟩
  · apply flatMap_congr_mem
    intro f hf
    unfold TFam.enum
    apply flatMap_congr_mem
    intro i hi
    have hri : f.hdr.Rng σ i := Hdr.mem_range.mp hi
    apply flatMap_congr_mem
    intro it hit
    cases it with
    | site st =>
        simp only [TFam.itemEnum, List.cons.injEq, and_true]
        refine h _ ?_ _ _ ⟨i, hri, rfl, rfl⟩
        simp only [Summary.lsites, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨f, hf, by simp [TFam.lsites, TFam.itemLs]; exact ⟨_, hit, by simp [TFam.itemLs]⟩⟩
    | loop l =>
        simp only [TFam.itemEnum]
        apply flatMap_congr_mem
        intro j hj
        have hrj := Hdr.mem_range.mp hj
        apply List.map_congr_left
        intro st hst
        refine h _ ?_ _ _ ⟨i, hri, j, hrj, rfl, rfl⟩
        simp only [Summary.lsites, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨f, hf, by simp [TFam.lsites]; exact ⟨_, hit, by simp [TFam.itemLs, hst]⟩⟩

end CombView

/-! ## The bridge -/

namespace CombEq
open CombView

theorem unsign_proc_assign {p : PProcess} {t : String} {v' : PExpr} (h : p.unsign = .assign t v') :
    ∃ v, p = .assign t v ∧ v.unsign = v' := by
  cases p with
  | assign t0 v0 => simp only [PProcess.unsign, PProcess.assign.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨v0, rfl, rfl⟩
  | assignL => simp [PProcess.unsign] at h
  | _ => simp [PProcess.unsign] at h

theorem unsign_proc_assignL {p : PProcess} {l : PLhs} {v' : PExpr} (h : p.unsign = .assignL l v') :
    ∃ v, p = .assignL l v ∧ v.unsign = v' := by
  cases p with
  | assignL l0 v0 => simp only [PProcess.unsign, PProcess.assignL.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨v0, rfl, rfl⟩
  | assign => simp [PProcess.unsign] at h
  | _ => simp [PProcess.unsign] at h

section proc
variable {σ : String → Int} {E : IEnv} {elems : List (String × Nat)}
  {DW : String → Option Nat} {DG : String → Option (List (Int × Int))}
  {EW : String → Option Nat} {ns : List String}

/-- **`proc_shapeC` for a process whose unsigned twin is a site**: the process as written instantiates to the assign
the twin's skeleton promises. -/
theorem proc_shapeCU (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite} (hs : siteOf? ds pos p.unsign = .ok st)
    (hso : ∀ a ∈ st.tgt :: st.rds, AccOK σ DW DG EW ns a) (hcn : st.ConstOK σ ns)
    (hf : fragOk (rhsOf p.unsign) = true)
    (hw : (skRhs (rhsOf p.unsign) st.rds).WidthOkC σ dw (st.tgt.win σ dw).2.2) :
    instProcess2 E elems p =
      .assign (st.tgt.lhs σ) ((skRhs (rhsOf p.unsign) st.rds).low σ dw (st.tgt.win σ dw).2.2) := by
  have hrdacc : ∀ rds, rds = st.rds → ∀ a ∈ rds, AccOK σ DW DG EW ns a := by
    rintro rds rfl a ha
    exact hso a (List.mem_cons_of_mem _ ha)
  rcases siteOf?_cases hs with ⟨t, v', rds, hpu, hrds, rfl⟩ | ⟨l, v', tg, rds, hpu, htg, hrds, rfl⟩
  · obtain ⟨v, rfl, rfl⟩ := unsign_proc_assign hpu
    have hdt : (DW t).isSome = true := (hso _ (List.mem_cons_self ..)).1
    have hW : E.widths.lookup t = some (dw t) := by
      rw [C.widths t]; exact hdw t hdt
    rw [instProcess2_assign v hW]
    simp only [PProcess.unsign, rhsOf] at hf hw ⊢
    have := rhs_shapeCU C hdw hrds hf (hrdacc _ rfl) hcn hw
    simpa [Acc.win, Acc.lhs] using this
  · obtain ⟨v, rfl, rfl⟩ := unsign_proc_assignL hpu
    rw [instProcess2_assignL v (instLhs_acc_w C hdw htg (hso _ (List.mem_cons_self ..)))]
    simp only [PProcess.unsign, rhsOf] at hf hw ⊢
    rw [rhs_shapeCU C hdw hrds hf (hrdacc _ rfl) hcn hw]

/-- **A process and its unsigned twin instantiate to the same process**, under the width contract. -/
theorem instProcess2_unsign (C : Ctx σ E elems DW DG EW ns) {dw : String → Nat}
    (hdw : ∀ n, (DW n).isSome = true → DW n = some (dw n))
    {ds : List DeclT} {pos : Nat} {p : PProcess} {st : TSite} (hs : siteOf? ds pos p.unsign = .ok st)
    (hso : ∀ a ∈ st.tgt :: st.rds, AccOK σ DW DG EW ns a) (hcn : st.ConstOK σ ns)
    (hf : fragOk (rhsOf p.unsign) = true)
    (hw : (skRhs (rhsOf p.unsign) st.rds).WidthOkC σ dw (st.tgt.win σ dw).2.2) :
    instProcess2 E elems p = instProcess2 E elems p.unsign := by
  rw [proc_shapeCU C hdw hs hso hcn hf hw, proc_shapeC C hdw hs hso hcn hf hw]

end proc

/-- `Design2` equality from its three fields. -/
theorem design2_ext {a b : Design2} (h1 : a.name = b.name) (h2 : a.decls.toList = b.decls.toList)
    (h3 : a.processes.toList = b.processes.toList) : a = b := by
  cases a; cases b
  simp only at h1 h2 h3
  subst h1
  rw [Array.toList_inj] at h2 h3
  subst h2 h3
  rfl

/-- **The design as written and its unsigned twin instantiate to the same design**, given the twin's summary and the
obligations of `sv_equations` that concern instantiation (the parameter stage, the structural facts, the in-range,
fragment, width and bit-read obligations). -/
theorem instantiate2_unsign {d : PDesign} {s : Summary} (hs : d.unsign.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hfrag : s.EqFrag) (hwid : s.WidthObl σ) (hbit : s.BitReadObl σ) :
    d.instantiate2 args (PDesign.surfaceFuel args) = d.unsign.instantiate2 args (PDesign.surfaceFuel args) := by
  -- the twin
  obtain ⟨-, -, hoth, -, hsd, hsts, hgen, hspec⟩ := summary_spec hs
  obtain ⟨hproc, hsites0⟩ := sitesOf?_spec hsts
  have hsites := lsites_spec hsites0 hspec
  have h1u : d.unsign.paramEnv2 args = .ok env := h1
  obtain ⟨C, M, hM, hMd, hMp⟩ :=
    sound_prefix (d := d.unsign) harity h1u hag hok hauto hoth hsd hproc hgen (fun f hf => (hspec f hf).1)
  -- the design as written
  obtain ⟨s', hs', hrel⟩ := summaryG_unsign hs
  obtain ⟨-, -, hoth', -, hsd', hsts', hgen', hspec'⟩ := summaryG_spec siteOfU? siteOfU?_proc hs'
  obtain ⟨hproc', -⟩ := sitesOfG_spec siteOfU? siteOfU?_proc hsts'
  subst hrel
  have hok' := Summary.structOk_of_mapProcs hok
  have hauto' := Summary.autoObl_of_mapProcs hauto
  obtain ⟨-, M', hM', hM'd, hM'p⟩ :=
    sound_prefix (d := d) (s := s') harity h1 hag hok' hauto' hoth' hsd' hproc' hgen'
      (fun f hf => (hspec' f hf).1)
  rw [hM, hM']
  congr 1
  apply design2_ext
  · obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := PDesign.instantiate2_eq_ok_iff.mp hM'
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl⟩ := PDesign.instantiate2_eq_ok_iff.mp hM
    rfl
  · rw [hM'd, hMd]; rfl
  · rw [hM'p, hMp]
    unfold Summary.pairs
    rw [Summary.enum_mapProcs]
    congr 1
    apply Summary.enum_congr
    intro ls hls σ' E' hr
    simp only [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    -- the twin's site
    have hls2 : ls.mapProc PProcess.unsign ∈ (s'.mapProcs PProcess.unsign).lsites := by
      rw [Summary.lsites_mapProcs]; exact List.mem_map_of_mem hls
    have hr2 : ReachE (ls.mapProc PProcess.unsign).hdrs σ (env.withDecls ((s'.mapProcs PProcess.unsign).decls.map
        (DeclT.toDecl σ))) σ' E' := hr
    obtain ⟨pos, p, hp⟩ := hsites _ hls2
    have hpp := siteOf?_proc hp
    have hb : ∀ r ∈ (ls.mapProc PProcess.unsign).site.rds, accBitUpper ((s'.mapProcs PProcess.unsign).dw σ) σ' r :=
      (Loops.all_iff _ _ _).mp (hbit _ hls2) σ' (ReachE_Reach hr2)
    obtain ⟨C', hso, -⟩ := site_ok C hok hauto hin hls2 hr2 hb
    have hw := (Loops.all_iff _ _ _).mp (hwid _ hls2) σ' (ReachE_Reach hr2)
    have hf := (hfrag _ hls2).1
    have hco := site_co hok hin hls2 (ReachE_Reach hr2)
    have hdw : ∀ n, ((s'.mapProcs PProcess.unsign).DW σ n).isSome = true →
        (s'.mapProcs PProcess.unsign).DW σ n = some ((s'.mapProcs PProcess.unsign).dw σ n) :=
      fun n h => dw_some n h
    subst hpp
    exact instProcess2_unsign C' hdw (p := ls.site.proc) hp hso hco hf hw

/-- **`instantiate2_unsign` at the comb family** `X.sem`'s unguarded twin (`PDesign.instantiateGD2`). -/
theorem instantiateGD2_unsign {d : PDesign} {s : Summary} (hs : d.unsign.summary = .ok s) {args : List Int}
    {σ : String → Int} {env : IEnv} (harity : args.length = d.params.length)
    (h1 : d.paramEnv2 args = .ok env) (hag : Agrees σ env s.params) (hok : s.StructOk)
    (hauto : s.AutoObl σ args) (hin : s.InRangeObl σ)
    (hfrag : s.EqFrag) (hwid : s.WidthObl σ) (hbit : s.BitReadObl σ) :
    d.instantiateGD2 args = d.unsign.instantiateGD2 args := by
  have h := instantiate2_unsign hs harity h1 hag hok hauto hin hfrag hwid hbit
  unfold PDesign.instantiateGD2 PDesign.instantiateG2 PDesign.driverGuard
  rw [h]
  rfl

/-- `instantiateGD2_unsign` with the hypotheses in the shape of the comb theorems' views (`comb_view`, `eq_view`, …:
the parameter agreement as an equation of two maps at the canonical valuation `s.val args`, the arity and the parameter
stage read on the twin), so that the tactics can share these goals between the bridge and the view. -/
theorem instantiateGD2_unsign_view {d : PDesign} {s : Summary} {args : List Int} {env : IEnv}
    (hs : d.unsign.summary = .ok s) (harity : args.length = d.unsign.params.length)
    (h1 : d.unsign.paramEnv2 args = .ok env)
    (hag : s.params.map (fun n => env.intVal? n) = s.params.map (fun n => some (s.val args n)))
    (hok : s.StructOk) (hauto : s.AutoObl (s.val args) args) (hin : s.InRangeObl (s.val args))
    (hfrag : s.EqFrag) (hwid : s.WidthObl (s.val args)) (hbit : s.BitReadObl (s.val args)) :
    d.instantiateGD2 args = d.unsign.instantiateGD2 args :=
  instantiateGD2_unsign hs harity h1 (Agrees_of_map hag) hok hauto hin hfrag hwid hbit

end CombEq
end LeanModels.Sv

/-! ## Axiom pins -/

/-- info: 'LeanModels.Sv.CombEq.instantiateGD2_unsign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombEq.instantiateGD2_unsign

/-- info: 'LeanModels.Sv.CombEq.instantiateGD2_unsign_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombEq.instantiateGD2_unsign_view

/-- info: 'LeanModels.Sv.CombEq.skT_shapeCU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LeanModels.Sv.CombEq.skT_shapeCU
