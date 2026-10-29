import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Comb2Base

/-!
# `sv_structure`, stage 1: the family summary of a `PDesign` and its soundness

Step 4 of `docs/sv-comb-design.md` §7 (design principle 6): a TRANSIENT view derived from
`PDesign`, with a soundness theorem against `PDesign.instantiate2`. Nothing here is a new
design AST or a new evaluator: the summary is read off the template (`PDesign.summary`,
structural recursion, evaluated by the kernel/unifier) and everything it claims is proved
against the real instantiation (`instProcess2`, `expandList2`, `buildDecls`, `dimTable`), using
the `Gen2.lean` handles.

## The fragment (v0)

A flat top whose processes are continuous assigns (`assign x = e`, `assign x[idx] = e`,
`assign x[idx] = e` over a packed array) plus at most ONE `generate for` over a genvar
`for (g = c0; g < bound; g++)` of such assigns. Targets and reads are whole signals or
single-bit selects whose indices are AFFINE in the genvar and the parameters (`i`, `i + 1`,
`N`, `N - 1`); declarations are scalars or 1-D packed vectors with affine bounds; every
expression is a tree of `&`/`|`/`^` over such reads and literals. Everything else is refused
with a specific message (`PDesign.summary` returns `.error msg`).

## What is claimed

* `PDesign.summary d = .ok s` computes the sites (`TSite`: write window and read windows as
  affine functions of the loop index) and the declaration geometry.
* `Summary.pairs` is the closed-form list `statics ++ (range).flatMap body` (a `flatMap` over
  the index range, never an enumeration) of `(SiteInst, Process2)` pairs: the footprint the
  summary promises next to the process `instProcess2` really builds.
* `site_desc` (the per-site soundness theorem): the real process IS an `assign` whose target
  is EXACTLY the promised one and whose reads are CONTAINED in the promised ones (equal when
  every array read is in range; `rhsFree`/`rhsDeclared` facts included).
* The `Summary.sound` theorem in `CombViewThm.lean` assembles them against `instantiate2`.
-/

namespace LeanModels.Sv
namespace CombView

/-! ## Affine terms -/

/-- `Σ k·n + c` over named integers (genvars and parameters). -/
structure Aff where
  terms : List (String × Int) := []
  c : Int := 0
deriving Repr, BEq, DecidableEq, Inhabited

namespace Aff

def const (c : Int) : Aff := { c := c }
def var (n : String) : Aff := { terms := [(n, 1)] }
def add (a b : Aff) : Aff := { terms := a.terms ++ b.terms, c := a.c + b.c }

def negTerms : List (String × Int) → List (String × Int)
  | [] => []
  | (n, k) :: ts => (n, -k) :: negTerms ts

def neg (a : Aff) : Aff := { terms := negTerms a.terms, c := -a.c }
def sub (a b : Aff) : Aff := a.add b.neg
def names (a : Aff) : List String := a.terms.map Prod.fst

def evalTerms (σ : String → Int) : List (String × Int) → Int
  | [] => 0
  | (n, k) :: ts => k * σ n + evalTerms σ ts

def eval (σ : String → Int) (a : Aff) : Int := evalTerms σ a.terms + a.c

theorem evalTerms_append (σ : String → Int) (a b : List (String × Int)) :
    evalTerms σ (a ++ b) = evalTerms σ a + evalTerms σ b := by
  induction a with
  | nil => simp [evalTerms]
  | cons p ts ih => obtain ⟨n, k⟩ := p; simp [evalTerms, ih, Int.add_assoc]

theorem evalTerms_negTerms (σ : String → Int) (a : List (String × Int)) :
    evalTerms σ (negTerms a) = - evalTerms σ a := by
  induction a with
  | nil => simp [negTerms, evalTerms]
  | cons p ts ih =>
    obtain ⟨n, k⟩ := p
    simp [negTerms, evalTerms, ih, Int.neg_mul, Int.neg_add]

theorem names_negTerms (a : List (String × Int)) :
    (negTerms a).map Prod.fst = a.map Prod.fst := by
  induction a with
  | nil => simp [negTerms]
  | cons p ts ih => obtain ⟨n, k⟩ := p; simp [negTerms, ih]

theorem eval_add (σ : String → Int) (a b : Aff) : (a.add b).eval σ = a.eval σ + b.eval σ := by
  simp only [eval, add, evalTerms_append]
  omega

theorem eval_neg (σ : String → Int) (a : Aff) : a.neg.eval σ = - a.eval σ := by
  simp only [eval, neg, evalTerms_negTerms]
  omega

theorem eval_sub (σ : String → Int) (a b : Aff) : (a.sub b).eval σ = a.eval σ - b.eval σ := by
  rw [sub, eval_add, eval_neg]
  omega

theorem eval_const (σ : String → Int) (c : Int) : (const c).eval σ = c := by
  simp [eval, const, evalTerms]

theorem eval_var (σ : String → Int) (n : String) : (var n).eval σ = σ n := by
  simp [eval, var, evalTerms]

theorem names_add (a b : Aff) : (a.add b).names = a.names ++ b.names := by
  simp [names, add]

theorem names_sub (a b : Aff) : (a.sub b).names = a.names ++ b.names := by
  simp [names, sub, add, neg, names_negTerms]

theorem evalTerms_congr (σ σ' : String → Int) (a : List (String × Int))
    (h : ∀ n ∈ a.map Prod.fst, σ n = σ' n) : evalTerms σ a = evalTerms σ' a := by
  induction a with
  | nil => rfl
  | cons p ts ih =>
    obtain ⟨n, k⟩ := p
    simp only [evalTerms]
    rw [h n (by simp), ih (fun m hm => h m (by simp [hm]))]

theorem eval_congr (σ σ' : String → Int) (a : Aff) (h : ∀ n ∈ a.names, σ n = σ' n) :
    a.eval σ = a.eval σ' := by
  simp only [eval]
  rw [evalTerms_congr σ σ' a.terms h]

end Aff

/-- The valuation `l` names (first binding wins, `0` when unbound). -/
def σL (l : List (String × Int)) : String → Int := fun n => (l.lookup n).getD 0

/-- Rebind one name (the genvar). -/
def bindσ (g : String) (i : Int) (σ : String → Int) : String → Int :=
  fun n => if n = g then i else σ n

@[simp] theorem bindσ_self (g : String) (i : Int) (σ : String → Int) : bindσ g i σ g = i := by
  simp [bindσ]

theorem bindσ_ne {g n : String} (h : n ≠ g) (i : Int) (σ : String → Int) :
    bindσ g i σ n = σ n := by
  simp [bindσ, h]

/-- `σ` agrees with the environment's constants on the listed names. -/
def Agrees (σ : String → Int) (E : IEnv) (ns : List String) : Prop :=
  ∀ n ∈ ns, E.vals.lookup n = some (σ n)

theorem Agrees.bindVal {σ : String → Int} {E : IEnv} {ns : List String} (h : Agrees σ E ns)
    (g : String) (i : Int) : Agrees (bindσ g i σ) (E.bindVal g i) (g :: ns) := by
  intro n hn
  simp only [IEnv.bindVal, List.lookup]
  by_cases hng : n = g
  · subst hng; simp
  · have hns : n ∈ ns := by
      rcases List.mem_cons.mp hn with h' | h'
      · exact absurd h' hng
      · exact h'
    have hb : (n == g) = false := by simpa using hng
    simp [hb, bindσ_ne hng, h n hns]

theorem Agrees.mono {σ : String → Int} {E : IEnv} {ns ms : List String} (h : Agrees σ E ns)
    (hs : ∀ n ∈ ms, n ∈ ns) : Agrees σ E ms := fun n hn => h n (hs n hn)

/-! ## Recognizing an affine constant expression -/

def affBin : SymBinOp → Aff → Aff → Option Aff
  | .m0 .add, a, b => some (a.add b)
  | .m0 .sub, a, b => some (a.sub b)
  | _, _, _ => none

def affOf? : PExpr → Option Aff
  | .int v => some (Aff.const v)
  | .genvarRef n => some (Aff.var n)
  | .paramRef n none => some (Aff.var n)
  | .binary op l r =>
      match affOf? l, affOf? r with
      | some a, some b => affBin op a b
      | _, _ => none
  | _ => none

theorem affBin_cases {op : SymBinOp} {a b c : Aff} (h : affBin op a b = some c) :
    (op = .m0 .add ∧ c = a.add b) ∨ (op = .m0 .sub ∧ c = a.sub b) := by
  unfold affBin at h
  split at h <;> simp_all

/-- **Affine recognition is sound**: an `Aff`-recognized expression is INT-class and evaluates
to its affine value, in every environment that binds the names it mentions. -/
theorem affOf?_sound {E : IEnv} {σ : String → Int} :
    ∀ (e : PExpr) (a : Aff), affOf? e = some a →
      (∀ n ∈ a.names, E.vals.lookup n = some (σ n)) →
      e.isInt E = true ∧ evalInt E e = .ok (a.eval σ)
  | .int v, a, h, _ => by
      simp only [affOf?, Option.some.injEq] at h
      subst h
      simp [PExpr.isInt, Aff.eval_const]
  | .genvarRef n, a, h, hb => by
      simp only [affOf?, Option.some.injEq] at h
      subst h
      have hl : E.vals.lookup n = some (σ n) := hb n (by simp [Aff.names, Aff.var])
      refine ⟨by simp [PExpr.isInt], ?_⟩
      rw [evalInt_genvarRef_of hl, Aff.eval_var]
  | .paramRef n none, a, h, hb => by
      simp only [affOf?, Option.some.injEq] at h
      subst h
      have hl : E.vals.lookup n = some (σ n) := hb n (by simp [Aff.names, Aff.var])
      refine ⟨isInt_paramRef_of hl, ?_⟩
      rw [evalInt_paramRef_of hl, Aff.eval_var]
  | .binary op l r, a, h, hb => by
      simp only [affOf?] at h
      rcases h1 : affOf? l with _ | a1 <;> rcases h2 : affOf? r with _ | a2 <;>
        simp only [h1, h2] at h <;> try exact absurd h (by simp)
      rcases affBin_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hb1 : ∀ n ∈ a1.names, E.vals.lookup n = some (σ n) :=
          fun n hn => hb n (by rw [Aff.names_add]; exact List.mem_append_left _ hn)
        have hb2 : ∀ n ∈ a2.names, E.vals.lookup n = some (σ n) :=
          fun n hn => hb n (by rw [Aff.names_add]; exact List.mem_append_right _ hn)
        obtain ⟨hi1, he1⟩ := affOf?_sound l a1 h1 hb1
        obtain ⟨hi2, he2⟩ := affOf?_sound r a2 h2 hb2
        exact ⟨isInt_binary_of (by simp) hi1 hi2, by rw [evalInt_add_of hi1 hi2 he1 he2, Aff.eval_add]⟩
      · have hb1 : ∀ n ∈ a1.names, E.vals.lookup n = some (σ n) :=
          fun n hn => hb n (by rw [Aff.names_sub]; exact List.mem_append_left _ hn)
        have hb2 : ∀ n ∈ a2.names, E.vals.lookup n = some (σ n) :=
          fun n hn => hb n (by rw [Aff.names_sub]; exact List.mem_append_right _ hn)
        obtain ⟨hi1, he1⟩ := affOf?_sound l a1 h1 hb1
        obtain ⟨hi2, he2⟩ := affOf?_sound r a2 h2 hb2
        exact ⟨isInt_binary_of (by simp) hi1 hi2, by rw [evalInt_sub_of hi1 hi2 he1 he2, Aff.eval_sub]⟩
  | .paramRef _ (some _), a, h, _ => by simp [affOf?] at h
  | .lit _, a, h, _ | .ident _, a, h, _ | .enumRef _ _ _, a, h, _ | .fill _, a, h, _
  | .unary _ _, a, h, _ | .ternary _ _ _, a, h, _ | .concat _, a, h, _ | .resize _ _, a, h, _
  | .signedResize _ _, a, h, _ | .squash2 _ _, a, h, _ | .sysCall _ _, a, h, _
  | .bitSel _ _, a, h, _ | .partSel _ _ _, a, h, _ | .repl _ _, a, h, _ | .reduce _ _, a, h, _
  | .cast _ _, a, h, _ | .arrayElem _ _, a, h, _ | .arrayPart _ _ _ _ _, a, h, _
  | .unsupported _ _, a, h, _ => by simp [affOf?] at h

/-! ## Template sites -/

/-- The identity of a rank site (design principle 13): a plain process by its position among the
module-level processes; a generate-family member by the block label, the position of the assign
inside the block, and the loop indices. -/
inductive SiteId where
  | plain (pos : Nat)
  | fam (label : String) (pos : Nat) (idx : List Int)
deriving Repr, DecidableEq, Inhabited

/-- The write of a template process. -/
inductive TTgt where
  | whole (n : String)
  | bit (n : String) (idx : Aff)
  | arr (n : String) (idx : Aff)
deriving Repr, DecidableEq, Inhabited

/-- One read of a template expression. -/
inductive TRd where
  | whole (n : String)
  | bit (n : String) (idx : Aff)
  | arr (n : String) (idx : Aff)
deriving Repr, DecidableEq, Inhabited

def TTgt.name : TTgt → String
  | .whole n => n | .bit n _ => n | .arr n _ => n

def TTgt.affs : TTgt → List Aff
  | .whole _ => [] | .bit _ a => [a] | .arr _ a => [a]

def TRd.name : TRd → String
  | .whole n => n | .bit n _ => n | .arr n _ => n

def TRd.affs : TRd → List Aff
  | .whole _ => [] | .bit _ a => [a] | .arr _ a => [a]

/-- A template process with its footprint: the write, the reads, and the process itself (the
equation schema kept for the later stages). -/
structure TSite where
  pos : Nat
  tgt : TTgt
  rds : List TRd
  proc : PProcess
deriving Repr, Inhabited

def TSite.names (st : TSite) : List String := st.tgt.name :: st.rds.map TRd.name

def TSite.affNames (st : TSite) : List String :=
  (st.tgt.affs.flatMap Aff.names) ++ (st.rds.flatMap fun r => r.affs.flatMap Aff.names)

/-- The bitwise gates of the fragment. -/
def gateOf : SymBinOp → Option BinOp
  | .m0 .and => some .and
  | .m0 .or => some .or
  | .m0 .xor => some .xor
  | _ => none

theorem gateOf_cases {op : SymBinOp} {b : BinOp} (h : gateOf op = some b) :
    op = .m0 b ∧ (b = .and ∨ b = .or ∨ b = .xor) := by
  unfold gateOf at h
  split at h <;> simp_all

/-- The reads of an expression of the fragment, or the reason it is outside it. -/
def rdsOf? : PExpr → Except String (List TRd)
  | .ident n => .ok [.whole n]
  | .lit _ => .ok []
  | .bitSel b i =>
      match b with
      | .ident n =>
          match affOf? i with
          | some a => .ok [.bit n a]
          | none => .error s!"read `{n}[…]` has a non-affine (dynamic or nonlinear) index"
      | _ => .error "bit select of a non-identifier base"
  | .arrayElem n is =>
      match is with
      | [i] =>
          match affOf? i with
          | some a => .ok [.arr n a]
          | none => .error s!"read `{n}[…]` has a non-affine (dynamic or nonlinear) index"
      | _ => .error s!"multi-dimensional array select `{n}[…][…]` (outside the v0 fragment)"
  | .binary op l r =>
      match gateOf op with
      | none => .error s!"operator `{op.sym}` is not a bitwise gate (`&`, `|`, `^`)"
      | some _ =>
          match rdsOf? l with
          | .error e => .error e
          | .ok a =>
              match rdsOf? r with
              | .error e => .error e
              | .ok b => .ok (a ++ b)
  | .unary .. => .error "unary operator (outside the v0 fragment)"
  | .ternary .. => .error "conditional expression `?:` (outside the v0 fragment)"
  | .concat _ => .error "concatenation (outside the v0 fragment)"
  | .partSel .. => .error "part select (outside the v0 fragment)"
  | .arrayPart .. => .error "array part select (outside the v0 fragment)"
  | .repl .. => .error "replication (outside the v0 fragment)"
  | .reduce .. => .error "reduction (outside the v0 fragment)"
  | _ => .error "expression construct outside the v0 fragment (constant, cast, width conversion or system call)"

def tgtOf? : PLhs → Except String TTgt
  | .ident n => .ok (.whole n)
  | .bitSel n i =>
      match affOf? i with
      | some a => .ok (.bit n a)
      | none => .error s!"write to `{n}[…]` has a non-affine (dynamic) index: the driven window cannot be determined"
  | .arrayElem n is =>
      match is with
      | [i] =>
          match affOf? i with
          | some a => .ok (.arr n a)
          | none => .error s!"write to `{n}[…]` has a non-affine (dynamic) index: the driven window cannot be determined"
      | _ => .error s!"write to a multi-dimensional array `{n}[…][…]` (outside the v0 fragment)"
  | .partSel n .. => .error s!"part-select write to `{n}` (outside the v0 fragment)"
  | .arrayPart n .. => .error s!"array part-select write to `{n}` (outside the v0 fragment)"
  | .concat _ => .error "concatenation target (outside the v0 fragment)"

def siteOf? (pos : Nat) : PProcess → Except String TSite
  | .assign t v =>
      match rdsOf? v with
      | .ok rds => .ok ⟨pos, .whole t, rds, .assign t v⟩
      | .error e => .error e
  | .assignL l v =>
      match tgtOf? l with
      | .error e => .error e
      | .ok tg =>
          match rdsOf? v with
          | .ok rds => .ok ⟨pos, tg, rds, .assignL l v⟩
          | .error e => .error e
  | .alwaysFF .. | .alwaysPlain .. | .alwaysComb .. | .alwaysFFR .. =>
      .error "procedural process (`always`): outside the combinational-assign fragment"
  | .unsupported k _ => .error s!"unsupported process `{k}`"

def sitesOf? (tag : String) : Nat → List PProcess → Except String (List TSite)
  | _, [] => .ok []
  | pos, p :: ps =>
      match siteOf? pos p with
      | .error e => .error s!"site `{tag}#{pos}`: {e}"
      | .ok st =>
          match sitesOf? tag (pos + 1) ps with
          | .error e => .error e
          | .ok sts => .ok (st :: sts)

/-- A generate-for family: block label, loop variable, first value, affine (parameter-only)
upper bound, and the sites of the body in source order. -/
structure TFam where
  label : String
  g : String
  c0 : Int
  bound : Aff
  body : List TSite
deriving Repr, Inhabited

def procsOf? : List GenItem → Option (List PProcess)
  | [] => some []
  | .process p :: rest =>
      match procsOf? rest with
      | some ps => some (p :: ps)
      | none => none
  | _ => none

theorem procsOf?_eq : ∀ {l : List GenItem} {ps : List PProcess}, procsOf? l = some ps →
    l = ps.map GenItem.process
  | [], ps, h => by simp [procsOf?] at h; subst h; rfl
  | .process p :: rest, ps, h => by
      simp only [procsOf?] at h
      rcases hr : procsOf? rest with _ | qs
      · simp [hr] at h
      · simp only [hr, Option.some.injEq] at h
        subst h
        simp [procsOf?_eq hr]
  | .genFor .. :: _, _, h => by simp [procsOf?] at h
  | .genIf .. :: _, _, h => by simp [procsOf?] at h
  | .unsupported .. :: _, _, h => by simp [procsOf?] at h
  | .inst _ :: _, _, h => by simp [procsOf?] at h

def famOf? : GenItem → Except String TFam
  | .genFor label g (.int c0) (.binary .slt (.genvarRef g') bnd) (.unary .inc (.genvarRef g'')) _ body =>
      if g' = g ∧ g'' = g then
        match affOf? bnd with
        | none => .error "generate bound is not affine in the parameters"
        | some b =>
            match procsOf? body with
            | none => .error "generate body holds a nested generate, a conditional generate or an instance"
            | some ps =>
                match sitesOf? (label.getD "genblk") 0 ps with
                | .error e => .error e
                | .ok sites => .ok ⟨label.getD "genblk", g, c0, b, sites⟩
      else .error "generate loop header mentions a second loop variable"
  | .genFor .. => .error "generate-for header outside `for (g = <int>; g < <affine>; g++)`"
  | .genIf .. => .error "conditional generate (outside the v0 fragment)"
  | .inst _ => .error "module instance (outside the v0 fragment)"
  | .process _ => .error "process item in the generate list"
  | .unsupported k _ => .error s!"unsupported generate item `{k}`"

/-! ## Declarations -/

/-- A scalar or 1-D packed declaration with affine bounds. -/
structure DeclT where
  name : String
  isInput : Bool
  isOutput : Bool
  dim : Option (PDim × Aff × Aff)
deriving Repr, Inhabited

def DeclT.width (σ : String → Int) (dt : DeclT) : Nat :=
  match dt.dim with
  | none => 1
  | some (_, m, l) => (m.eval σ - l.eval σ).natAbs + 1

def DeclT.vals (σ : String → Int) (dt : DeclT) : List (Int × Int) :=
  match dt.dim with
  | none => []
  | some (_, m, l) => [(m.eval σ, l.eval σ)]

def DeclT.pdims (dt : DeclT) : List PDim :=
  match dt.dim with
  | none => []
  | some (d, _, _) => [d]

def DeclT.affNames (dt : DeclT) : List String :=
  match dt.dim with
  | none => []
  | some (_, m, l) => m.names ++ l.names

def DeclT.toDecl (σ : String → Int) (dt : DeclT) : Decl :=
  { name := dt.name, width := dt.width σ, isInput := dt.isInput, isOutput := dt.isOutput }

def declOf? (pd : PDecl) : Except String DeclT :=
  match pd.init with
  | some _ => .error s!"declaration `{pd.name}` has an initializer"
  | none =>
      if pd.isSigned || pd.twoState then
        .error s!"declaration `{pd.name}` is signed or 2-state (outside the v0 fragment: the summary's declarations are unsigned 4-state)"
      else
        match pd.type with
        | .packed [] _ => .ok ⟨pd.name, pd.isInput, pd.isOutput, none⟩
        | .packed [d] _ =>
            match affOf? d.msb, affOf? d.lsb with
            | some m, some l => .ok ⟨pd.name, pd.isInput, pd.isOutput, some (d, m, l)⟩
            | _, _ => .error s!"declaration `{pd.name}`: packed bounds are not affine in the parameters"
        | _ => .error s!"declaration `{pd.name}`: only scalar and 1-D packed declarations are in the v0 fragment"

def declsOf? : List PDecl → Except String (List DeclT)
  | [] => .ok []
  | pd :: rest =>
      match declOf? pd with
      | .error e => .error e
      | .ok dt =>
          match declsOf? rest with
          | .error e => .error e
          | .ok ds => .ok (dt :: ds)

/-! ## The summary -/

structure Summary where
  params : List String
  decls : List DeclT
  statics : List TSite
  fam : Option TFam
deriving Repr, Inhabited

def _root_.LeanModels.Sv.PDesign.summary (d : PDesign) : Except String Summary :=
  if !d.localParams.isEmpty then .error "local parameters are outside the v0 fragment"
  else if !d.enums.isEmpty then .error "enums are outside the v0 fragment"
  else if !d.others.isEmpty then .error "out-of-tier module members are present"
  else
    match declsOf? d.decls with
    | .error e => .error e
    | .ok ds =>
        match sitesOf? "plain" 0 d.processes with
        | .error e => .error e
        | .ok sts =>
            match d.generates with
            | [] => .ok ⟨d.params.map (·.name), ds, sts, none⟩
            | [it] =>
                match famOf? it with
                | .error e => .error e
                | .ok f => .ok ⟨d.params.map (·.name), ds, sts, some f⟩
            | _ => .error "more than one generate item (the v0 fragment has at most one `generate for`)"

namespace Summary

variable (s : Summary)

def declNames : List String := s.decls.map (·.name)
def inputNames : List String := s.decls.filterMap fun dt => if dt.isInput then some dt.name else none
def famSites : List TSite := match s.fam with | none => [] | some f => f.body
def sites : List TSite := s.statics ++ s.famSites
def find (n : String) : Option DeclT := s.decls.find? (fun dt => dt.name == n)

/-- Declared width of a signal (`0` when undeclared). -/
def dw (σ : String → Int) (n : String) : Nat := ((s.find n).map (·.width σ)).getD 0

/-- The widths as the `IEnv.widths`/`Design2.declWidth` view of the declaration scope. -/
def DW (σ : String → Int) (n : String) : Option Nat := (s.find n).map (·.width σ)

/-- The most significant label of a zero-based descending 1-D declaration `[m:0]`. -/
def AD (σ : String → Int) (n : String) : Option Int :=
  match s.find n with
  | some ⟨_, _, _, some (_, m, l)⟩ => if l = Aff.const 0 then some (m.eval σ) else none
  | _ => none

end Summary

/-! ## What the summary promises: footprints of the instantiated processes -/

def TTgt.win (σ : String → Int) (dw : String → Nat) : TTgt → Win
  | .whole n => (n, 0, dw n)
  | .bit n a => (n, (a.eval σ).toNat, 1)
  | .arr n a => (n, (a.eval σ).toNat, 1)

def TTgt.lhs (σ : String → Int) : TTgt → Lhs2
  | .whole n => .ident n
  | .bit n a => .slice n (a.eval σ).toNat 1
  | .arr n a => .slice n (a.eval σ).toNat 1

def TRd.rd (σ : String → Int) : TRd → ReadWin
  | .whole n => .whole n
  | .bit n a => .win n (a.eval σ).toNat 1
  | .arr n a => .win n (a.eval σ).toNat 1

/-- The footprint of one process instance. -/
structure SiteInst where
  id : SiteId
  win : Win
  tgt : Lhs2
  rd : List ReadWin

def TSite.inst (σ : String → Int) (dw : String → Nat) (id : SiteId) (st : TSite) : SiteInst :=
  { id := id, win := st.tgt.win σ dw, tgt := st.tgt.lhs σ, rd := st.rds.map (TRd.rd σ) }

def TFam.range (f : TFam) (σ : String → Int) : List Int :=
  intRange f.c0 (f.bound.eval σ - f.c0).toNat

def TFam.insts (f : TFam) (σ : String → Int) (dw : String → Nat) : List SiteInst :=
  (f.range σ).flatMap fun i =>
    f.body.map fun st => st.inst (bindσ f.g i σ) dw (.fam f.label st.pos [i])

def Summary.insts (s : Summary) (σ : String → Int) : List SiteInst :=
  s.statics.map (fun st => st.inst σ (s.dw σ) (.plain st.pos)) ++
    (match s.fam with
     | none => []
     | some f => f.insts σ (s.dw σ))

/-- The closed-form realized list: each promised footprint next to the process the real
instantiation builds for it, in `instantiate2`'s order. -/
def Summary.pairs (s : Summary) (σ : String → Int) (E : IEnv) (elems : List (String × Nat)) :
    List (SiteInst × Process2) :=
  s.statics.map (fun st => (st.inst σ (s.dw σ) (.plain st.pos), instProcess2 E elems st.proc)) ++
    (match s.fam with
     | none => []
     | some f =>
         (f.range σ).flatMap fun i =>
           f.body.map fun st =>
             (st.inst (bindσ f.g i σ) (s.dw σ) (.fam f.label st.pos [i]),
              instProcess2 (E.bindVal f.g i) elems st.proc))

theorem Summary.pairs_map_fst (s : Summary) (σ : String → Int) (E : IEnv)
    (elems : List (String × Nat)) : (s.pairs σ E elems).map Prod.fst = s.insts σ := by
  unfold Summary.pairs Summary.insts
  rw [List.map_append, List.map_map]
  congr 1
  cases s.fam with
  | none => rfl
  | some f =>
    simp only [TFam.insts, List.map_flatMap, List.map_map, Function.comp_def]

/-! ## The declaration stage -/

theorem declOf?_spec {pd : PDecl} {dt : DeclT} (h : declOf? pd = .ok dt) :
    dt.name = pd.name ∧ dt.isInput = pd.isInput ∧ dt.isOutput = pd.isOutput ∧ pd.init = none ∧
    (∃ r, pd.type = .packed dt.pdims r) ∧
    (∀ d m l, dt.dim = some (d, m, l) → affOf? d.msb = some m ∧ affOf? d.lsb = some l) ∧
    pd.isSigned = false ∧ pd.twoState = false := by
  unfold declOf? at h
  cases hi : pd.init with
  | some v => rw [hi] at h; simp at h
  | none =>
    rw [hi] at h
    by_cases hst : (pd.isSigned || pd.twoState) = true
    · rw [if_pos hst] at h; simp at h
    rw [if_neg hst] at h
    have hs : pd.isSigned = false ∧ pd.twoState = false := by simpa using hst
    cases hty : pd.type with
    | packed ds r =>
      rw [hty] at h
      cases ds with
      | nil =>
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨rfl, rfl, rfl, rfl, ⟨r, by simp [DeclT.pdims]⟩, ?_, hs.1, hs.2⟩
        intro d m l hd; simp at hd
      | cons d ds' =>
        cases ds' with
        | nil =>
          rcases hm : affOf? d.msb with _ | m <;> rcases hl : affOf? d.lsb with _ | l <;>
            simp [hm, hl] at h
          subst h
          refine ⟨rfl, rfl, rfl, rfl, ⟨r, by simp [DeclT.pdims]⟩, ?_, hs.1, hs.2⟩
          intro d' m' l' hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          obtain ⟨rfl, rfl, rfl⟩ := hd
          exact ⟨hm, hl⟩
        | cons d2 ds'' => simp at h
    | typeRef n pkg r => rw [hty] at h; simp at h
    | unrecoverable r => rw [hty] at h; simp at h

theorem declsOf?_cons {pd : PDecl} {rest : List PDecl} {sd : List DeclT}
    (h : declsOf? (pd :: rest) = .ok sd) :
    ∃ dt sd', declOf? pd = .ok dt ∧ declsOf? rest = .ok sd' ∧ sd = dt :: sd' := by
  unfold declsOf? at h
  rcases hd : declOf? pd with e | dt
  · simp [hd] at h
  · rcases hr : declsOf? rest with e | sd'
    · simp [hd, hr] at h
    · simp only [hd, hr, Except.ok.injEq] at h
      exact ⟨dt, sd', rfl, rfl, h.symm⟩

/-- `dimsWidth` of at most one dimension, computed. -/
theorem width_decl {env : IEnv} {σ : String → Int} {pd : PDecl} {dt : DeclT}
    (hd : declOf? pd = .ok dt)
    (hag : ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n)) :
    pd.type.width env = .ok (dt.width σ) := by
  obtain ⟨-, -, -, -, ⟨r, hr⟩, hdim, -, -⟩ := declOf?_spec hd
  rw [hr]
  cases hdt : dt.dim with
  | none => simp [DeclT.pdims, hdt, DeclT.width]
  | some p =>
    obtain ⟨d, m, l⟩ := p
    obtain ⟨hm, hl⟩ := hdim d m l hdt
    have hm' : ∀ n ∈ m.names, env.vals.lookup n = some (σ n) :=
      fun n hn => hag n (by simp [DeclT.affNames, hdt, hn])
    have hl' : ∀ n ∈ l.names, env.vals.lookup n = some (σ n) :=
      fun n hn => hag n (by simp [DeclT.affNames, hdt, hn])
    obtain ⟨-, hem⟩ := affOf?_sound _ _ hm hm'
    obtain ⟨-, hel⟩ := affOf?_sound _ _ hl hl'
    simp only [DeclT.pdims, hdt]
    rw [PType.width_packed_single_of r hem hel]
    simp [DeclT.width, hdt]

theorem buildDecls_summary {σ : String → Int} :
    ∀ (ds : List PDecl) (sd : List DeclT), declsOf? ds = .ok sd →
      ∀ (env : IEnv), (∀ dt ∈ sd, ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n)) →
        buildDecls env ds = .ok (sd.map (·.toDecl σ))
  | [], sd, h, env, _ => by
      simp [declsOf?] at h; subst h; rfl
  | pd :: rest, sd, h, env, hag => by
      obtain ⟨dt, sd', hd, hr, rfl⟩ := declsOf?_cons h
      obtain ⟨hn, hi, ho, hinit, -, -, hsg, hts⟩ := declOf?_spec hd
      have hw := width_decl (env := env) (σ := σ) hd (fun n hn => hag dt (by simp) n hn)
      have hrest := buildDecls_summary rest sd' hr
        { env with widths := (pd.name, dt.width σ) :: env.widths }
        (fun dt' hdt' n hn => hag dt' (by simp [hdt']) n hn)
      have hdecl : instDecl env pd = .ok (dt.toDecl σ) := by
        simp [instDecl, hw, hinit, DeclT.toDecl, hn, hi, ho, hsg, hts]
      simp only [buildDecls, hdecl, Res.ok_bind]
      have : ({ name := pd.name, width := dt.width σ, isInput := pd.isInput, isOutput := pd.isOutput } : Decl)
          = dt.toDecl σ := by simp [DeclT.toDecl, hn, hi, ho]
      simp only [DeclT.toDecl] at hrest ⊢
      rw [hrest]
      simp [Res.ok_bind, hn]

theorem buildElems_summary {σ : String → Int} :
    ∀ (ds : List PDecl) (sd : List DeclT), declsOf? ds = .ok sd →
      ∀ (env : IEnv), (∀ dt ∈ sd, ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n)) →
        buildElems env ds = .ok (sd.map fun dt => (dt.name, 1))
  | [], sd, h, env, _ => by
      simp [declsOf?] at h; subst h; rfl
  | pd :: rest, sd, h, env, hag => by
      obtain ⟨dt, sd', hd, hr, rfl⟩ := declsOf?_cons h
      obtain ⟨hn, -, -, -, ⟨r, hr'⟩, -, -, -⟩ := declOf?_spec hd
      have hw := width_decl (env := env) (σ := σ) hd (fun n hn => hag dt (by simp) n hn)
      have hrest := buildElems_summary rest sd' hr
        { env with widths := (pd.name, dt.width σ) :: env.widths }
        (fun dt' hdt' n hn => hag dt' (by simp [hdt']) n hn)
      have hew : pd.type.elemWidth env = .ok 1 := by
        rw [hr']
        cases hdt : dt.dim <;> simp [DeclT.pdims, hdt]
      simp only [buildElems, hw, hew]
      rw [hrest]
      simp [Res.ok_bind, hn]

theorem dimTableStep_vals (env : IEnv) (pd : PDecl) : (dimTableStep env pd).vals = env.vals := by
  unfold dimTableStep
  split <;> rfl

theorem dimTable_summary {σ : String → Int} :
    ∀ (ds : List PDecl) (sd : List DeclT), declsOf? ds = .ok sd →
      ∀ (env : IEnv), (∀ dt ∈ sd, ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n)) →
        ∀ n, (dimTable env ds).lookup n = (sd.find? (fun dt => dt.name == n)).map (DeclT.vals σ)
  | [], sd, h, env, _, n => by
      simp [declsOf?] at h; subst h; simp [dimTable]
  | pd :: rest, sd, h, env, hag, n => by
      obtain ⟨dt, sd', hd, hr, rfl⟩ := declsOf?_cons h
      obtain ⟨hn, -, -, -, ⟨r, hr'⟩, hdim, -, -⟩ := declOf?_spec hd
      have hrest := dimTable_summary rest sd' hr (dimTableStep env pd)
        (fun dt' hdt' n' hn' => by
          rw [dimTableStep_vals]; exact hag dt' (by simp [hdt']) n' hn') n
      have hev : evalDims env dt.pdims = .ok (dt.vals σ) := by
        cases hdt : dt.dim with
        | none => simp [DeclT.pdims, DeclT.vals, hdt]
        | some p =>
          obtain ⟨d, m, l⟩ := p
          obtain ⟨hm, hl⟩ := hdim d m l hdt
          have hm' : ∀ n ∈ m.names, env.vals.lookup n = some (σ n) :=
            fun n hn => hag dt (by simp) n (by simp [DeclT.affNames, hdt, hn])
          have hl' : ∀ n ∈ l.names, env.vals.lookup n = some (σ n) :=
            fun n hn => hag dt (by simp) n (by simp [DeclT.affNames, hdt, hn])
          obtain ⟨-, hem⟩ := affOf?_sound _ _ hm hm'
          obtain ⟨-, hel⟩ := affOf?_sound _ _ hl hl'
          simp only [DeclT.pdims, DeclT.vals, hdt]
          exact evalDims_cons_of hem hel evalDims_nil
      simp only [dimTable, hr', hev, List.lookup, List.find?_cons]
      by_cases hnm : n = pd.name
      · subst hnm
        have h1 : (pd.name == pd.name) = true := beq_self_eq_true _
        have h2 : (dt.name == pd.name) = true := by simp [hn]
        simp [h2]
      · have h1 : (n == pd.name) = false := beq_eq_false_iff_ne.2 hnm
        have h2 : (dt.name == n) = false := by rw [hn]; exact beq_eq_false_iff_ne.2 (Ne.symm hnm)
        simp [h1, h2, hrest]

end CombView
end LeanModels.Sv
