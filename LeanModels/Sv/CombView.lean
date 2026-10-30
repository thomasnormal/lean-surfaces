import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Comb2Base
import LeanModels.Sv.CombViewArith

/-!
# `sv_structure`, stage 1: the family summary of a `PDesign` and its soundness

Step 4 of `docs/sv-comb-design.md` §7 (design principle 6): a TRANSIENT view derived from
`PDesign`, with a soundness theorem against `PDesign.instantiate2`. Nothing here is a new
design AST or a new evaluator: the summary is read off the template (`PDesign.summary`,
structural recursion, evaluated by the kernel/unifier) and everything it claims is proved
against the real instantiation (`instProcess2`, `expandList2`, `buildDecls`, `dimTable`), using
the `Gen2.lean` handles.

## The fragment (v1)

A flat top whose processes are continuous assigns (`assign x = e`, `assign x[idx] = e`,
`assign x[i][j] = e`, `assign x[i] = e` over a 2-D packed array (a whole row), `assign x[hi:lo] = e`),
plus ANY NUMBER of `generate for` loops `for (g = c0; g < bound; g++)` whose bodies hold such assigns
and, one level down, further `generate for` loops of such assigns (two levels deep, mixed bodies).

* declarations: scalars, 1-D and 2-D packed arrays with affine bounds;
* localparams (`localparam integer L = e`, `e` an integer constant expression of the parameters and the
  earlier localparams: `+ - *` by a literal, `/` `%` by a positive literal): one more NAMED CONSTANT,
  wherever a parameter may stand (`Summary.lps`, `Summary.val`; see "Local parameters" below);
* accesses (`Acc`): the whole signal, a bit `x[i]`, an element of a 1-D array, a row or an element
  of a 2-D array (`x[i]`, `x[i][j]`), a part `x[hi:lo]` or a part of a row `x[i][hi:lo]`; every
  index and bound AFFINE in the parameters and the enclosing genvars (`i`, `i + 1`, `N`, `2*N - 1`);
* expressions: a tree of `&`/`|`/`^` over accesses and literals, concatenations of accesses and
  literals, and (as the whole right-hand side) an unbased unsized fill `'0`.

Everything else is refused with a specific message (`PDesign.summary` returns `.error msg`).

## What is claimed

* `PDesign.summary d = .ok s` computes the sites (`TSite`: target access and read accesses as
  affine data), the generate tree (`TFam`: loops and the sites in their bodies) and the
  declaration geometry.
* `Summary.enum` / `Summary.insts` / `Summary.pairs` is the closed-form list (a `flatMap` over each
  loop's index range, never an enumeration of `N` cells) of the footprints the summary promises
  next to the processes `instProcess2` really builds.
* `site_desc` (per-site soundness, `CombViewThm.lean`) and `Summary.sound` (`CombViewSound.lean`).
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

def scaleTerms (k : Int) : List (String × Int) → List (String × Int)
  | [] => []
  | (n, m) :: ts => (n, k * m) :: scaleTerms k ts

/-- Scaling by a constant. -/
def scale (k : Int) (a : Aff) : Aff := { terms := scaleTerms k a.terms, c := k * a.c }

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

theorem evalTerms_scaleTerms (σ : String → Int) (k : Int) (a : List (String × Int)) :
    evalTerms σ (scaleTerms k a) = k * evalTerms σ a := by
  induction a with
  | nil => simp [scaleTerms, evalTerms]
  | cons p ts ih =>
    obtain ⟨n, m⟩ := p
    simp [scaleTerms, evalTerms, ih, Int.mul_add, Int.mul_assoc]

theorem names_scaleTerms (k : Int) (a : List (String × Int)) :
    (scaleTerms k a).map Prod.fst = a.map Prod.fst := by
  induction a with
  | nil => simp [scaleTerms]
  | cons p ts ih => obtain ⟨n, m⟩ := p; simp [scaleTerms, ih]

theorem eval_add (σ : String → Int) (a b : Aff) : (a.add b).eval σ = a.eval σ + b.eval σ := by
  simp only [eval, add, evalTerms_append]
  omega

theorem eval_neg (σ : String → Int) (a : Aff) : a.neg.eval σ = - a.eval σ := by
  simp only [eval, neg, evalTerms_negTerms]
  omega

theorem eval_sub (σ : String → Int) (a b : Aff) : (a.sub b).eval σ = a.eval σ - b.eval σ := by
  rw [sub, eval_add, eval_neg]
  omega

theorem eval_scale (σ : String → Int) (k : Int) (a : Aff) : (a.scale k).eval σ = k * a.eval σ := by
  simp only [eval, scale, evalTerms_scaleTerms]
  rw [Int.mul_add]

theorem eval_const (σ : String → Int) (c : Int) : (const c).eval σ = c := by
  simp [eval, const, evalTerms]

theorem eval_var (σ : String → Int) (n : String) : (var n).eval σ = σ n := by
  simp [eval, var, evalTerms]

theorem names_add (a b : Aff) : (a.add b).names = a.names ++ b.names := by
  simp [names, add]

theorem names_sub (a b : Aff) : (a.sub b).names = a.names ++ b.names := by
  simp [names, sub, add, neg, names_negTerms]

theorem names_scale (k : Int) (a : Aff) : (a.scale k).names = a.names := by
  simp [names, scale, names_scaleTerms]

theorem eval_of_terms_nil (σ : String → Int) (a : Aff) (h : a.terms = []) : a.eval σ = a.c := by
  simp [eval, h, evalTerms]

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

def affMul (a b : Aff) : Option Aff :=
  if a.terms.isEmpty then some (b.scale a.c)
  else if b.terms.isEmpty then some (a.scale b.c)
  else none

def affBin : SymBinOp → Aff → Aff → Option Aff
  | .m0 .add, a, b => some (a.add b)
  | .m0 .sub, a, b => some (a.sub b)
  | .mul, a, b => affMul a b
  | .m0 .mul, a, b => affMul a b
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

theorem affMul_eval {a b c : Aff} (σ : String → Int) (h : affMul a b = some c) :
    c.eval σ = a.eval σ * b.eval σ := by
  unfold affMul at h
  by_cases ha : a.terms.isEmpty = true
  · simp only [ha, if_true, Option.some.injEq] at h
    subst h
    have ha' : a.terms = [] := by simpa using ha
    rw [Aff.eval_scale, Aff.eval_of_terms_nil σ a ha']
  · have ha' : a.terms.isEmpty = false := by simpa using ha
    simp only [ha', Bool.false_eq_true, if_false] at h
    by_cases hb : b.terms.isEmpty = true
    · simp only [hb, if_true, Option.some.injEq] at h
      subst h
      have hb' : b.terms = [] := by simpa using hb
      rw [Aff.eval_scale, Aff.eval_of_terms_nil σ b hb', Int.mul_comm]
    · have hb' : b.terms.isEmpty = false := by simpa using hb
      simp [hb'] at h

theorem affMul_names {a b c : Aff} (h : affMul a b = some c) :
    (a.terms = [] ∧ c.names = b.names) ∨ (b.terms = [] ∧ c.names = a.names) := by
  unfold affMul at h
  by_cases ha : a.terms.isEmpty = true
  · simp only [ha, if_true, Option.some.injEq] at h
    subst h
    have ha' : a.terms = [] := by simpa using ha
    exact Or.inl ⟨ha', by simp [Aff.names_scale]⟩
  · have ha' : a.terms.isEmpty = false := by simpa using ha
    simp only [ha', Bool.false_eq_true, if_false] at h
    by_cases hb : b.terms.isEmpty = true
    · simp only [hb, if_true, Option.some.injEq] at h
      subst h
      have hb' : b.terms = [] := by simpa using hb
      exact Or.inr ⟨hb', by simp [Aff.names_scale]⟩
    · have hb' : b.terms.isEmpty = false := by simpa using hb
      simp [hb'] at h

theorem affBin_cases {op : SymBinOp} {a b c : Aff} (h : affBin op a b = some c) :
    (op = .m0 .add ∧ c = a.add b) ∨ (op = .m0 .sub ∧ c = a.sub b) ∨
    ((op = .mul ∨ op = .m0 .mul) ∧ affMul a b = some c) := by
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
      rcases affBin_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hop, hm⟩
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
      · have hev := affMul_eval σ hm
        have hn := affMul_names hm
        have hb1 : ∀ n ∈ a1.names, E.vals.lookup n = some (σ n) := by
          intro n hn1
          rcases hn with ⟨h0, -⟩ | ⟨-, hc⟩
          · simp [Aff.names, h0] at hn1
          · exact hb n (by rw [hc]; exact hn1)
        have hb2 : ∀ n ∈ a2.names, E.vals.lookup n = some (σ n) := by
          intro n hn2
          rcases hn with ⟨-, hc⟩ | ⟨h0, -⟩
          · exact hb n (by rw [hc]; exact hn2)
          · simp [Aff.names, h0] at hn2
        obtain ⟨hi1, he1⟩ := affOf?_sound l a1 h1 hb1
        obtain ⟨hi2, he2⟩ := affOf?_sound r a2 h2 hb2
        rcases hop with rfl | rfl
        · exact ⟨isInt_binary_of (by simp) hi1 hi2, by rw [evalInt_mul_of hi1 hi2 he1 he2, hev]⟩
        · exact ⟨isInt_binary_of (by simp) hi1 hi2, by rw [evalInt_m0_mul_of hi1 hi2 he1 he2, hev]⟩
  | .paramRef _ (some _), a, h, _ => by simp [affOf?] at h
  | .lit _, a, h, _ | .ident _, a, h, _ | .enumRef _ _ _, a, h, _ | .fill _, a, h, _
  | .unary _ _, a, h, _ | .ternary _ _ _, a, h, _ | .concat _, a, h, _ | .resize _ _, a, h, _
  | .signedResize _ _, a, h, _ | .squash2 _ _, a, h, _ | .sysCall _ _, a, h, _
  | .bitSel _ _, a, h, _ | .partSel _ _ _, a, h, _ | .repl _ _, a, h, _ | .reduce _ _, a, h, _
  | .cast _ _, a, h, _ | .arrayElem _ _, a, h, _ | .arrayPart _ _ _ _ _, a, h, _
  | .unsupported _ _, a, h, _ => by simp [affOf?] at h

/-! ## Template sites -/

/-- The identity of a rank site (design principle 13): a plain process by its position among the
module-level processes; a generate-family member by the label of its innermost block, the position
of the assign inside that block, and the values of the enclosing loop indices (outermost first). -/
inductive SiteId where
  | plain (pos : Nat)
  | fam (label : String) (pos : Nat) (idx : List Int)
deriving Repr, DecidableEq, Inhabited

/-- One access to a declared signal: the shapes the summary can compute a window for.

* `whole n`             the whole signal
* `bit n i`             `n[i]`, `n` a scalar or 1-D vector (bit select)
* `cell1 n i`           `n[i]`, `n` a 1-D packed array
* `row n w r`           `n[r]`, `n` a 2-D packed array whose rows are `w` bits wide
* `cell2 n w r c`       `n[r][c]`, rows `w` bits wide
* `part1 n hi lo`       `n[hi:lo]`, `n` 1-D
* `part2 n w r hi lo`   `n[r][hi:lo]`, rows `w` bits wide

The row width `w` is the second dimension's extent, recorded here (affine) and checked against the
declaration by `Summary.accOk`. -/
inductive Acc where
  | whole (n : String)
  | bit (n : String) (idx : Aff)
  | cell1 (n : String) (idx : Aff)
  | row (n : String) (w : Aff) (r : Aff)
  | cell2 (n : String) (w : Aff) (r c : Aff)
  | part1 (n : String) (hi lo : Aff)
  | part2 (n : String) (w : Aff) (r hi lo : Aff)
deriving Repr, DecidableEq, Inhabited

def Acc.name : Acc → String
  | .whole n => n
  | .bit n _ => n
  | .cell1 n _ => n
  | .row n _ _ => n
  | .cell2 n _ _ _ => n
  | .part1 n _ _ => n
  | .part2 n _ _ _ _ => n

/-- The index expressions (not the row width, which the declaration determines). -/
def Acc.affs : Acc → List Aff
  | .whole _ => []
  | .bit _ a => [a]
  | .cell1 _ a => [a]
  | .row _ _ r => [r]
  | .cell2 _ _ r c => [r, c]
  | .part1 _ hi lo => [hi, lo]
  | .part2 _ _ r hi lo => [r, hi, lo]

/-- Bit offset of an access (a row-major offset for the 2-D forms). -/
def Acc.lo (σ : String → Int) : Acc → Nat
  | .whole _ => 0
  | .bit _ a => (a.eval σ).toNat
  | .cell1 _ a => (a.eval σ).toNat
  | .row _ w r => rmN (w.eval σ) (r.eval σ) 0
  | .cell2 _ w r c => rmN (w.eval σ) (r.eval σ) (c.eval σ)
  | .part1 _ _ lo => (lo.eval σ).toNat
  | .part2 _ w r _ lo => rmN (w.eval σ) (r.eval σ) (lo.eval σ)

/-- Bit width of an access (`0` for the whole signal: its width is the declared one). -/
def Acc.wid (σ : String → Int) : Acc → Nat
  | .whole _ => 0
  | .bit _ _ => 1
  | .cell1 _ _ => 1
  | .row _ w _ => (w.eval σ).toNat
  | .cell2 _ _ _ _ => 1
  | .part1 _ hi lo => (hi.eval σ - lo.eval σ + 1).toNat
  | .part2 _ _ _ hi lo => (hi.eval σ - lo.eval σ + 1).toNat

/-- The write window of a target access. -/
def Acc.win (σ : String → Int) (dw : String → Nat) : Acc → Win
  | .whole n => (n, 0, dw n)
  | .bit n a => (n, Acc.lo σ (.bit n a), 1)
  | .cell1 n a => (n, Acc.lo σ (.cell1 n a), 1)
  | .row n w r => (n, Acc.lo σ (.row n w r), Acc.wid σ (.row n w r))
  | .cell2 n w r c => (n, Acc.lo σ (.cell2 n w r c), 1)
  | .part1 n hi lo => (n, Acc.lo σ (.part1 n hi lo), Acc.wid σ (.part1 n hi lo))
  | .part2 n w r hi lo => (n, Acc.lo σ (.part2 n w r hi lo), Acc.wid σ (.part2 n w r hi lo))

/-- The lowered target. -/
def Acc.lhs (σ : String → Int) : Acc → Lhs2
  | .whole n => .ident n
  | .bit n a => .slice n (Acc.lo σ (.bit n a)) 1
  | .cell1 n a => .slice n (Acc.lo σ (.cell1 n a)) 1
  | .row n w r => .slice n (Acc.lo σ (.row n w r)) (Acc.wid σ (.row n w r))
  | .cell2 n w r c => .slice n (Acc.lo σ (.cell2 n w r c)) 1
  | .part1 n hi lo => .slice n (Acc.lo σ (.part1 n hi lo)) (Acc.wid σ (.part1 n hi lo))
  | .part2 n w r hi lo =>
      .slice n (Acc.lo σ (.part2 n w r hi lo)) (Acc.wid σ (.part2 n w r hi lo))

/-- The read it promises. -/
def Acc.rd (σ : String → Int) : Acc → ReadWin
  | .whole n => .whole n
  | .bit n a => .win n (Acc.lo σ (.bit n a)) 1
  | .cell1 n a => .win n (Acc.lo σ (.cell1 n a)) 1
  | .row n w r => .win n (Acc.lo σ (.row n w r)) (Acc.wid σ (.row n w r))
  | .cell2 n w r c => .win n (Acc.lo σ (.cell2 n w r c)) 1
  | .part1 n hi lo => .win n (Acc.lo σ (.part1 n hi lo)) (Acc.wid σ (.part1 n hi lo))
  | .part2 n w r hi lo => .win n (Acc.lo σ (.part2 n w r hi lo)) (Acc.wid σ (.part2 n w r hi lo))

/-- A template process with its footprint: the write, the reads, and the process itself (the
equation schema kept for the later stages). -/
structure TSite where
  pos : Nat
  tgt : Acc
  rds : List Acc
  proc : PProcess
deriving Repr, Inhabited

def TSite.names (st : TSite) : List String := st.tgt.name :: st.rds.map Acc.name

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

/-! ## Declarations -/

/-- A scalar, 1-D or 2-D packed declaration with affine bounds. -/
structure DeclT where
  name : String
  isInput : Bool
  isOutput : Bool
  dims : List (PDim × Aff × Aff)
deriving Repr, Inhabited

def dimsW (σ : String → Int) : List (PDim × Aff × Aff) → Nat
  | [] => 1
  | (_, m, l) :: rest => ((m.eval σ - l.eval σ).natAbs + 1) * dimsW σ rest

def DeclT.width (σ : String → Int) (dt : DeclT) : Nat := dimsW σ dt.dims

def DeclT.vals (σ : String → Int) (dt : DeclT) : List (Int × Int) :=
  dt.dims.map fun p => (p.2.1.eval σ, p.2.2.eval σ)

def DeclT.pdims (dt : DeclT) : List PDim := dt.dims.map (·.1)

/-- The element width `buildElems` records: the width of the second dimension of a 2-D
declaration, `1` otherwise. -/
def DeclT.elemW (σ : String → Int) (dt : DeclT) : Nat :=
  match dt.dims with
  | [_, p] => 1 * ((p.2.1.eval σ - p.2.2.eval σ).natAbs + 1)
  | _ => 1

def DeclT.affNames (dt : DeclT) : List String :=
  dt.dims.flatMap fun p => p.2.1.names ++ p.2.2.names

def DeclT.toDecl (σ : String → Int) (dt : DeclT) : Decl :=
  { name := dt.name, width := dt.width σ, isInput := dt.isInput, isOutput := dt.isOutput }

def dimOf? (name : String) (d : PDim) : Except String (PDim × Aff × Aff) :=
  match affOf? d.msb, affOf? d.lsb with
  | some m, some l => .ok (d, m, l)
  | _, _ => .error s!"declaration `{name}`: packed bounds are not affine in the parameters"

def declOf? (pd : PDecl) : Except String DeclT :=
  match pd.init with
  | some _ => .error s!"declaration `{pd.name}` has an initializer"
  | none =>
      if pd.isSigned || pd.twoState then
        .error s!"declaration `{pd.name}` is signed or 2-state (outside the v1 fragment: the summary's declarations are unsigned 4-state)"
      else
        match pd.type with
        | .packed [] _ => .ok ⟨pd.name, pd.isInput, pd.isOutput, []⟩
        | .packed [d] _ =>
            match dimOf? pd.name d with
            | .ok p => .ok ⟨pd.name, pd.isInput, pd.isOutput, [p]⟩
            | .error e => .error e
        | .packed [d1, d2] _ =>
            match dimOf? pd.name d1 with
            | .error e => .error e
            | .ok p1 =>
                match dimOf? pd.name d2 with
                | .error e => .error e
                | .ok p2 => .ok ⟨pd.name, pd.isInput, pd.isOutput, [p1, p2]⟩
        | _ => .error s!"declaration `{pd.name}`: only scalar, 1-D and 2-D packed declarations are in the v1 fragment"

def declsOf? : List PDecl → Except String (List DeclT)
  | [] => .ok []
  | pd :: rest =>
      match declOf? pd with
      | .error e => .error e
      | .ok dt =>
          match declsOf? rest with
          | .error e => .error e
          | .ok ds => .ok (dt :: ds)

def findDecl (ds : List DeclT) (n : String) : Option DeclT := ds.find? (fun dt => dt.name == n)

/-- The (msb, lsb) bounds of a declaration. -/
def dimsOf (ds : List DeclT) (n : String) : Option (List (Aff × Aff)) :=
  (findDecl ds n).map fun dt => dt.dims.map fun p => (p.2.1, p.2.2)

/-! ## Recognizing accesses and expressions -/

def elemAcc? (ds : List DeclT) (n : String) (is : List PExpr) : Except String Acc :=
  match dimsOf ds n with
  | none => .error s!"`{n}` is not declared"
  | some dims =>
      match dims, is with
      | [(_, l)], [i] =>
          if l = Aff.const 0 then
            match affOf? i with
            | some a => .ok (.cell1 n a)
            | none => .error s!"index of `{n}[…]` is not affine (dynamic or nonlinear)"
          else .error s!"`{n}`: element selects need a zero-based descending dimension `[hi:0]`"
      | [(_, l1), (m2, l2)], [i] =>
          if l1 = Aff.const 0 ∧ l2 = Aff.const 0 then
            match affOf? i with
            | some a => .ok (.row n (m2.add (Aff.const 1)) a)
            | none => .error s!"index of `{n}[…]` is not affine (dynamic or nonlinear)"
          else .error s!"`{n}`: element selects need zero-based descending dimensions `[hi:0][hi:0]`"
      | [(_, l1), (m2, l2)], [i, j] =>
          if l1 = Aff.const 0 ∧ l2 = Aff.const 0 then
            match affOf? i, affOf? j with
            | some a, some b => .ok (.cell2 n (m2.add (Aff.const 1)) a b)
            | _, _ => .error s!"an index of `{n}[…][…]` is not affine (dynamic or nonlinear)"
          else .error s!"`{n}`: element selects need zero-based descending dimensions `[hi:0][hi:0]`"
      | _, _ => .error s!"select path on `{n}` does not match its declared packed dimensions (outside the v1 fragment)"

def partAcc? (ds : List DeclT) (n : String) (is : List PExpr) (mode : PartMode) (hi lo : PExpr) :
    Except String Acc :=
  match mode with
  | .up => .error s!"indexed part select `{n}[…+:…]` (outside the v1 fragment)"
  | .down => .error s!"indexed part select `{n}[…-:…]` (outside the v1 fragment)"
  | .range =>
      match dimsOf ds n with
      | none => .error s!"`{n}` is not declared"
      | some dims =>
          match dims, is with
          | [(_, l)], [] =>
              if l = Aff.const 0 then
                match affOf? hi, affOf? lo with
                | some h, some l' => .ok (.part1 n h l')
                | _, _ => .error s!"a bound of `{n}[hi:lo]` is not affine (dynamic or nonlinear)"
              else .error s!"`{n}`: part selects need a zero-based descending dimension `[hi:0]`"
          | [(_, l1), (m2, l2)], [i] =>
              if l1 = Aff.const 0 ∧ l2 = Aff.const 0 then
                match affOf? i, affOf? hi, affOf? lo with
                | some r, some h, some l' => .ok (.part2 n (m2.add (Aff.const 1)) r h l')
                | _, _, _ => .error s!"an index or bound of `{n}[…][hi:lo]` is not affine (dynamic or nonlinear)"
              else .error s!"`{n}`: part selects need zero-based descending dimensions `[hi:0][hi:0]`"
          | _, _ => .error s!"part select on `{n}` does not match its declared packed dimensions (outside the v1 fragment)"

/-- A read of one access. -/
def leafRd? (ds : List DeclT) : PExpr → Except String Acc
  | .ident n => .ok (.whole n)
  | .bitSel b i =>
      match b with
      | .ident n =>
          match affOf? i with
          | some a => .ok (.bit n a)
          | none => .error s!"read `{n}[…]` has a non-affine (dynamic or nonlinear) index"
      | _ => .error "bit select of a non-identifier base"
  | .arrayElem n is => elemAcc? ds n is
  | .arrayPart n is mode hi lo => partAcc? ds n is mode hi lo
  | .unary .. => .error "unary operator (outside the v1 fragment)"
  | .ternary .. => .error "conditional expression `?:` (outside the v1 fragment)"
  | .partSel .. => .error "legacy part select (outside the v1 fragment)"
  | .repl .. => .error "replication (outside the v1 fragment)"
  | .reduce .. => .error "reduction (outside the v1 fragment)"
  | .fill _ => .error "unbased unsized literal `'0`/`'1` inside an expression (outside the v1 fragment; allowed as a whole right-hand side)"
  | _ => .error "expression construct outside the v1 fragment (constant, cast, width conversion or system call)"

/-- One access, as a read list. -/
def rdsLeaf? (ds : List DeclT) (e : PExpr) : Except String (List Acc) :=
  match leafRd? ds e with
  | .ok a => .ok [a]
  | .error m => .error m

/-- A concatenation part: a literal or one access. -/
def partRd? (ds : List DeclT) (e : PExpr) : Except String (List Acc) :=
  match e with
  | .lit _ => .ok []
  | _ => rdsLeaf? ds e

def partsRd? (ds : List DeclT) : List PExpr → Except String (List Acc)
  | [] => .ok []
  | p :: ps =>
      match partRd? ds p with
      | .error e => .error e
      | .ok a =>
          match partsRd? ds ps with
          | .error e => .error e
          | .ok b => .ok (a ++ b)

/-- The reads of an expression of the fragment, or the reason it is outside it. -/
def rdsOf? (ds : List DeclT) : PExpr → Except String (List Acc)
  | .lit _ => .ok []
  | .binary op l r =>
      match gateOf op with
      | none => .error s!"operator `{op.sym}` is not a bitwise gate (`&`, `|`, `^`)"
      | some _ =>
          match rdsOf? ds l with
          | .error e => .error e
          | .ok a =>
              match rdsOf? ds r with
              | .error e => .error e
              | .ok b => .ok (a ++ b)
  | .concat ps => partsRd? ds ps
  | e => rdsLeaf? ds e

/-- The reads of a right-hand side: an unbased unsized fill (`'0`) alone, or an expression. -/
def rhsRds? (ds : List DeclT) (v : PExpr) : Except String (List Acc) :=
  match v with
  | .fill _ => .ok []
  | _ => rdsOf? ds v

def tgtOf? (ds : List DeclT) : PLhs → Except String Acc
  | .ident n => .ok (.whole n)
  | .bitSel n i =>
      match affOf? i with
      | some a => .ok (.bit n a)
      | none => .error s!"write to `{n}[…]` has a non-affine (dynamic) index: the driven window cannot be determined"
  | .arrayElem n is => elemAcc? ds n is
  | .arrayPart n is mode hi lo => partAcc? ds n is mode hi lo
  | .partSel n .. => .error s!"legacy part-select write to `{n}` (outside the v1 fragment)"
  | .concat _ => .error "concatenation target (outside the v1 fragment)"

def siteOf? (ds : List DeclT) (pos : Nat) : PProcess → Except String TSite
  | .assign t v =>
      match rhsRds? ds v with
      | .ok rds => .ok ⟨pos, .whole t, rds, .assign t v⟩
      | .error e => .error e
  | .assignL l v =>
      match tgtOf? ds l with
      | .error e => .error e
      | .ok tg =>
          match rhsRds? ds v with
          | .ok rds => .ok ⟨pos, tg, rds, .assignL l v⟩
          | .error e => .error e
  | .alwaysFF .. | .alwaysPlain .. | .alwaysComb .. | .alwaysFFR .. =>
      .error "procedural process (`always`): outside the combinational-assign fragment"
  | .unsupported k _ => .error s!"unsupported process `{k}`"

def sitesOf? (ds : List DeclT) (tag : String) : Nat → List PProcess → Except String (List TSite)
  | _, [] => .ok []
  | pos, p :: ps =>
      match siteOf? ds pos p with
      | .error e => .error s!"site `{tag}#{pos}`: {e}"
      | .ok st =>
          match sitesOf? ds tag (pos + 1) ps with
          | .error e => .error e
          | .ok sts => .ok (st :: sts)

/-! ## Generate loops -/

/-- A generate-loop header `for (g = c0; g < bound; g++)` with its block label. -/
structure Hdr where
  lbl : Option String
  g : String
  c0 : Int
  bound : Aff
  bndE : PExpr
deriving Repr, Inhabited

def Hdr.name (h : Hdr) : String := h.lbl.getD "genblk"

/-- The loop index ranges over `[c0, bound)`. -/
def Hdr.Rng (h : Hdr) (σ : String → Int) (i : Int) : Prop := h.c0 ≤ i ∧ i < h.bound.eval σ

def Hdr.range (h : Hdr) (σ : String → Int) : List Int :=
  intRange h.c0 (h.bound.eval σ - h.c0).toNat

theorem Hdr.mem_range {h : Hdr} {σ : String → Int} {i : Int} : i ∈ h.range σ ↔ h.Rng σ i := by
  simp only [Hdr.range, Hdr.Rng, mem_intRange]
  omega

/-- The header's envelope form. -/
def Hdr.gen (h : Hdr) (rc : Option Nat) (body : List GenItem) : GenItem :=
  .genFor h.lbl h.g (.int h.c0) (.binary .slt (.genvarRef h.g) h.bndE)
    (.unary .inc (.genvarRef h.g)) rc body

/-- The header's recognized bound is the envelope's. -/
def Hdr.Wf (h : Hdr) : Prop := affOf? h.bndE = some h.bound

/-- An inner loop: sites only. -/
structure TInner where
  hdr : Hdr
  rc : Option Nat
  body : List TSite
deriving Repr, Inhabited

/-- An item of an outer loop's body. -/
inductive TItem where
  | site (st : TSite)
  | loop (l : TInner)
deriving Repr, Inhabited

/-- A top-level generate loop. -/
structure TFam where
  hdr : Hdr
  rc : Option Nat
  body : List TItem
deriving Repr, Inhabited

def TItem.toGen : TItem → GenItem
  | .site st => .process st.proc
  | .loop l => l.hdr.gen l.rc (l.body.map fun st => GenItem.process st.proc)

def TFam.toGen (f : TFam) : GenItem := f.hdr.gen f.rc (f.body.map TItem.toGen)

def TItem.Wf : TItem → Prop
  | .site _ => True
  | .loop l => l.hdr.Wf

def TFam.Wf (f : TFam) : Prop := f.hdr.Wf ∧ ∀ it ∈ f.body, it.Wf

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

def hdrOf? (label : Option String) (g : String) (initE bound step : PExpr) : Except String Hdr :=
  match initE, bound, step with
  | .int c0, .binary .slt (.genvarRef g') bnd, .unary .inc (.genvarRef g'') =>
      if g' = g ∧ g'' = g then
        match affOf? bnd with
        | none => .error "generate bound is not affine in the parameters"
        | some b => .ok ⟨label, g, c0, b, bnd⟩
      else .error "generate loop header mentions a second loop variable"
  | _, _, _ => .error "generate-for header outside `for (g = <int>; g < <affine>; g++)`"

theorem hdrOf?_spec {label : Option String} {g : String} {initE bound step : PExpr} {h : Hdr}
    (hh : hdrOf? label g initE bound step = .ok h) :
    h.lbl = label ∧ h.g = g ∧ h.Wf ∧
      initE = .int h.c0 ∧ bound = .binary .slt (.genvarRef h.g) h.bndE ∧
      step = .unary .inc (.genvarRef h.g) := by
  unfold hdrOf? at hh
  split at hh
  · rename_i c0 g' bnd g''
    by_cases hgg : g' = g ∧ g'' = g
    · obtain ⟨h1, h2⟩ := hgg
      subst h1 h2
      simp only [and_self, if_true] at hh
      rcases hb : affOf? bnd with _ | b
      · simp [hb] at hh
      · simp only [hb, Except.ok.injEq] at hh
        subst hh
        exact ⟨rfl, rfl, hb, rfl, rfl, rfl⟩
    · simp [hgg] at hh
  · simp at hh

/-- An item of an outer loop's body at position `pos`. -/
def itemOf? (ds : List DeclT) (tag : String) (pos : Nat) : GenItem → Except String TItem
  | .process p =>
      match siteOf? ds pos p with
      | .error e => .error s!"site `{tag}#{pos}`: {e}"
      | .ok st => .ok (.site st)
  | .genFor label g initE bound step rc body =>
      match hdrOf? label g initE bound step with
      | .error e => .error e
      | .ok h =>
          match procsOf? body with
          | none => .error "an inner generate loop holds a nested generate, a conditional generate or an instance (the v1 fragment nests generate loops two deep)"
          | some ps =>
              match sitesOf? ds h.name 0 ps with
              | .error e => .error e
              | .ok sts => .ok (.loop ⟨h, rc, sts⟩)
  | .genIf .. => .error "conditional generate inside a generate loop (outside the v1 fragment)"
  | .inst _ => .error "module instance inside a generate loop (outside the v1 fragment)"
  | .unsupported k _ => .error s!"unsupported generate item `{k}`"

def itemsOf? (ds : List DeclT) (tag : String) : Nat → List GenItem → Except String (List TItem)
  | _, [] => .ok []
  | pos, it :: rest =>
      match itemOf? ds tag pos it with
      | .error e => .error e
      | .ok x =>
          match itemsOf? ds tag (pos + 1) rest with
          | .error e => .error e
          | .ok xs => .ok (x :: xs)

def famOf? (ds : List DeclT) : GenItem → Except String TFam
  | .genFor label g initE bound step rc body =>
      match hdrOf? label g initE bound step with
      | .error e => .error e
      | .ok h =>
          match itemsOf? ds h.name 0 body with
          | .error e => .error e
          | .ok its => .ok ⟨h, rc, its⟩
  | .genIf .. => .error "conditional generate (outside the v1 fragment)"
  | .inst _ => .error "module instance (outside the v1 fragment)"
  | .process _ => .error "process item in the generate list"
  | .unsupported k _ => .error s!"unsupported generate item `{k}`"

def famsOf? (ds : List DeclT) : List GenItem → Except String (List TFam)
  | [] => .ok []
  | it :: rest =>
      match famOf? ds it with
      | .error e => .error e
      | .ok f =>
          match famsOf? ds rest with
          | .error e => .error e
          | .ok fs => .ok (f :: fs)

/-! ## Local parameters

A `localparam L = <constant expression of the parameters>` enters the view as one more NAMED CONSTANT:
`Summary.params` lists the module parameters and then the localparams (the names an `Aff` may
mention), and `Summary.lps` keeps each localparam's definition as a `CE`, a tiny constant-expression
language (integer literals, references to parameters and EARLIER localparams, `+`, `-`, `*` by a
literal, `/` and `%` by a positive literal). `Summary.val s args` is the valuation of all the constants:
the parameters zipped with the arguments, then each localparam evaluated over what precedes it.

Nothing here is trusted. `Summary.sound` and everything built on it need only
`Agrees σ env s.params` for the environment `paramEnv2` really produced; the tactics close that by
`rfl` per design (the localparam really sits in `env.vals`, bound by `bindLocal`, at the value
`CE.eval` computes), so a `CE` that disagreed with the instantiation makes `hag` fail to close. The
operations are `evalInt`'s own (`Int.tdiv`/`Int.tmod`, the operand order of `+ - *`), which is what
lets `rfl` see through the symbolic parameter. -/

/-- The definition of a localparam. -/
inductive CE where
  | lit (v : Int)
  | ref (n : String)
  | add (a b : CE)
  | sub (a b : CE)
  | mul (a b : CE)
  | divK (a : CE) (k : Int)
  | modK (a : CE) (k : Int)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The value of a definition, with `evalInt`'s own operations (`/` and `%` truncate toward zero). -/
def CE.eval (σ : String → Int) : CE → Int
  | .lit v => v
  | .ref n => σ n
  | .add a b => a.eval σ + b.eval σ
  | .sub a b => a.eval σ - b.eval σ
  | .mul a b => a.eval σ * b.eval σ
  | .divK a k => (a.eval σ).tdiv k
  | .modK a k => (a.eval σ).tmod k

/-- The bindings of the localparams, each evaluated over the bindings before it (latest first). -/
def lpEnv : List (String × CE) → List (String × Int) → List (String × Int)
  | [], acc => acc
  | (n, c) :: rest, acc => lpEnv rest ((n, c.eval (σL acc)) :: acc)

def CE.isLit : CE → Bool
  | .lit _ => true
  | _ => false

def ceMul (nm : String) (a b : CE) : Except String CE :=
  if a.isLit || b.isLit then .ok (.mul a b)
  else .error s!"localparam `{nm}`: a product of two non-constant factors is outside the v1 fragment (`*` needs an integer-literal factor, so that the obligations stay linear)"

def ceBin (nm : String) : SymBinOp → CE → CE → Except String CE
  | .m0 .add, a, b => .ok (.add a b)
  | .m0 .sub, a, b => .ok (.sub a b)
  | .mul, a, b => ceMul nm a b
  | .m0 .mul, a, b => ceMul nm a b
  | .div, a, .lit k =>
      if 0 < k then .ok (.divK a k)
      else .error s!"localparam `{nm}`: `/` by the literal {k} is outside the v1 fragment (a positive literal divisor is required)"
  | .div, _, _ =>
      .error s!"localparam `{nm}`: `/` by a non-literal is outside the v1 fragment (a localparam may divide by an integer literal)"
  | .mod, a, .lit k =>
      if 0 < k then .ok (.modK a k)
      else .error s!"localparam `{nm}`: `%` by the literal {k} is outside the v1 fragment (a positive literal divisor is required)"
  | .mod, _, _ =>
      .error s!"localparam `{nm}`: `%` by a non-literal is outside the v1 fragment (a localparam may take a remainder by an integer literal)"
  | op, _, _ =>
      .error s!"localparam `{nm}`: operator `{op.sym}` is outside the v1 fragment (a localparam may use + - *, and / % by an integer literal)"

/-- Recognize a localparam's initializer, in the scope of the names bound before it. -/
def ceOf? (nm : String) (scope : List String) : PExpr → Except String CE
  | .int v => .ok (.lit v)
  | .paramRef n none =>
      if scope.contains n then .ok (.ref n)
      else .error s!"localparam `{nm}`: `{n}` is neither a parameter nor an earlier localparam"
  | .binary op l r =>
      match ceOf? nm scope l with
      | .error e => .error e
      | .ok a =>
          match ceOf? nm scope r with
          | .error e => .error e
          | .ok b => ceBin nm op a b
  | .squash2 _ a =>
      match ceOf? nm scope a with
      | .error e => .error e
      | .ok _ =>
          .error s!"localparam `{nm}`: a 2-state `int` localparam initialised by `/` or `%` is squashed to 2 states and wraps at 2^31 in the elaborated design (its closed arithmetic form would be false for huge parameters); declare it `localparam integer {nm} = …;` (outside the v1 fragment)"
  | .sysCall .clog2 _ =>
      .error s!"localparam `{nm}`: `$clog2` is outside the v1 fragment (it is not a linear function of the parameters; a localparam may use + - *, and / % by an integer literal)"
  | .sysCall .. =>
      .error s!"localparam `{nm}`: a system call is outside the v1 fragment (a localparam may use + - *, and / % by an integer literal)"
  | _ =>
      .error s!"localparam `{nm}`: the initializer is outside the v1 fragment (a localparam may use integer literals, parameters, earlier localparams, + - *, and / % by an integer literal)"

/-- The localparam's declared type: `int`/`integer` (packed `[31:0]`, signed or default) or none — the
INT class, which `bindLocal` binds in `IEnv.vals`, where the parameters are. -/
def lpTypeOk (lp : PLocalParam) : Bool :=
  lp.signed? != some false &&
    match lp.type? with
    | none => true
    | some (.packed [⟨.int 31, .int 0⟩] _) => true
    | _ => false

def lpOf? (scope : List String) (lp : PLocalParam) : Except String CE :=
  if !lpTypeOk lp then
    .error s!"localparam `{lp.name}`: only `int`/`integer` (32-bit signed) localparams are in the v1 fragment"
  else ceOf? lp.name scope lp.expr

def lpsOf? : List String → List PLocalParam → Except String (List (String × CE))
  | _, [] => .ok []
  | scope, lp :: rest =>
      match lpOf? scope lp with
      | .error e => .error e
      | .ok c =>
          match lpsOf? (scope ++ [lp.name]) rest with
          | .error e => .error e
          | .ok cs => .ok ((lp.name, c) :: cs)

/-! ## The summary -/

structure Summary where
  /-- The constant names: the module parameters, then the localparams. -/
  params : List String
  decls : List DeclT
  statics : List TSite
  fams : List TFam
  /-- The localparams and their definitions (empty for a design without any). -/
  lps : List (String × CE) := []
deriving Repr, Inhabited

/-- The valuation of all the constants at the arguments: the parameters zipped with `args`
(`List.zip` stops at the parameters), then the localparams. For a design without localparams this IS
`σL (s.params.zip args)`. -/
def Summary.val (s : Summary) (args : List Int) : String → Int :=
  σL (lpEnv s.lps (s.params.zip args))

def _root_.LeanModels.Sv.PDesign.summary (d : PDesign) : Except String Summary :=
  match lpsOf? (d.params.map (·.name)) d.localParams with
  | .error e => .error e
  | .ok lps =>
      if !d.enums.isEmpty then .error "enums are outside the v1 fragment"
      else if !d.others.isEmpty then .error "out-of-tier module members are present"
      else
        match declsOf? d.decls with
        | .error e => .error e
        | .ok ds =>
            match sitesOf? ds "plain" 0 d.processes with
            | .error e => .error e
            | .ok sts =>
                match famsOf? ds d.generates with
                | .error e => .error e
                | .ok fs =>
                    .ok { params := d.params.map (·.name) ++ lps.map Prod.fst, decls := ds,
                          statics := sts, fams := fs, lps := lps }

/-- A site together with the loops that enclose it (outermost first) and the label of the
innermost enclosing block (`"plain"` for a module-level process). -/
structure LSite where
  hdrs : List Hdr
  blk : String
  site : TSite
deriving Repr, Inhabited

/-- The site's identity at a valuation of its enclosing loop indices. -/
def LSite.id (ls : LSite) (σ : String → Int) : SiteId :=
  match ls.hdrs with
  | [] => .plain ls.site.pos
  | _ => .fam ls.blk ls.site.pos (ls.hdrs.map fun h => σ h.g)

/-- The static identity of a site (unique per site on a design the structural check accepts). -/
def LSite.key (ls : LSite) : String × Nat × Nat :=
  ((if ls.hdrs.isEmpty then "plain" else ls.blk), ls.site.pos, ls.hdrs.length)

/-- The located sites of one item of an outer loop's body. -/
def TFam.itemLs (f : TFam) : TItem → List LSite
  | .site st => [⟨[f.hdr], f.hdr.name, st⟩]
  | .loop l => l.body.map fun st => ⟨[f.hdr, l.hdr], l.hdr.name, st⟩

/-- The located sites of a top-level loop. -/
def TFam.lsites (f : TFam) : List LSite := f.body.flatMap f.itemLs

namespace Summary

variable (s : Summary)

def declNames : List String := s.decls.map (·.name)
def inputNames : List String := s.decls.filterMap fun dt => if dt.isInput then some dt.name else none
def find (n : String) : Option DeclT := findDecl s.decls n
def dimsOf' (n : String) : Option (List (Aff × Aff)) := dimsOf s.decls n

/-- Declared width of a signal (`0` when undeclared). -/
def dw (σ : String → Int) (n : String) : Nat := ((s.find n).map (·.width σ)).getD 0

/-- The widths as the `IEnv.widths`/`Design2.declWidth` view of the declaration scope. -/
def DW (σ : String → Int) (n : String) : Option Nat := (s.find n).map (·.width σ)

/-- The evaluated packed dimensions, as `IEnv.dims` records them. -/
def DG (σ : String → Int) (n : String) : Option (List (Int × Int)) := (s.find n).map (·.vals σ)

/-- The element width, as `buildElems` records it. -/
def EW (σ : String → Int) (n : String) : Option Nat := (s.find n).map (·.elemW σ)

/-- The most significant label of the `k`-th packed dimension (`0` if there is none). -/
def dm (σ : String → Int) (n : String) (k : Nat) : Int :=
  match s.find n with
  | none => 0
  | some dt =>
      match dt.dims[k]? with
      | none => 0
      | some p => p.2.1.eval σ

/-- The access is consistent with the declaration it names: right number of dimensions, zero-based
descending, and the recorded row width is the second dimension's extent. -/
def accOk : Acc → Bool
  | .whole n => (s.find n).isSome
  | .bit n _ =>
      match s.dimsOf' n with
      | some [] => true
      | some [_] => true
      | _ => false
  | .cell1 n _ =>
      match s.dimsOf' n with
      | some [(_, l)] => decide (l = Aff.const 0)
      | _ => false
  | .row n w _ =>
      match s.dimsOf' n with
      | some [(_, l1), (m2, l2)] =>
          decide (l1 = Aff.const 0) && decide (l2 = Aff.const 0) && decide (w = m2.add (Aff.const 1))
      | _ => false
  | .cell2 n w _ _ =>
      match s.dimsOf' n with
      | some [(_, l1), (m2, l2)] =>
          decide (l1 = Aff.const 0) && decide (l2 = Aff.const 0) && decide (w = m2.add (Aff.const 1))
      | _ => false
  | .part1 n _ _ =>
      match s.dimsOf' n with
      | some [(_, l)] => decide (l = Aff.const 0)
      | _ => false
  | .part2 n w _ _ _ =>
      match s.dimsOf' n with
      | some [(_, l1), (m2, l2)] =>
          decide (l1 = Aff.const 0) && decide (l2 = Aff.const 0) && decide (w = m2.add (Aff.const 1))
      | _ => false

/-- The located sites, in instantiation order of their first instances. -/
def lsites : List LSite :=
  s.statics.map (fun st => (⟨[], "plain", st⟩ : LSite)) ++ s.fams.flatMap TFam.lsites

/-- The loop-header paths of the generate tree: each top-level loop alone, and each inner loop
under its outer loop (outermost first). -/
def hdrPaths : List (List Hdr) :=
  s.fams.flatMap fun f =>
    [f.hdr] :: f.body.filterMap fun it =>
      match it with
      | .site _ => none
      | .loop l => some [f.hdr, l.hdr]

end Summary

/-! ## What the summary promises: footprints of the instantiated processes -/

/-- The footprint of one process instance. -/
structure SiteInst where
  id : SiteId
  win : Win
  tgt : Lhs2
  rd : List ReadWin

/-- The footprint of a located site at a valuation of its loops. -/
def LSite.inst (ls : LSite) (σ : String → Int) (dw : String → Nat) : SiteInst :=
  { id := ls.id σ, win := ls.site.tgt.win σ dw, tgt := ls.site.tgt.lhs σ,
    rd := ls.site.rds.map (Acc.rd σ) }

/-- The valuation reached by binding the loops' indices, and the environment reached alongside
it (`IEnv.bindVal`). -/
def Reach : List Hdr → (String → Int) → (String → Int) → Prop
  | [], σ, σ' => σ' = σ
  | h :: hs, σ, σ' => ∃ i, h.Rng σ i ∧ Reach hs (bindσ h.g i σ) σ'

def ReachE : List Hdr → (String → Int) → IEnv → (String → Int) → IEnv → Prop
  | [], σ, E, σ', E' => σ' = σ ∧ E' = E
  | h :: hs, σ, E, σ', E' => ∃ i, h.Rng σ i ∧ ReachE hs (bindσ h.g i σ) (E.bindVal h.g i) σ' E'

/-- `P` holds at every valuation of the loops (nested `∀`, outermost first). -/
def Loops.all : List Hdr → (String → Int) → ((String → Int) → Prop) → Prop
  | [], σ, P => P σ
  | h :: hs, σ, P => ∀ i, h.Rng σ i → Loops.all hs (bindσ h.g i σ) P

theorem Loops.all_iff : ∀ (hs : List Hdr) (σ : String → Int) (P : (String → Int) → Prop),
    Loops.all hs σ P ↔ ∀ σ', Reach hs σ σ' → P σ'
  | [], σ, P => by simp [Loops.all, Reach]
  | h :: hs, σ, P => by
      simp only [Loops.all, Reach]
      constructor
      · intro H σ' ⟨i, hi, hr⟩
        exact (Loops.all_iff hs _ P).mp (H i hi) σ' hr
      · intro H i hi
        exact (Loops.all_iff hs _ P).mpr fun σ' hr => H σ' ⟨i, hi, hr⟩

theorem ReachE_Reach : ∀ {hs : List Hdr} {σ : String → Int} {E : IEnv} {σ' : String → Int}
    {E' : IEnv}, ReachE hs σ E σ' E' → Reach hs σ σ'
  | [], σ, E, σ', E', h => h.1
  | h :: hs, σ, E, σ', E', ⟨i, hi, hr⟩ => ⟨i, hi, ReachE_Reach hr⟩

theorem Reach_ReachE : ∀ {hs : List Hdr} {σ : String → Int} {σ' : String → Int} (E : IEnv),
    Reach hs σ σ' → ∃ E', ReachE hs σ E σ' E'
  | [], σ, σ', E, h => ⟨E, h, rfl⟩
  | h :: hs, σ, σ', E, ⟨i, hi, hr⟩ => by
      obtain ⟨E', hE⟩ := Reach_ReachE (E.bindVal h.g i) hr
      exact ⟨E', i, hi, hE⟩

/-- **The closed-form list**: each located site, instantiated at every valuation of its loops, in
`instantiate2`'s order (module-level processes, then each generate loop: for each outer index, the
body's items in order, an inner loop contributing its sites for each inner index). The builder
`b` receives the located site, the valuation and the environment. -/
def TFam.itemEnum {β : Type} (b : LSite → (String → Int) → IEnv → β) (σ : String → Int) (E : IEnv)
    (f : TFam) (i : Int) : TItem → List β
  | .site st => [b ⟨[f.hdr], f.hdr.name, st⟩ (bindσ f.hdr.g i σ) (E.bindVal f.hdr.g i)]
  | .loop l => (l.hdr.range (bindσ f.hdr.g i σ)).flatMap fun j =>
      l.body.map fun st =>
        b ⟨[f.hdr, l.hdr], l.hdr.name, st⟩ (bindσ l.hdr.g j (bindσ f.hdr.g i σ))
          ((E.bindVal f.hdr.g i).bindVal l.hdr.g j)

def TFam.enum {β : Type} (b : LSite → (String → Int) → IEnv → β) (σ : String → Int) (E : IEnv)
    (f : TFam) : List β :=
  (f.hdr.range σ).flatMap fun i => f.body.flatMap fun it => f.itemEnum b σ E i it

def Summary.enum {β : Type} (s : Summary) (b : LSite → (String → Int) → IEnv → β)
    (σ : String → Int) (E : IEnv) : List β :=
  s.statics.map (fun st => b ⟨[], "plain", st⟩ σ E) ++ s.fams.flatMap fun f => TFam.enum b σ E f

def Summary.insts (s : Summary) (σ : String → Int) (E : IEnv := {}) : List SiteInst :=
  s.enum (fun ls σ' _ => ls.inst σ' (s.dw σ)) σ E

/-- The realized list: each promised footprint next to the process the real instantiation builds
for it. -/
def Summary.pairs (s : Summary) (σ : String → Int) (E : IEnv) (elems : List (String × Nat)) :
    List (SiteInst × Process2) :=
  s.enum (fun ls σ' E' => (ls.inst σ' (s.dw σ), instProcess2 E' elems ls.site.proc)) σ E

theorem TFam.itemEnum_map {β γ : Type} (b : LSite → (String → Int) → IEnv → β) (g : β → γ)
    (σ : String → Int) (E : IEnv) (f : TFam) (i : Int) (it : TItem) :
    (f.itemEnum b σ E i it).map g = f.itemEnum (fun ls σ' E' => g (b ls σ' E')) σ E i it := by
  cases it with
  | site st => simp [TFam.itemEnum]
  | loop l => simp [TFam.itemEnum, List.map_flatMap, List.map_map, Function.comp_def]

theorem TFam.enum_map {β γ : Type} (b : LSite → (String → Int) → IEnv → β) (g : β → γ)
    (σ : String → Int) (E : IEnv) (f : TFam) :
    (TFam.enum b σ E f).map g = TFam.enum (fun ls σ' E' => g (b ls σ' E')) σ E f := by
  unfold TFam.enum
  simp only [List.map_flatMap]
  apply flatMap_congr'
  intro i _
  apply flatMap_congr'
  intro it _
  exact TFam.itemEnum_map b g σ E f i it

theorem Summary.enum_map {β γ : Type} (s : Summary) (b : LSite → (String → Int) → IEnv → β)
    (g : β → γ) (σ : String → Int) (E : IEnv) :
    (s.enum b σ E).map g = s.enum (fun ls σ' E' => g (b ls σ' E')) σ E := by
  unfold Summary.enum
  simp only [List.map_append, List.map_map, List.map_flatMap, Function.comp_def]
  congr 1
  apply flatMap_congr'
  intro f _
  exact TFam.enum_map b g σ E f

theorem Summary.pairs_map_fst (s : Summary) (σ : String → Int) (E : IEnv)
    (elems : List (String × Nat)) : (s.pairs σ E elems).map Prod.fst = s.insts σ E := by
  unfold Summary.pairs
  rw [Summary.enum_map]
  rfl

/-! ## The declaration stage -/

theorem declOf?_spec {pd : PDecl} {dt : DeclT} (h : declOf? pd = .ok dt) :
    dt.name = pd.name ∧ dt.isInput = pd.isInput ∧ dt.isOutput = pd.isOutput ∧ pd.init = none ∧
    (∃ r, pd.type = .packed dt.pdims r) ∧ dt.dims.length ≤ 2 ∧
    (∀ p ∈ dt.dims, affOf? p.1.msb = some p.2.1 ∧ affOf? p.1.lsb = some p.2.2) ∧
    pd.isSigned = false ∧ pd.twoState = false := by
  have hdim : ∀ {nm : String} {d : PDim} {p : PDim × Aff × Aff}, dimOf? nm d = .ok p →
      p.1 = d ∧ affOf? p.1.msb = some p.2.1 ∧ affOf? p.1.lsb = some p.2.2 := by
    intro nm d p hp
    unfold dimOf? at hp
    rcases hm : affOf? d.msb with _ | m <;> rcases hl : affOf? d.lsb with _ | l <;>
      simp [hm, hl] at hp
    subst hp
    exact ⟨rfl, hm, hl⟩
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
      match ds, h with
      | [], h =>
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨rfl, rfl, rfl, rfl, ⟨r, by simp [DeclT.pdims]⟩, by simp, ?_, hs.1, hs.2⟩
        intro p hp; simp at hp
      | [d], h =>
        rcases hp : dimOf? pd.name d with e | p
        · simp [hp] at h
        · simp only [hp, Except.ok.injEq] at h
          subst h
          obtain ⟨h1, h2, h3⟩ := hdim hp
          refine ⟨rfl, rfl, rfl, rfl, ⟨r, by simp [DeclT.pdims, h1]⟩, by simp, ?_, hs.1, hs.2⟩
          intro q hq
          simp only [List.mem_singleton] at hq
          subst hq
          exact ⟨h2, h3⟩
      | [d1, d2], h =>
        rcases hp1 : dimOf? pd.name d1 with e | p1
        · simp [hp1] at h
        · rcases hp2 : dimOf? pd.name d2 with e | p2
          · simp [hp1, hp2] at h
          · simp only [hp1, hp2, Except.ok.injEq] at h
            subst h
            obtain ⟨h1, h2, h3⟩ := hdim hp1
            obtain ⟨k1, k2, k3⟩ := hdim hp2
            refine ⟨rfl, rfl, rfl, rfl, ⟨r, by simp [DeclT.pdims, h1, k1]⟩, by simp, ?_, hs.1, hs.2⟩
            intro q hq
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
            rcases hq with rfl | rfl
            · exact ⟨h2, h3⟩
            · exact ⟨k2, k3⟩
      | _ :: _ :: _ :: _, h => simp at h
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

/-- `evalDims` of the recognized dimensions, computed. -/
theorem evalDims_dims {env : IEnv} {σ : String → Int} :
    ∀ (dims : List (PDim × Aff × Aff)),
      (∀ p ∈ dims, affOf? p.1.msb = some p.2.1 ∧ affOf? p.1.lsb = some p.2.2) →
      (∀ p ∈ dims, ∀ n ∈ p.2.1.names ++ p.2.2.names, env.vals.lookup n = some (σ n)) →
      evalDims env (dims.map (·.1)) = .ok (dims.map fun p => (p.2.1.eval σ, p.2.2.eval σ))
  | [], _, _ => by simp
  | p :: rest, ha, hg => by
      obtain ⟨hm, hl⟩ := ha p (List.mem_cons_self ..)
      have hm' : ∀ n ∈ p.2.1.names, env.vals.lookup n = some (σ n) :=
        fun n hn => hg p (List.mem_cons_self ..) n (List.mem_append_left _ hn)
      have hl' : ∀ n ∈ p.2.2.names, env.vals.lookup n = some (σ n) :=
        fun n hn => hg p (List.mem_cons_self ..) n (List.mem_append_right _ hn)
      obtain ⟨-, hem⟩ := affOf?_sound _ _ hm hm'
      obtain ⟨-, hel⟩ := affOf?_sound _ _ hl hl'
      have ih := evalDims_dims rest (fun q hq => ha q (List.mem_cons_of_mem _ hq))
        (fun q hq => hg q (List.mem_cons_of_mem _ hq))
      exact evalDims_cons_of hem hel ih

/-- `PType.width` of the recognized dimensions, computed. -/
theorem width_dims {env : IEnv} {σ : String → Int} (r : Option Nat) :
    ∀ (dims : List (PDim × Aff × Aff)),
      (∀ p ∈ dims, affOf? p.1.msb = some p.2.1 ∧ affOf? p.1.lsb = some p.2.2) →
      (∀ p ∈ dims, ∀ n ∈ p.2.1.names ++ p.2.2.names, env.vals.lookup n = some (σ n)) →
      (PType.packed (dims.map (·.1)) r).width env = .ok (dimsW σ dims)
  | [], _, _ => by simp [dimsW]
  | p :: rest, ha, hg => by
      obtain ⟨hm, hl⟩ := ha p (List.mem_cons_self ..)
      have hm' : ∀ n ∈ p.2.1.names, env.vals.lookup n = some (σ n) :=
        fun n hn => hg p (List.mem_cons_self ..) n (List.mem_append_left _ hn)
      have hl' : ∀ n ∈ p.2.2.names, env.vals.lookup n = some (σ n) :=
        fun n hn => hg p (List.mem_cons_self ..) n (List.mem_append_right _ hn)
      obtain ⟨-, hem⟩ := affOf?_sound _ _ hm hm'
      obtain ⟨-, hel⟩ := affOf?_sound _ _ hl hl'
      have ih := width_dims r rest (fun q hq => ha q (List.mem_cons_of_mem _ hq))
        (fun q hq => hg q (List.mem_cons_of_mem _ hq))
      rw [List.map_cons, PType.width_packed_cons, ih]
      simp [PDim.width, hem, hel, dimsW, Gen2.except_ok_bind]

theorem dt_agree {env : IEnv} {σ : String → Int} {dt : DeclT}
    (hag : ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n)) :
    ∀ p ∈ dt.dims, ∀ n ∈ p.2.1.names ++ p.2.2.names, env.vals.lookup n = some (σ n) := by
  intro p hp n hn
  apply hag n
  simp only [DeclT.affNames, List.mem_flatMap]
  exact ⟨p, hp, hn⟩

/-- `dimsWidth` of a declaration, computed. -/
theorem width_decl {env : IEnv} {σ : String → Int} {pd : PDecl} {dt : DeclT}
    (hd : declOf? pd = .ok dt)
    (hag : ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n)) :
    pd.type.width env = .ok (dt.width σ) := by
  obtain ⟨-, -, -, -, ⟨r, hr⟩, -, hdim, -, -⟩ := declOf?_spec hd
  rw [hr]
  exact width_dims r dt.dims hdim (dt_agree hag)

theorem elemWidth_decl {env : IEnv} {σ : String → Int} {pd : PDecl} {dt : DeclT}
    (hd : declOf? pd = .ok dt)
    (hag : ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n)) :
    pd.type.elemWidth env = .ok (dt.elemW σ) := by
  obtain ⟨-, -, -, -, ⟨r, hr⟩, hlen, hdim, -, -⟩ := declOf?_spec hd
  rw [hr]
  have hag' := dt_agree hag
  unfold DeclT.pdims
  match hdt : dt.dims, hlen with
  | [], _ => simp [DeclT.elemW, hdt]
  | [p], _ => simp [DeclT.elemW, hdt]
  | [p1, p2], _ =>
      have hp2 : p2 ∈ dt.dims := by rw [hdt]; simp
      have hm : affOf? p2.1.msb = some p2.2.1 := (hdim p2 hp2).1
      have hl : affOf? p2.1.lsb = some p2.2.2 := (hdim p2 hp2).2
      obtain ⟨-, hem⟩ := affOf?_sound _ _ hm
        (fun n hn => hag' p2 hp2 n (List.mem_append_left _ hn))
      obtain ⟨-, hel⟩ := affOf?_sound _ _ hl
        (fun n hn => hag' p2 hp2 n (List.mem_append_right _ hn))
      simp [PType.elemWidth, DeclT.elemW, hdt, PDim.width, hem, hel, List.foldlM, Gen2.except_ok_bind]
  | _ :: _ :: _ :: _, hl => simp at hl

theorem buildDecls_summary {σ : String → Int} :
    ∀ (ds : List PDecl) (sd : List DeclT), declsOf? ds = .ok sd →
      ∀ (env : IEnv), (∀ dt ∈ sd, ∀ n ∈ dt.affNames, env.vals.lookup n = some (σ n)) →
        buildDecls env ds = .ok (sd.map (·.toDecl σ))
  | [], sd, h, env, _ => by
      simp [declsOf?] at h; subst h; rfl
  | pd :: rest, sd, h, env, hag => by
      obtain ⟨dt, sd', hd, hr, rfl⟩ := declsOf?_cons h
      obtain ⟨hn, hi, ho, hinit, -, -, -, hsg, hts⟩ := declOf?_spec hd
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
        buildElems env ds = .ok (sd.map fun dt => (dt.name, dt.elemW σ))
  | [], sd, h, env, _ => by
      simp [declsOf?] at h; subst h; rfl
  | pd :: rest, sd, h, env, hag => by
      obtain ⟨dt, sd', hd, hr, rfl⟩ := declsOf?_cons h
      obtain ⟨hn, -, -, -, -, -, -, -, -⟩ := declOf?_spec hd
      have hw := width_decl (env := env) (σ := σ) hd (fun n hn => hag dt (by simp) n hn)
      have hrest := buildElems_summary rest sd' hr
        { env with widths := (pd.name, dt.width σ) :: env.widths }
        (fun dt' hdt' n hn => hag dt' (by simp [hdt']) n hn)
      have hew := elemWidth_decl (env := env) (σ := σ) hd (fun n hn => hag dt (by simp) n hn)
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
      obtain ⟨hn, -, -, -, ⟨r, hr'⟩, -, hdim, -, -⟩ := declOf?_spec hd
      have hrest := dimTable_summary rest sd' hr (dimTableStep env pd)
        (fun dt' hdt' n' hn' => by
          rw [dimTableStep_vals]; exact hag dt' (by simp [hdt']) n' hn') n
      have hev : evalDims env dt.pdims = .ok (dt.vals σ) :=
        evalDims_dims dt.dims hdim (dt_agree (fun n hn => hag dt (by simp) n hn))
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
