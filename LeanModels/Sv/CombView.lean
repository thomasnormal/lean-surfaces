import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Comb2Base
import LeanModels.Sv.CombViewArith
import LeanModels.Sv.Loop2

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
  earlier localparams: `+ - *` by a literal, `/` `%` by a positive literal, `$clog2`): one more NAMED CONSTANT,
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
  ∀ n ∈ ns, E.intVal? n = some (σ n)

/-- Every named constant used by the affine view is representable by the
exact signed-32 `int` instantiation.  This is the refinement premise that
lets the view's affine arithmetic agree with `evalIntExact`; it is kept
separate from `Agrees` so existing non-parametric proofs retain their shape.
-/
def IntRange (σ : String → Int) (ns : List String) : Prop :=
  ∀ n ∈ ns, -2147483648 ≤ σ n ∧ σ n < 2147483648

/-- All intermediate affine values used by an exact constant fold are
representable signed-32 values.  This is deliberately a premise over the
recognized affine form, rather than a fuel or a hidden evaluator guard. -/
def Aff.InInt32 (σ : String → Int) (a : Aff) : Prop :=
  -2147483648 ≤ a.eval σ ∧ a.eval σ < 2147483648


theorem IntRange.mono {σ : String → Int} {ns ms : List String}
    (h : IntRange σ ns) (hs : ∀ n ∈ ms, n ∈ ns) : IntRange σ ms :=
  fun n hn => h n (hs n hn)


theorem canonInt32_of_range {v : Int} (h : -2147483648 ≤ v ∧ v < 2147483648) :
    canonInt 32 true v = v := by
  exact Loop2.int32_of_inInt32 h

theorem evalIntExact_paramRef {E : IEnv} {n : String} {v : Int}
    (hm : E.int32 = true) (h : IEnv.intVal? E n = some v) :
    evalIntExact E (.paramRef n none) = .ok (canonInt 32 true v) := by
  simp [evalIntExact, evalIntExactRec, h, hm]

theorem evalIntExact_genvarRef {E : IEnv} {n : String} {v : Int}
    (hm : E.int32 = true) (h : IEnv.intVal? E n = some v) :
    evalIntExact E (.genvarRef n) = .ok (canonInt 32 true v) := by
  simp [evalIntExact, evalIntExactRec, h, hm]

/-! The exact view consumes the signed-32 `nvals` binding directly.  This
guard keeps the public range premise visible: a representable symbolic value
is the same value after the exact leaf fold, without falling back to the old
unbounded `vals` path. -/
example (v : Int) (hr : -2147483648 ≤ v ∧ v < 2147483648) :
    evalIntExact
        ({ nvals := [("N", (v, 32, true))], int32 := true } : IEnv)
        (.paramRef "N" none) = .ok v := by
  rw [evalIntExact_paramRef (hm := rfl) (h := by rfl), canonInt32_of_range hr]

theorem isInt_paramRef_of_intVal {E : IEnv} {n : String} {v : Int}
    (h : E.intVal? n = some v) : (PExpr.paramRef n none).isInt E = true := by
  rcases IEnv.intVal?_cases h with hv | ⟨w, s, hn, rfl, rfl⟩
  · simp [PExpr.isInt, hv]
  · cases hv : E.vals.lookup n <;> simp [PExpr.isInt, hv, hn]

theorem evalInt_paramRef_of_intVal {E : IEnv} {n : String} {v : Int}
    (h : E.intVal? n = some v) : evalInt E (.paramRef n none) = .ok v := by
  rcases IEnv.intVal?_cases h with hv | ⟨w, s, hn, rfl, rfl⟩
  · simp [evalInt, hv]
  · cases hv : E.vals.lookup n with
    | none => simp [evalInt, IEnv.intVal?, hv, hn]
    | some x =>
        have heq : x = v := by simpa [IEnv.intVal?, hv, hn] using h
        subst x
        simp [evalInt, hv, hn]

theorem evalInt_genvarRef_of_intVal {E : IEnv} {n : String} {v : Int}
    (h : E.intVal? n = some v) : evalInt E (.genvarRef n) = .ok v := by
  rcases IEnv.intVal?_cases h with hv | ⟨w, s, hn, rfl, rfl⟩
  · simp [evalInt, hv]
  · cases hv : E.vals.lookup n with
    | none => simp [evalInt, IEnv.intVal?, hv, hn]
    | some x =>
        have heq : x = v := by simpa [IEnv.intVal?, hv, hn] using h
        subst x
        simp [evalInt, hv, hn]

theorem Agrees.bindVal {σ : String → Int} {E : IEnv} {ns : List String} (h : Agrees σ E ns)
    (g : String) (i : Int) : Agrees (bindσ g i σ) (E.bindVal g i) (g :: ns) := by
  intro n hn
  by_cases hng : n = g
  · subst hng
    simp [IEnv.intVal?_bindVal_self]
  · have hns : n ∈ ns := by
      rcases List.mem_cons.mp hn with h' | h'
      · exact absurd h' hng
      · exact h'
    rw [IEnv.intVal?_bindVal_ne i hng, h n hns, bindσ_ne hng]

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

/-! Exact semantic folds need a premise that every recognized affine result
stays in the signed-32 range. -/
def ExactAffObl (σ : String → Int) (e : PExpr) : Prop :=
  ∀ a, affOf? e = some a → Aff.InInt32 σ a

theorem ExactAffObl.mono {σ : String → Int} {e : PExpr}
    (h : ExactAffObl σ e) : ExactAffObl σ e := h

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
      (∀ n ∈ a.names, E.intVal? n = some (σ n)) →
      e.isInt E = true ∧ evalInt E e = .ok (a.eval σ)
  | .int v, a, h, _ => by
      simp only [affOf?, Option.some.injEq] at h
      subst h
      simp [PExpr.isInt, Aff.eval_const]
  | .genvarRef n, a, h, hb => by
      simp only [affOf?, Option.some.injEq] at h
      subst h
      have hl : E.intVal? n = some (σ n) := hb n (by simp [Aff.names, Aff.var])
      refine ⟨by simp [PExpr.isInt], ?_⟩
      rw [evalInt_genvarRef_of_intVal hl, Aff.eval_var]
  | .paramRef n none, a, h, hb => by
      simp only [affOf?, Option.some.injEq] at h
      subst h
      have hl : E.intVal? n = some (σ n) := hb n (by simp [Aff.names, Aff.var])
      refine ⟨isInt_paramRef_of_intVal hl, ?_⟩
      rw [evalInt_paramRef_of_intVal hl, Aff.eval_var]
  | .binary op l r, a, h, hb => by
      simp only [affOf?] at h
      rcases h1 : affOf? l with _ | a1 <;> rcases h2 : affOf? r with _ | a2 <;>
        simp only [h1, h2] at h <;> try exact absurd h (by simp)
      rcases affBin_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hop, hm⟩
      · have hb1 : ∀ n ∈ a1.names, E.intVal? n = some (σ n) :=
          fun n hn => hb n (by rw [Aff.names_add]; exact List.mem_append_left _ hn)
        have hb2 : ∀ n ∈ a2.names, E.intVal? n = some (σ n) :=
          fun n hn => hb n (by rw [Aff.names_add]; exact List.mem_append_right _ hn)
        obtain ⟨hi1, he1⟩ := affOf?_sound l a1 h1 hb1
        obtain ⟨hi2, he2⟩ := affOf?_sound r a2 h2 hb2
        exact ⟨isInt_binary_of (by simp) hi1 hi2, by rw [evalInt_add_of hi1 hi2 he1 he2, Aff.eval_add]⟩
      · have hb1 : ∀ n ∈ a1.names, E.intVal? n = some (σ n) :=
          fun n hn => hb n (by rw [Aff.names_sub]; exact List.mem_append_left _ hn)
        have hb2 : ∀ n ∈ a2.names, E.intVal? n = some (σ n) :=
          fun n hn => hb n (by rw [Aff.names_sub]; exact List.mem_append_right _ hn)
        obtain ⟨hi1, he1⟩ := affOf?_sound l a1 h1 hb1
        obtain ⟨hi2, he2⟩ := affOf?_sound r a2 h2 hb2
        exact ⟨isInt_binary_of (by simp) hi1 hi2, by rw [evalInt_sub_of hi1 hi2 he1 he2, Aff.eval_sub]⟩
      · have hev := affMul_eval σ hm
        have hn := affMul_names hm
        have hb1 : ∀ n ∈ a1.names, E.intVal? n = some (σ n) := by
          intro n hn1
          rcases hn with ⟨h0, -⟩ | ⟨-, hc⟩
          · simp [Aff.names, h0] at hn1
          · exact hb n (by rw [hc]; exact hn1)
        have hb2 : ∀ n ∈ a2.names, E.intVal? n = some (σ n) := by
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

/-- The count of a replication `{c{x}}` as an affine form (WP-B2 gate 4c; `0` when it is not affine, which the recognizer
refuses before this is read). -/
def repAff (c : PExpr) : Aff := (affOf? c).getD (Aff.const 0)

/-- The names a replication count mentions, and the replication counts, of ONE concatenation part or operand (`[]` for
anything that is not a replication). -/
def repNames : PExpr → List String
  | .repl c _ => (repAff c).names
  | _ => []

def repCount : PExpr → List Aff
  | .repl c _ => [repAff c]
  | _ => []

/-- The names of the constants of the instance a right-hand side mentions (the genvars named as shift amounts, the
names of a replication count): they must be bound where the site is instantiated, like the indices of its accesses
(`TSite.affNames`). -/
def _root_.LeanModels.Sv.PExpr.cnames : PExpr → List String
  | .binary op l r =>
      (match op, r with
       | .m0 (.shl _), .genvarRef g => [g]
       | .m0 (.shr false), .genvarRef g => [g]
       | .m0 (.shl _), .paramRef n none => [n]
       | .m0 (.shr false), .paramRef n none => [n]
       | _, _ => []) ++ l.cnames ++ r.cnames
  | .unary _ a => a.cnames
  | .reduce _ a => a.cnames
  | .ternary c t e => c.cnames ++ t.cnames ++ e.cnames
  | .resize _ a => a.cnames
  | .repl c _ => (repAff c).names
  | .concat ps => ps.flatMap repNames
  | _ => []

/-- The replication counts of a right-hand side: each must be non-negative where the site is instantiated (the model
refuses a negative count loudly), an obligation of `InRangeObl`. -/
def _root_.LeanModels.Sv.PExpr.rcounts : PExpr → List Aff
  | .binary _ l r => l.rcounts ++ r.rcounts
  | .unary _ a => a.rcounts
  | .reduce _ a => a.rcounts
  | .ternary c t e => c.rcounts ++ t.rcounts ++ e.rcounts
  | .resize _ a => a.rcounts
  | .repl c _ => [repAff c]
  | .concat ps => ps.flatMap repCount
  | _ => []

/-- `(v.cnames, v.rcounts)` in ONE traversal (`consts_eq`): the recognizer forces it once per site that is not a leaf
(`forceSite`), where the two functions would each cost a traversal of every right-hand side. -/
def _root_.LeanModels.Sv.PExpr.consts : PExpr → List String × List Aff
  | .binary op l r =>
      let a := l.consts
      let b := r.consts
      ((match op, r with
        | .m0 (.shl _), .genvarRef g => [g]
        | .m0 (.shr false), .genvarRef g => [g]
        | .m0 (.shl _), .paramRef n none => [n]
        | .m0 (.shr false), .paramRef n none => [n]
        | _, _ => []) ++ a.1 ++ b.1, a.2 ++ b.2)
  | .unary _ a => a.consts
  | .reduce _ a => a.consts
  | .ternary c t e =>
      let a := c.consts
      let b := t.consts
      let d := e.consts
      (a.1 ++ b.1 ++ d.1, a.2 ++ b.2 ++ d.2)
  | .resize _ a => a.consts
  | .repl c _ => ((repAff c).names, [repAff c])
  | .concat ps => (ps.flatMap repNames, ps.flatMap repCount)
  | _ => ([], [])

theorem consts_eq : ∀ v : PExpr, v.consts = (v.cnames, v.rcounts)
  | .binary op l r => by
      simp only [PExpr.consts, PExpr.cnames, PExpr.rcounts, consts_eq l, consts_eq r]
  | .unary _ a => by simp only [PExpr.consts, PExpr.cnames, PExpr.rcounts, consts_eq a]
  | .reduce _ a => by simp only [PExpr.consts, PExpr.cnames, PExpr.rcounts, consts_eq a]
  | .ternary c t e => by
      simp only [PExpr.consts, PExpr.cnames, PExpr.rcounts, consts_eq c, consts_eq t, consts_eq e]
  | .resize _ a => by simp only [PExpr.consts, PExpr.cnames, PExpr.rcounts, consts_eq a]
  | .repl c _ => by simp only [PExpr.consts, PExpr.cnames, PExpr.rcounts]
  | .concat ps => by simp only [PExpr.consts, PExpr.cnames, PExpr.rcounts]
  | .lit _ | .fill _ | .ident _ | .bitSel .. | .partSel .. | .arrayElem .. | .arrayPart .. | .paramRef .. | .genvarRef _
  | .enumRef .. | .int _ | .sysCall .. | .cast .. | .signedResize .. | .squash2 .. | .unsupported .. => by
      simp [PExpr.consts, PExpr.cnames, PExpr.rcounts]

/-- The constants of an expression are in scope and its replication counts are non-negative. -/
def ConstOK (σ : String → Int) (ns : List String) (v : PExpr) : Prop :=
  (∀ n ∈ v.cnames, n ∈ ns) ∧ ∀ c ∈ v.rcounts, 0 ≤ c.eval σ

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
  /-- The further target accessors of a body that writes SEVERAL windows (`always_comb`, WP-G S1b): the window of
  `tgt` is the first, those of `more` follow in source order; `rds` are the reads of all of them. `[]` for every
  other site. -/
  more : List Acc
  /-- WP-B2 gate 4b/4c (`R`): the constants of the instance (genvars named as shift amounts, names of a replication count) a
  PLAIN site's right-hand side mentions, and its replication counts; `[]` for a procedural body (its leaves refuse them).
  Stored by the recognizer, so that the structural and range obligations read them by projection (like `more`). -/
  cnames : List String
  rcounts : List Aff
deriving Repr, Inhabited

def TSite.names (st : TSite) : List String := st.tgt.name :: (st.more ++ st.rds).map Acc.name

/-- The names an index of the site mentions, and the constants of the instance its right-hand side mentions: all
must be parameters or enclosing loop variables (the structural obligation). -/
def TSite.affNames (st : TSite) : List String :=
  ((st.tgt.affs.flatMap Aff.names) ++ ((st.more ++ st.rds).flatMap fun r => r.affs.flatMap Aff.names)) ++ st.cnames

/-- `ConstOK` of a site: the constants its right-hand side mentions are in scope `ns`, its replication counts non-negative. -/
def TSite.ConstOK (σ : String → Int) (ns : List String) (st : TSite) : Prop :=
  (∀ n ∈ st.cnames, n ∈ ns) ∧ ∀ c ∈ st.rcounts, 0 ≤ c.eval σ

/-- The accesses of a site: its target, its further targets, then its reads. -/
theorem TSite.mem_accs {st : TSite} {a : Acc} (h : a ∈ st.tgt :: st.rds) :
    a ∈ st.tgt :: (st.more ++ st.rds) := by
  rcases List.mem_cons.mp h with rfl | h
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)

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
  if !pd.unpackedDims.isEmpty then
    .error s!"declaration `{pd.name}`: unpacked array storage outside the v1 fragment (UnpackedDecl:memory)"
  else match pd.init with
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

/-- WP-B2 gate 4a: the access a LEGACY select `n[i]` (the extractor's `BitSel`) stands for. Over a declaration of zero or
one packed dimensions it is one bit; over a zero-based two-dimensional declaration `[hi:0][hi:0]` the select is a WHOLE ROW
(`PExpr.bitSel`: "over a multi-dim packed base this reads one `elemW`-bit chunk"), the access `elemAcc?` makes of the
`ArraySel` encoding of the same row. Any other two-dimensional declaration stays `Acc.bit`, which `Summary.accOk` refuses. -/
def bitAcc? (ds : List DeclT) (n : String) (a : Aff) : Except String Acc :=
  match dimsOf ds n with
  | some [(_, l1), (m2, l2)] =>
      if l1 = Aff.const 0 ∧ l2 = Aff.const 0 then .ok (.row n (m2.add (Aff.const 1)) a) else .ok (.bit n a)
  | _ => .ok (.bit n a)

theorem bitAcc?_cases (ds : List DeclT) (n : String) (a : Aff) :
    bitAcc? ds n a = .ok (.bit n a) ∨ ∃ w, bitAcc? ds n a = .ok (.row n w a) := by
  unfold bitAcc?
  split
  · split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- A read of one access. -/
def leafRd? (ds : List DeclT) : PExpr → Except String Acc
  | .ident n => .ok (.whole n)
  | .bitSel b i =>
      match b with
      | .ident n =>
          match affOf? i with
          | some a => bitAcc? ds n a
          | none => .error s!"non-affine genvar-index obligation: read `{n}[…]` has a dynamic or nonlinear index, so the driven window cannot be determined"
      | _ => .error "bit select of a non-identifier base"
  | .partSel b msb lsb =>
      match b with
      | .ident n => partAcc? ds n [] .range msb lsb
      | _ => .error "part select of a non-identifier base"
  | .arrayElem n is => elemAcc? ds n is
  | .arrayPart n is mode hi lo => partAcc? ds n is mode hi lo
  | .unary .. => .error "unary operator in this position (outside the v1 fragment: `~` and `!` are allowed as a whole right-hand side, an operand or a condition, not inside a concatenation part)"
  | .ternary .. => .error "conditional expression `?:` in this position (outside the v1 fragment: allowed as a whole right-hand side, an operand or a condition, not inside a concatenation part)"
  | .repl .. => .error "replication (outside the v1 fragment)"
  | .reduce .. => .error "reduction in this position (outside the v1 fragment: allowed as a whole right-hand side, an operand or a condition, not inside a concatenation part)"
  | .resize .. | .signedResize .. => .error "width conversion (an operand is not as wide as its context at the default parameters, so slang inserted an implicit zero-extension or truncation; the v1 fragment needs every operand exactly as wide as its target: widen or narrow it explicitly)"
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

/-- The argument of a replication (WP-B2 gate 4c): a sized literal, or ONE access that is not a whole signal (the
window of an access knows its own width; a whole signal's is the declared one). -/
def notWhole (r : Except String (List Acc)) : Except String (List Acc) :=
  match r with
  | .ok [.whole _] => .error "replication of a whole signal (outside the v1 fragment: replicate a bit or a part select)"
  | r => r

def repArgRd? (ds : List DeclT) : PExpr → Except String (List Acc)
  | .concat [.lit _] => .ok []
  | .concat [e] => notWhole (rdsLeaf? ds e)
  | _ => .error "replication of a concatenation of several parts (outside the v1 fragment: replicate a sized literal, a bit select or a part select)"

/-- A replication `{c{a}}`: an affine count (parameters and genvars) over a literal or one access. -/
def repRd? (ds : List DeclT) (c a : PExpr) : Except String (List Acc) :=
  match affOf? c with
  | some _ => repArgRd? ds a
  | none => .error "replication count is not affine (outside the v1 fragment: dynamic or nonlinear)"

/-- A concatenation part of the word-level fragment: a literal, one access, or a replication. -/
def partRdW? (ds : List DeclT) (e : PExpr) : Except String (List Acc) :=
  match e with
  | .lit _ => .ok []
  | .repl c a => repRd? ds c a
  | _ => rdsLeaf? ds e

def partsRdW? (ds : List DeclT) : List PExpr → Except String (List Acc)
  | [] => .ok []
  | p :: ps =>
      match partRdW? ds p with
      | .error e => .error e
      | .ok a =>
          match partsRdW? ds ps with
          | .error e => .error e
          | .ok b => .ok (a ++ b)

def partsRd? (ds : List DeclT) : List PExpr → Except String (List Acc)
  | [] => .ok []
  | p :: ps =>
      match partRd? ds p with
      | .error e => .error e
      | .ok a =>
          match partsRd? ds ps with
          | .error e => .error e
          | .ok b => .ok (a ++ b)

/-- The binary operators of the fragment: the bitwise gates `& | ^`, logical `&&` `||` and `==` `!=`
(WP-G S2). -/
def binOk : SymBinOp → Bool
  | .m0 .and | .m0 .or | .m0 .xor | .land | .lor | .m0 .eq | .m0 .ne => true
  | _ => false

/-- The reads of an expression of the fragment, or the reason it is outside it.

WP-G S2: besides the gate trees of `& | ^` the fragment has `~` and `!`, the reductions, `&&` and `||`,
`==` and `!=`, and the conditional expression `c ? a : b` (reads in textual order: `c`, `a`, `b`). -/
def rdsOf? (ds : List DeclT) : PExpr → Except String (List Acc)
  | .lit _ => .ok []
  | .binary op l r =>
      if binOk op then
        match rdsOf? ds l with
        | .error e => .error e
        | .ok a =>
            match rdsOf? ds r with
            | .error e => .error e
            | .ok b => .ok (a ++ b)
      else .error s!"operator `{op.sym}` is outside the v1 fragment here (it has the bitwise gates `&`, `|`, `^`, the logical `&&`, `||` and `==`, `!=`; the word-level `+`, `-` and `*` are accepted only at the context-determined positions of a right-hand side (an `assign` or an `always_comb` leaf), not under `!`, a reduction, a comparison or a `?:` condition; so are the six comparisons and the run-time shifts `<<`, `>>`; `<<<`, `>>>`, a signed `>>`, `/`, `%` and `**` are word-level operators it does not have yet)"
  | .unary op a =>
      match op with
      | .m0 .bnot => rdsOf? ds a
      | .m0 .lnot => rdsOf? ds a
      | _ => .error "unary operator `-` or `+` (outside the v1 fragment: it has `~` and `!`)"
  | .ternary c t e =>
      match rdsOf? ds c with
      | .error m => .error m
      | .ok a =>
          match rdsOf? ds t with
          | .error m => .error m
          | .ok b =>
              match rdsOf? ds e with
              | .error m => .error m
              | .ok d => .ok (a ++ b ++ d)
  | .reduce _ a => rdsOf? ds a
  | .concat ps => partsRd? ds ps
  | e => rdsLeaf? ds e

/-! ### WP-B2: the word-level recognizer (`+`, `-`, `*`, implicit zero extension)

`rdsOfW?` reads the CONTEXT-determined positions of an `assign` right-hand side: the bitwise gates, `~`, `?:` arms
and (new) `+`, `-` and `*`, whose operands may carry the `Resize` marker slang puts around an operand narrower than
the context (`*` with one factor a signal access, `mulOk`). The SELF-determined positions (the operands of `!`, the
reductions, `&&`, `||`, `==`, `!=`, the condition of `?:`) are read by the old `rdsOf?`: they keep their v1 fragment,
so the whole S2 theory applies to them unchanged. `rdsOf?` itself is untouched (the `always_comb` chain uses it). -/

/-- The six comparison operators (WP-B2 gate 2b). -/
inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq

/-- The `BinOp` of a comparison. -/
def CmpOp.ex : CmpOp → BinOp
  | .eq => .eq
  | .ne => .ne
  | .lt => .lt
  | .le => .le
  | .gt => .gt
  | .ge => .ge

/-- The binary operators whose operands `rdsOfW?` reads itself: the bitwise gates, `+`, `-` and `*` (operands
context-determined at the operation's context) and the six comparisons (operands context-determined at the wider of
their own natural widths; the result is one bit). -/
def ctxOpW : SymBinOp → Bool
  | .m0 .and | .m0 .or | .m0 .xor | .m0 .add | .m0 .sub | .mul
  | .m0 .eq | .m0 .ne | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge => true
  | _ => false

/-- A factor of `*` that makes the product a run-time value: a signal access, bare or under the `Resize` marker.
`instExpr2` folds a product that `evalInt` can evaluate (a product of constants) and lowers `*` like `+` only when
that evaluation fails; it fails at every type on a signal access (`evalAt_sigOpd`), so the recognizer asks for one such
factor. -/
def sigOpd : PExpr → Bool
  | .ident _ | .bitSel (.ident _) _ | .partSel (.ident _) _ _ | .arrayElem .. | .arrayPart .. => true
  | .resize _ (.ident _) | .resize _ (.bitSel (.ident _) _) | .resize _ (.partSel (.ident _) _ _)
  | .resize _ (.arrayElem ..) | .resize _ (.arrayPart ..) => true
  | _ => false

/-- The extra condition of `*` (WP-B2): one factor is a signal access (`sigOpd`). Every other operator passes. -/
def mulOk (op : SymBinOp) (l r : PExpr) : Bool :=
  op != .mul || sigOpd l || sigOpd r

/-- The binary operators of one-bit results over self-determined operands (`&&`, `||`). -/
def selfOpW : SymBinOp → Bool
  | .land | .lor => true
  | _ => false

/-- The run-time shifts `<<` (over an unsigned or a signed left operand) and `>>` (over an unsigned one) (WP-B2 gate 3). -/
def shOpW : SymBinOp → Bool
  | .m0 (.shl _) | .m0 (.shr false) => true
  | _ => false

/-- The signedness flag of a shift operator (the flag `instDivOperand2` passes to its left operand). -/
def shSign : SymBinOp → Bool
  | .m0 (.shl s) => s
  | _ => false

/-- An operand of a shift (the left operand, or the amount): a signal access, a sized literal or an unsized constant.
`instExpr2` lowers both through `instDivOperand2`, whose default arm these are; an operation is refused. -/
def shOpdRd? (ds : List DeclT) : PExpr → Except String (List Acc)
  | .lit _ => .ok []
  | .int _ => .ok []
  | .ident n => rdsLeaf? ds (.ident n)
  | .bitSel b i => rdsLeaf? ds (.bitSel b i)
  | .partSel b m l => rdsLeaf? ds (.partSel b m l)
  | .arrayElem n is => rdsLeaf? ds (.arrayElem n is)
  | .arrayPart n is m a b => rdsLeaf? ds (.arrayPart n is m a b)
  | _ => .error "operand of a shift that is not a signal access, a sized literal or an unsized constant (outside the v1 fragment: `instExpr2` lowers a shift operand through a different instantiation than an operand of `+` or `&`, so only these are read; write the operand into a signal first)"

/-- The left operand of a shift of signedness `s`: as `shOpdRd?`, under the marker `instDivOperand2` sees through
without changing the signedness of the operand: the `Resize` marker of an unsigned shift, the `SignedResize` marker of a
signed one (`1 << s`: the unsized constant is a signed 32-bit integer). The other marker would flip the signedness the
operand is lowered at, and is refused. -/
def shLeftRd? (ds : List DeclT) (s : Bool) : PExpr → Except String (List Acc)
  | .resize _ e =>
      if s then .error "operand of a signed shift under a zero-extension marker (outside the v1 fragment: write the operand into a signal first)"
      else shOpdRd? ds e
  | .signedResize _ e =>
      if s then shOpdRd? ds e
      else .error "operand of an unsigned shift under a sign-extension marker (outside the v1 fragment: write the operand into a signal first)"
  | e => shOpdRd? ds e

/-- The AMOUNT of a shift (WP-B2 gate 4b): as `shOpdRd?`, or a bare genvar (`a << i` in a generate loop), a constant of
the instance that reads nothing. `instDivOperand2` lowers it at its own width, 32 bits (`divOperandWidth2 (.genvarRef _)`), to
the literal of its value. (A genvar under a conversion marker has its own lowering arm, a refusal of a negative value:
not read.) -/
def shAmtRd? (ds : List DeclT) : PExpr → Except String (List Acc)
  | .genvarRef _ => .ok []
  | .paramRef _ none => .ok []
  | e => shOpdRd? ds e

/-- The operand of a width conversion: ONE signal access (a sized literal is read before this is called). -/
def resizeRd? (ds : List DeclT) (e : PExpr) : Except String (List Acc) :=
  match e with
  | .ident _ | .bitSel .. | .partSel .. | .arrayElem .. | .arrayPart .. =>
      match leafRd? ds e with
      | .ok a => .ok [a]
      | .error m => .error m
  | _ => .error "width conversion of something other than a signal access or a sized literal"

/-- The reads of a context-determined expression of the word-level fragment, or the reason it is outside it. -/
def rdsOfW? (ds : List DeclT) : PExpr → Except String (List Acc)
  | .lit _ => .ok []
  | .binary op l r =>
      if ctxOpW op then
        if mulOk op l r then
          match rdsOfW? ds l with
          | .error e => .error e
          | .ok a =>
              match rdsOfW? ds r with
              | .error e => .error e
              | .ok b => .ok (a ++ b)
        else .error "a product neither of whose factors is a signal access (outside the v1 fragment: the elaboration folds a product of constants, so `*` is read with at least one factor a signal access, bare or zero-extended; write one factor into a signal first)"
      else if selfOpW op then
        match rdsOf? ds l with
        | .error e => .error e
        | .ok a =>
            match rdsOf? ds r with
            | .error e => .error e
            | .ok b => .ok (a ++ b)
      else if shOpW op then
        match shLeftRd? ds (shSign op) l with
        | .error e => .error e
        | .ok a =>
            match shAmtRd? ds r with
            | .error e => .error e
            | .ok b => .ok (a ++ b)
      else .error s!"operator `{op.sym}` is outside the v1 fragment (it has the bitwise gates `&`, `|`, `^`, the word-level `+`, `-` and `*`, the six comparisons, the run-time shifts `<<` and `>>` and the logical `&&`, `||`; `<<<`, `>>>`, a signed `>>`, `/`, `%` and `**` are word-level operators it does not have yet)"
  | .unary op a =>
      match op with
      | .m0 .bnot => rdsOfW? ds a
      | .m0 .lnot => rdsOf? ds a
      | _ => .error "unary operator `-` or `+` (outside the v1 fragment: it has `~` and `!`)"
  | .ternary c t e =>
      match rdsOf? ds c with
      | .error m => .error m
      | .ok a =>
          match rdsOfW? ds t with
          | .error m => .error m
          | .ok b =>
              match rdsOfW? ds e with
              | .error m => .error m
              | .ok d => .ok (a ++ b ++ d)
  | .reduce _ a => rdsOf? ds a
  | .concat ps => partsRdW? ds ps
  | .repl c a => repRd? ds c a
  | .resize _ e =>
      match e with
      | .lit _ => .ok []
      | .ident _ => resizeRd? ds e
      | .bitSel .. => resizeRd? ds e
      | .partSel .. => resizeRd? ds e
      | .arrayElem .. => resizeRd? ds e
      | .arrayPart .. => resizeRd? ds e
      | .binary .. => rdsOfW? ds e
      | .unary .. => rdsOfW? ds e
      | .ternary .. => rdsOfW? ds e
      | .reduce .. => rdsOfW? ds e
      | .int _ => rdsOfW? ds e
      | .concat _ => rdsOfW? ds e
      | _ => .error "width conversion of a nested conversion or a constant that is not an unsized integer (outside the v1 fragment: a conversion is read around one signal access, one sized literal, a concatenation, or an operation of the fragment)"
  | .int _ => .ok []
  | e => rdsLeaf? ds e

/-- An expression a width conversion may wrap besides a signal access or a sized literal: an operation of the
fragment or an unsized integer constant (WP-B2 gate 2b). -/
def _root_.LeanModels.Sv.PExpr.isOpW : PExpr → Bool
  | .binary .. => true
  | .unary .. => true
  | .ternary .. => true
  | .reduce .. => true
  | .int _ => true
  | .concat _ => true
  | _ => false

/-- The reads of a right-hand side (WP-B2 gate 2: the word-level fragment, the one reading of the assign sites
and of the leaves of an `always_comb` tree): an unbased unsized fill (`'0`) alone, or an expression of
`rdsOfW?`. -/
def rhsRds? (ds : List DeclT) (v : PExpr) : Except String (List Acc) :=
  match v with
  | .fill _ => .ok []
  | _ => rdsOfW? ds v

def tgtOf? (ds : List DeclT) : PLhs → Except String Acc
  | .ident n => .ok (.whole n)
  | .bitSel n i =>
      match affOf? i with
      | some a => bitAcc? ds n a
      | none => .error s!"non-affine genvar-index obligation: write to `{n}[…]` has a dynamic or nonlinear index, so the driven window cannot be determined"
  | .arrayElem n is => elemAcc? ds n is
  | .arrayPart n is mode hi lo => partAcc? ds n is mode hi lo
  | .partSel n msb lsb => partAcc? ds n [] .range msb lsb
  | .concat _ => .error "concatenation target (outside the v1 fragment)"

/-- No constant of the instance and no replication in a right-hand side, in ONE cheap traversal (`noConst_spec`): the
genvar amount of a shift (`cnames`) and a replication (`cnames`, `rcounts`) are the only sources. A traversal per leaf of
a `case` table is what `sbox_table` pays (about 2.5 heartbeat-thousands per leaf), so the check is ONE function, not
`cnames.isEmpty && rcounts.isEmpty`. -/
def noConst : PExpr → Bool
  | .binary op l r =>
      (match op, r with
       | .m0 (.shl _), .genvarRef _ => false
       | .m0 (.shr false), .genvarRef _ => false
       | .m0 (.shl _), .paramRef _ none => false
       | .m0 (.shr false), .paramRef _ none => false
       | _, _ => true) && noConst l && noConst r
  | .unary _ a => noConst a
  | .reduce _ a => noConst a
  | .ternary c t e => noConst c && noConst t && noConst e
  | .resize _ a => noConst a
  | .repl .. => false
  | .concat ps => ps.all fun p => match p with | .repl .. => false | _ => true
  | _ => true

theorem flatMap_nil_of_all {α β : Type} (f : α → List β) :
    ∀ ps : List α, (∀ p ∈ ps, f p = []) → ps.flatMap f = []
  | [], _ => rfl
  | p :: ps, h => by
      simp only [List.flatMap_cons, h p (by simp), List.nil_append]
      exact flatMap_nil_of_all f ps fun q hq => h q (by simp [hq])

theorem noConst_spec : ∀ v : PExpr, noConst v = true → v.cnames = [] ∧ v.rcounts = []
  | .binary op l r, h => by
      simp only [noConst, Bool.and_eq_true] at h
      obtain ⟨⟨h0, hl⟩, hr⟩ := h
      obtain ⟨hl1, hl2⟩ := noConst_spec l hl
      obtain ⟨hr1, hr2⟩ := noConst_spec r hr
      refine ⟨?_, by simp [PExpr.rcounts, hl2, hr2]⟩
      simp only [PExpr.cnames, hl1, hr1]
      split <;> first | rfl | (simp_all)
  | .unary _ a, h => by simpa only [noConst, PExpr.cnames, PExpr.rcounts] using noConst_spec a h
  | .reduce _ a, h => by simpa only [noConst, PExpr.cnames, PExpr.rcounts] using noConst_spec a h
  | .ternary c t e, h => by
      simp only [noConst, Bool.and_eq_true] at h
      obtain ⟨⟨hc, ht⟩, he⟩ := h
      obtain ⟨c1, c2⟩ := noConst_spec c hc
      obtain ⟨t1, t2⟩ := noConst_spec t ht
      obtain ⟨e1, e2⟩ := noConst_spec e he
      simp [PExpr.cnames, PExpr.rcounts, c1, c2, t1, t2, e1, e2]
  | .resize _ a, h => by simpa only [noConst, PExpr.cnames, PExpr.rcounts] using noConst_spec a h
  | .repl .., h => by simp [noConst] at h
  | .concat ps, h => by
      simp only [noConst, List.all_eq_true] at h
      have key : ∀ p ∈ ps, repNames p = [] ∧ repCount p = [] := by
        intro p hp
        have := h p hp
        cases p <;> first | exact ⟨rfl, rfl⟩ | (simp at this; done)
      exact ⟨flatMap_nil_of_all repNames ps fun p hp => (key p hp).1,
        flatMap_nil_of_all repCount ps fun p hp => (key p hp).2⟩
  | .lit _, _ | .fill _, _ | .ident _, _ | .bitSel .., _ | .partSel .., _ | .arrayElem .., _ | .arrayPart .., _
  | .paramRef .., _ | .genvarRef _, _ | .enumRef .., _ | .int _, _ | .sysCall .., _ | .cast .., _
  | .signedResize .., _ | .squash2 .., _ | .unsupported .., _ => by
      simp [PExpr.cnames, PExpr.rcounts]

/-- The site with the lists `cn`, `rc` given, a literal `[]` for each that is empty (see `forceSite`). -/
def forceC (pos : Nat) (tg : Acc) (rds : List Acc) (proc : PProcess) (cn : List String) (rc : List Aff) :
    Except String TSite :=
  match cn, rc with
  | [], [] => .ok ⟨pos, tg, rds, proc, [], [], []⟩
  | cn, [] => .ok ⟨pos, tg, rds, proc, [], cn, []⟩
  | [], rc => .ok ⟨pos, tg, rds, proc, [], [], rc⟩
  | cn, rc => .ok ⟨pos, tg, rds, proc, [], cn, rc⟩

theorem forceC_eq (pos : Nat) (tg : Acc) (rds : List Acc) (proc : PProcess) (cn : List String) (rc : List Aff) :
    forceC pos tg rds proc cn rc = .ok ⟨pos, tg, rds, proc, [], cn, rc⟩ := by
  unfold forceC
  split <;> simp_all

/-- A site of one right-hand side `v`, with its constants of the instance (`cnames`) and replication counts (`rcounts`)
FORCED to values at recognition time: `noConst` (one cheap Boolean traversal) first, `PExpr.consts` (ONE traversal for both lists) only for a right-hand side that names a constant or replicates:
the match is the head of what `PDesign.summary` evaluates, so the site the tactics see carries `[]` literally for a
leaf and for every design before gate 4b (instead of thunks that every obligation would have to unfold with `simp`: a
lemma name in the tactics' lists costs about 21 thousand heartbeats per `simp` call, so the lists do not name
`PExpr.rcounts`: WP-B2 gate 4c). A function of the nested `PExpr` costs a few heartbeats even on a leaf (`brecOn`), so a
256-site table of literals pays nothing here. Equal to the plain constructor: `forceSite_eq`. -/
def forceSite (pos : Nat) (tg : Acc) (rds : List Acc) (proc : PProcess) (v : PExpr) : Except String TSite :=
  match noConst v with
  | true => .ok ⟨pos, tg, rds, proc, [], [], []⟩
  | false =>
      match v.consts with
      | (cn, rc) => forceC pos tg rds proc cn rc

theorem forceSite_eq (pos : Nat) (tg : Acc) (rds : List Acc) (proc : PProcess) (v : PExpr) :
    forceSite pos tg rds proc v = .ok ⟨pos, tg, rds, proc, [], v.cnames, v.rcounts⟩ := by
  unfold forceSite
  cases h : noConst v
  · simp only [consts_eq, forceC_eq]
  · obtain ⟨h1, h2⟩ := noConst_spec v h
    simp [h1, h2]

def siteOf? (ds : List DeclT) (pos : Nat) : PProcess → Except String TSite
  | .assign t v =>
      match rhsRds? ds v with
      | .ok rds => forceSite pos (.whole t) rds (.assign t v) v
      | .error e => .error e
  | .assignL l v =>
      match tgtOf? ds l with
      | .error e => .error e
      | .ok tg =>
          match rhsRds? ds v with
          | .ok rds => forceSite pos tg rds (.assignL l v) v
          | .error e => .error e
  | .alwaysFF .. | .alwaysPlain .. | .alwaysComb .. | .alwaysFFR .. =>
      .error "procedural process (`always`): outside the combinational-assign fragment"
  | .unsupported k _ => .error s!"unsupported process `{k}`"

/-- The recognizer of a process list, GENERIC in the recognizer `so` of one process (`siteOf?`; the
proc-aware layer, `CombProcSummary.lean`, instantiates it with `siteOfP?`). -/
def sitesOfG (so : List DeclT → Nat → PProcess → Except String TSite) (ds : List DeclT) (tag : String) : Nat → List PProcess → Except String (List TSite)
  | _, [] => .ok []
  | pos, p :: ps =>
      match so ds pos p with
      | .error e => .error s!"site `{tag}#{pos}`: {e}"
      | .ok st =>
          match sitesOfG so ds tag (pos + 1) ps with
          | .error e => .error e
          | .ok sts => .ok (st :: sts)

def sitesOf? (ds : List DeclT) (tag : String) : Nat → List PProcess → Except String (List TSite) :=
  sitesOfG siteOf? ds tag

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

/-- An item of an outer loop's body at position `pos` (generic in the process recognizer `so`). -/
def itemOfG (so : List DeclT → Nat → PProcess → Except String TSite) (ds : List DeclT) (tag : String) (pos : Nat) : GenItem → Except String TItem
  | .process p =>
      match so ds pos p with
      | .error e => .error s!"site `{tag}#{pos}`: {e}"
      | .ok st => .ok (.site st)
  | .genFor label g initE bound step rc body =>
      match hdrOf? label g initE bound step with
      | .error e => .error e
      | .ok h =>
          match procsOf? body with
          | none => .error "an inner generate loop holds a nested generate, a conditional generate or an instance (the v1 fragment nests generate loops two deep)"
          | some ps =>
              match sitesOfG so ds h.name 0 ps with
              | .error e => .error e
              | .ok sts => .ok (.loop ⟨h, rc, sts⟩)
  | .genIf .. =>
      .error "conditional generate inside a generate loop: GuardEval obligation (the selected arm depends on reached genvar values)"
  | .inst _ => .error "module instance inside a generate loop (outside the v1 fragment)"
  | .unsupported k _ => .error s!"unsupported generate item `{k}`"

def itemOf? (ds : List DeclT) (tag : String) (pos : Nat) : GenItem → Except String TItem :=
  itemOfG siteOf? ds tag pos

def itemsOfG (so : List DeclT → Nat → PProcess → Except String TSite) (ds : List DeclT) (tag : String) : Nat → List GenItem → Except String (List TItem)
  | _, [] => .ok []
  | pos, it :: rest =>
      match itemOfG so ds tag pos it with
      | .error e => .error e
      | .ok x =>
          match itemsOfG so ds tag (pos + 1) rest with
          | .error e => .error e
          | .ok xs => .ok (x :: xs)

def itemsOf? (ds : List DeclT) (tag : String) : Nat → List GenItem → Except String (List TItem) :=
  itemsOfG siteOf? ds tag

def famOfG (so : List DeclT → Nat → PProcess → Except String TSite) (ds : List DeclT) : GenItem → Except String TFam
  | .genFor label g initE bound step rc body =>
      match hdrOf? label g initE bound step with
      | .error e => .error e
      | .ok h =>
          match itemsOfG so ds h.name 0 body with
          | .error e => .error e
          | .ok its => .ok ⟨h, rc, its⟩
  | .genIf .. => .error "conditional generate (outside the v1 fragment)"
  | .inst _ => .error "module instance (outside the v1 fragment)"
  | .process _ => .error "process item in the generate list"
  | .unsupported k _ => .error s!"unsupported generate item `{k}`"

def famOf? (ds : List DeclT) : GenItem → Except String TFam :=
  famOfG siteOf? ds

def famsOfG (so : List DeclT → Nat → PProcess → Except String TSite) (ds : List DeclT) : List GenItem → Except String (List TFam)
  | [] => .ok []
  | it :: rest =>
      match famOfG so ds it with
      | .error e => .error e
      | .ok f =>
          match famsOfG so ds rest with
          | .error e => .error e
          | .ok fs => .ok (f :: fs)

def famsOf? (ds : List DeclT) : List GenItem → Except String (List TFam) :=
  famsOfG siteOf? ds

/-! ## Local parameters

A `localparam L = <constant expression of the parameters>` enters the view as one more NAMED CONSTANT:
`Summary.params` lists the module parameters and then the localparams (the names an `Aff` may
mention), and `Summary.lps` keeps each localparam's definition as a `CE`, a tiny constant-expression
language (integer literals, references to parameters and EARLIER localparams, `+`, `-`, `*` by a
literal, `/` and `%` by a positive literal, `$clog2`). `Summary.val s args` is the valuation of all the constants:
the parameters zipped with the arguments, then each localparam evaluated over what precedes it.

`$clog2 (e)` is not linear: downstream (widths, loop bounds, the obligations) its value is an opaque atom, `↑(clog2 n)`
for the natural number `n` of its argument, which `omega` reads as a non-negative unknown. A fact about it that an
obligation needs (`2 ^ NI ≥ …`) is the player's to supply.

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
  /-- `$clog2 (a)`. -/
  | clog2 (a : CE)
  /-- `$clog2 (a)` through a 32-bit signed `int` localparam target. -/
  | clog2S (a : CE)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The value of a definition, with `evalInt`'s own operations (`/` and `%` truncate toward zero; `$clog2` is
`LeanModels.Sv.clog2` of the argument's `toNat`, where `evalInt` refuses a negative argument). -/
def CE.eval (σ : String → Int) : CE → Int
  | .lit v => v
  | .ref n => σ n
  | .add a b => a.eval σ + b.eval σ
  | .sub a b => a.eval σ - b.eval σ
  | .mul a b => a.eval σ * b.eval σ
  | .divK a k => (a.eval σ).tdiv k
  | .modK a k => (a.eval σ).tmod k
  | .clog2 a => (LeanModels.Sv.clog2 (a.eval σ).toNat : Int)
  | .clog2S a => canonInt 32 true (LeanModels.Sv.clog2 (a.eval σ).toNat : Int)

/-- `$clog2 n ≤ n`: what the generate-fuel obligation (`auto_k`) of a loop bounded by a `$clog2` localparam needs. -/
theorem clog2_le (n : Nat) : LeanModels.Sv.clog2 n ≤ n := by
  unfold LeanModels.Sv.clog2
  split
  · omega
  · have := (Nat.log2_lt (n := n - 1) (k := n - 1) (by omega)).mpr (Nat.lt_two_pow_self)
    omega

/-- `n ≤ 2 ^ $clog2 n`, the defining property of the ceiling logarithm. -/
theorem le_two_pow_clog2 (n : Nat) : n ≤ 2 ^ LeanModels.Sv.clog2 n := by
  unfold LeanModels.Sv.clog2
  split
  · simp only [Nat.pow_zero]; omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-- The bindings of the localparams, each evaluated over the bindings before it (latest first). -/
def lpEnv : List (String × CE) → List (String × Int) → List (String × Int)
  | [], acc => acc
  | (n, c) :: rest, acc => lpEnv rest ((n, c.eval (σL acc)) :: acc)

def CE.isLit : CE → Bool
  | .lit _ => true
  | _ => false

/-- A `$clog2` occurs in the definition (for the refusal message of a 2-state `int` localparam). -/
def CE.hasClog2 : CE → Bool
  | .clog2 _ | .clog2S _ => true
  | .add a b | .sub a b | .mul a b => a.hasClog2 || b.hasClog2
  | .divK a _ | .modK a _ => a.hasClog2
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
      .error s!"localparam `{nm}`: operator `{op.sym}` is outside the v1 fragment (a localparam may use + - *, / % by an integer literal, and `$clog2`)"

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
      | .ok c =>
          if c.hasClog2 then
            -- `$clog2` is an integer constant function.  `int` and
            -- `integer` are both 32-bit signed in the summary, so retain
            -- the same opaque `CE.clog2` atom; the defaults gate separately
            -- checks the exact 32-bit elaboration point.
            match c with
            | .clog2 a => .ok (.clog2S a)
            | _ => .ok c
          else
            .error s!"localparam `{nm}`: a 2-state `int` localparam initialised by `/` or `%` is squashed to 2 states and wraps at 2^31 in the elaborated design (its closed arithmetic form would be false for huge parameters); declare it `localparam integer {nm} = …;` (outside the v1 fragment)"
  | .sysCall .clog2 a =>
      match ceOf? nm scope a with
      | .error e => .error e
      | .ok c => .ok (.clog2 c)
  | .sysCall .. =>
      .error s!"localparam `{nm}`: a system call other than `$clog2` is outside the v1 fragment (a localparam may use + - *, / % by an integer literal, and `$clog2`)"
  | _ =>
      .error s!"localparam `{nm}`: the initializer is outside the v1 fragment (a localparam may use integer literals, parameters, earlier localparams, + - *, / % by an integer literal, and `$clog2`)"

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

/-- The summary of a design, generic in the process recognizer `so` (`PDesign.summary` is `siteOf?`, the
proc-aware `PDesign.summaryP` is `siteOfP?`). -/
def _root_.LeanModels.Sv.PDesign.summaryG (so : List DeclT → Nat → PProcess → Except String TSite) (d : PDesign) : Except String Summary :=
  match lpsOf? (d.params.map (·.name)) d.localParams with
  | .error e => .error e
  | .ok lps =>
      if !d.enums.isEmpty then .error "enums are outside the v1 fragment"
      else if !d.others.isEmpty then .error "out-of-tier module members are present"
      else
        match declsOf? d.decls with
        | .error e => .error e
        | .ok ds =>
            match sitesOfG so ds "plain" 0 d.processes with
            | .error e => .error e
            | .ok sts =>
                match famsOfG so ds d.generates with
                | .error e => .error e
                | .ok fs =>
                    .ok { params := d.params.map (·.name) ++ lps.map Prod.fst, decls := ds,
                          statics := sts, fams := fs, lps := lps }

def _root_.LeanModels.Sv.PDesign.summary (d : PDesign) : Except String Summary :=
  d.summaryG siteOf?

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

/-- Does some site replicate (WP-B2 gate 4c)? Decided by the tactics on the COMPILED summary, to pass the replication
vocabulary to `simp` for that design only: naming it in the tactics' own lists costs about 21 units of heartbeats per
`simp` call on every proof (measured), which the designs without a replication would pay for nothing. -/
def hasRepl : Bool := s.lsites.any fun ls => !ls.site.rcounts.isEmpty

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
  /-- The further windows (and their targets) of a body that writes several: `TSite.more` at the valuation. -/
  more : List (Win × Lhs2)

/-- All the windows of a footprint: the first, then the further ones. -/
def SiteInst.wins (si : SiteInst) : List Win := si.win :: si.more.map Prod.fst

/-- The footprint of a located site at a valuation of its loops. -/
def LSite.inst (ls : LSite) (σ : String → Int) (dw : String → Nat) : SiteInst :=
  { id := ls.id σ, win := ls.site.tgt.win σ dw, tgt := ls.site.tgt.lhs σ,
    rd := ls.site.rds.map (Acc.rd σ), more := ls.site.more.map fun a => (a.win σ dw, a.lhs σ) }

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
  split at h
  · cases h
  · cases hi : pd.init with
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
      (∀ p ∈ dims, ∀ n ∈ p.2.1.names ++ p.2.2.names, env.intVal? n = some (σ n)) →
      evalDims env (dims.map (·.1)) = .ok (dims.map fun p => (p.2.1.eval σ, p.2.2.eval σ))
  | [], _, _ => by simp
  | p :: rest, ha, hg => by
      obtain ⟨hm, hl⟩ := ha p (List.mem_cons_self ..)
      have hm' : ∀ n ∈ p.2.1.names, env.intVal? n = some (σ n) :=
        fun n hn => hg p (List.mem_cons_self ..) n (List.mem_append_left _ hn)
      have hl' : ∀ n ∈ p.2.2.names, env.intVal? n = some (σ n) :=
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
      (∀ p ∈ dims, ∀ n ∈ p.2.1.names ++ p.2.2.names, env.intVal? n = some (σ n)) →
      (PType.packed (dims.map (·.1)) r).width env = .ok (dimsW σ dims)
  | [], _, _ => by simp [dimsW]
  | p :: rest, ha, hg => by
      obtain ⟨hm, hl⟩ := ha p (List.mem_cons_self ..)
      have hm' : ∀ n ∈ p.2.1.names, env.intVal? n = some (σ n) :=
        fun n hn => hg p (List.mem_cons_self ..) n (List.mem_append_left _ hn)
      have hl' : ∀ n ∈ p.2.2.names, env.intVal? n = some (σ n) :=
        fun n hn => hg p (List.mem_cons_self ..) n (List.mem_append_right _ hn)
      obtain ⟨-, hem⟩ := affOf?_sound _ _ hm hm'
      obtain ⟨-, hel⟩ := affOf?_sound _ _ hl hl'
      have ih := width_dims r rest (fun q hq => ha q (List.mem_cons_of_mem _ hq))
        (fun q hq => hg q (List.mem_cons_of_mem _ hq))
      rw [List.map_cons, PType.width_packed_cons, ih]
      simp [PDim.width, hem, hel, dimsW, Gen2.except_ok_bind]

theorem dt_agree {env : IEnv} {σ : String → Int} {dt : DeclT}
    (hag : ∀ n ∈ dt.affNames, env.intVal? n = some (σ n)) :
    ∀ p ∈ dt.dims, ∀ n ∈ p.2.1.names ++ p.2.2.names, env.intVal? n = some (σ n) := by
  intro p hp n hn
  apply hag n
  simp only [DeclT.affNames, List.mem_flatMap]
  exact ⟨p, hp, hn⟩

/-- `dimsWidth` of a declaration, computed. -/
theorem width_decl {env : IEnv} {σ : String → Int} {pd : PDecl} {dt : DeclT}
    (hd : declOf? pd = .ok dt)
    (hag : ∀ n ∈ dt.affNames, env.intVal? n = some (σ n)) :
    pd.type.width env = .ok (dt.width σ) := by
  obtain ⟨-, -, -, -, ⟨r, hr⟩, -, hdim, -, -⟩ := declOf?_spec hd
  rw [hr]
  exact width_dims r dt.dims hdim (dt_agree hag)

theorem elemWidth_decl {env : IEnv} {σ : String → Int} {pd : PDecl} {dt : DeclT}
    (hd : declOf? pd = .ok dt)
    (hag : ∀ n ∈ dt.affNames, env.intVal? n = some (σ n)) :
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
      ∀ (env : IEnv), (∀ dt ∈ sd, ∀ n ∈ dt.affNames, env.intVal? n = some (σ n)) →
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
      have hun : pd.unpackedDims = [] := by
        have hd' := hd
        unfold declOf? at hd'
        split at hd'
        · simp at hd'
        · simp_all
      have hdecl : instDecl env pd = .ok (dt.toDecl σ) := by
        simp [instDecl, hw, hun, hinit, DeclT.toDecl, hn, hi, ho, hsg, hts]
      simp only [buildDecls, hdecl, Res.ok_bind]
      have : ({ name := pd.name, width := dt.width σ, isInput := pd.isInput, isOutput := pd.isOutput } : Decl)
          = dt.toDecl σ := by simp [DeclT.toDecl, hn, hi, ho]
      simp only [DeclT.toDecl] at hrest ⊢
      rw [hrest]
      simp [Res.ok_bind, hn]

theorem buildElems_summary {σ : String → Int} :
    ∀ (ds : List PDecl) (sd : List DeclT), declsOf? ds = .ok sd →
      ∀ (env : IEnv), (∀ dt ∈ sd, ∀ n ∈ dt.affNames, env.intVal? n = some (σ n)) →
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

theorem dimTableStep_intVal (env : IEnv) (pd : PDecl) (n : String) :
    (dimTableStep env pd).intVal? n = env.intVal? n := by
  unfold dimTableStep
  split <;> rfl

theorem dimTable_summary {σ : String → Int} :
    ∀ (ds : List PDecl) (sd : List DeclT), declsOf? ds = .ok sd →
      ∀ (env : IEnv), (∀ dt ∈ sd, ∀ n ∈ dt.affNames, env.intVal? n = some (σ n)) →
        ∀ n, (dimTable env ds).lookup n = (sd.find? (fun dt => dt.name == n)).map (DeclT.vals σ)
  | [], sd, h, env, _, n => by
      simp [declsOf?] at h; subst h; simp [dimTable]
  | pd :: rest, sd, h, env, hag, n => by
      obtain ⟨dt, sd', hd, hr, rfl⟩ := declsOf?_cons h
      obtain ⟨hn, -, -, -, ⟨r, hr'⟩, -, hdim, -, -⟩ := declOf?_spec hd
      have hrest := dimTable_summary rest sd' hr (dimTableStep env pd)
        (fun dt' hdt' n' hn' => by
          rw [dimTableStep_intVal]; exact hag dt' (by simp [hdt']) n' hn') n
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

/-! `$clog2` has the same symbolic constant-expression class in a 32-bit
signed `int` localparam as in `integer`. -/
private def guardInt32Ty : PType := .packed [⟨.int 31, .int 0⟩] (some 32)
private def guardIntClog2 : PLocalParam :=
  { name := "L", expr := .squash2 32 (.sysCall .clog2 (.paramRef "N" none)), type? := some guardInt32Ty }
#guard (match lpOf? ["N"] guardIntClog2 with
  | .ok (.clog2S (.ref "N")) => true
  | _ => false)
#guard (match bindLocal { vals := [("N", 16)], int32 := true } guardIntClog2 with
  | .ok e => e.nvals.lookup "L" == some (4, 32, true)
  | .error _ => false)
#guard (match bindLocal { vals := [("N", 1)], int32 := true } guardIntClog2 with
  | .ok e => e.nvals.lookup "L" == some (0, 32, true)
  | .error _ => false)

end CombView
end LeanModels.Sv
