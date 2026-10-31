import Lean
import LeanModels.Sv.CombViewArith

/-!
# `sv_cover`, the 2-D rule: solved witnesses and a case chain (WP-P4)

A coverage goal of `sv_equations` says that every cell a read observes is written by some assign:

    ∀ (i : Int), 0 ≤ i → i < ↑N →
      (W₁ ∨ ∃ a, bounds ∧ ∃ b, bounds ∧ cell(a, b) ≤ X ∧ X < cell(a, b) + 1 ∨ …) ∧ (…) ∧ …

with `X = rmN W R C` (possibly `+ k`, the part select `s[r][c₀ +: n]`) and, per writer, a window
`rmN W r c₀ ≤ X ∧ X < rmN W r c₀ + wd` whose row `r` and column `c₀` are affine in the `∃`-variables
(generate loops), or a plain multi-bit window with no variable (a packed assign), or a 1-D window
(`A ≤ max X 0 ∧ …`, what `Int.toNat` becomes under `simp`).

The old search (`svCover`) tried constants and `x ± 1` for every variable and ran out of budget on
these goals. The writer of a cell is not a guess: the variables are the solution of the affine
equations `r(a) = R`, `c₀(b) = C`. The rule therefore

1. solves each `∃`-variable from the equation of the read's row or column in which it is the only
   unknown (`a := (R - r₀).toNat`, `r₀` the row with the variable set to `0`), substituting solved
   variables into the remaining equations (a 1-D window: from its `A ≤ B` conjunct);
2. states the writer's condition at the solved witnesses as a linear proposition `L`: the bounds, and
   for a window `r = R ∧ 0 ≤ c₀ ∧ 0 ≤ C ∧ c₀ ≤ C + e ∧ C + e < c₀ + wd` (the premises of the single
   sufficiency lemma `rmN_win_suff`, which is all the arithmetic of `rmN` the rule needs);
3. walks the disjunction: `Classical.em L`, `L` gives the disjunct (the proof is built from the
   components of `L`, no tactic runs), `¬L` goes to the next disjunct; the LAST disjunct is proved by
   `omega` from the negations of the others and the hypotheses;
4. closes a conjunct that already occurred in the goal by the proof of its first occurrence.

`L` is only sufficient (the lemma has no converse), but the witnesses are the unique solution of the
read's equations, so `omega` closes the last disjunct exactly when the cell is covered. A shape the
rule does not read (a non-`Nat` binder, an equation with two unknowns, a nonlinear index) makes it
fail with an ordinary exception and `sv_cover` runs its old search; a goal the rule reads and cannot
prove is reported with the read and the conditions it needs. -/

namespace LeanModels.Sv
namespace CombCover

open CombView Lean Meta Elab Tactic

/-- **The one arithmetic fact of the rule**: a write window `[rmN W r c₀, … + wd)` contains the cell
`rmN W R C + e` of the same row-major array when the rows agree and the column is in `[c₀, c₀ + wd)`.
Sufficiency only; the premises are what the rule states about the solved witnesses. -/
theorem rmN_win_suff {W r c0 R C : Int} {e wd : Nat} (hr : r = R) (hc0 : 0 ≤ c0) (hC : 0 ≤ C)
    (h1 : c0 ≤ C + (e : Int)) (h2 : C + (e : Int) < c0 + (wd : Int)) :
    rmN W r c0 ≤ rmN W R C + e ∧ rmN W R C + e < rmN W r c0 + wd := by
  subst hr
  unfold rmN
  constructor <;> omega

/-! ## Reading a disjunct -/

/-- The parts of a write window `rmN W r c0 ≤ X ∧ X < rmN W r c0 + wd`, `X = rmN W R C (+ e)`. -/
structure WinParts where
  W : Lean.Expr
  r : Lean.Expr
  c0 : Lean.Expr
  R : Lean.Expr
  C : Lean.Expr
  e : Lean.Expr
  wd : Lean.Expr

private def isRmN (x : Lean.Expr) : Bool := x.isAppOfArity ``LeanModels.Sv.CombView.rmN 3

/-- `a ≤ b` / `a < b` over any type: the two sides. -/
private def cmpSides? (rel : Name) (x : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if x.isAppOfArity rel 4 then some (x.getArg! 2, x.getArg! 3) else none

/-- `rmN W R C` or `rmN W R C + e`: the read position. -/
private def readPos? (x : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr × Option Lean.Expr) :=
  if isRmN x then some (x.getArg! 0, x.getArg! 1, x.getArg! 2, none)
  else if x.isAppOfArity ``HAdd.hAdd 6 && isRmN (x.getArg! 4) then
    let y := x.getArg! 4
    some (y.getArg! 0, y.getArg! 1, y.getArg! 2, some (x.getArg! 5))
  else none

/-- Recognize the node `P ∧ Q` of a write window. -/
def matchWin (n : Lean.Expr) : Option WinParts := do
  guard (n.isAppOfArity ``And 2)
  let (lo, x) ← cmpSides? ``LE.le (n.appFn!.appArg!)
  let (x', hi) ← cmpSides? ``LT.lt (n.appArg!)
  guard (isRmN lo)
  guard (x == x')
  guard (hi.isAppOfArity ``HAdd.hAdd 6)
  guard (hi.getArg! 4 == lo)
  let (W', R, C, e?) ← readPos? x
  guard (W' == lo.getArg! 0)
  let nat0 := mkNatLit 0
  pure { W := W', r := lo.getArg! 1, c0 := lo.getArg! 2, R := R, C := C, e := e?.getD nat0,
         wd := hi.getArg! 5 }

/-- The five premises of `rmN_win_suff` for the window, as `Int` propositions, each with a proof when
it is `0 ≤ ↑n` (kept out of the condition `L`: it costs `omega` a case split and never discriminates). -/
private def winPremises (p : WinParts) : MetaM (Array (Lean.Expr × Option Lean.Expr)) := do
  let intTy := mkConst ``Int
  let zero ← mkAppOptM ``OfNat.ofNat #[intTy, mkRawNatLit 0, none]
  let eI ← mkAppOptM ``Nat.cast #[intTy, none, p.e]
  let wdI ← mkAppOptM ``Nat.cast #[intTy, none, p.wd]
  let ce ← mkAppM ``HAdd.hAdd #[p.C, eI]
  let nonneg (x : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
    let pr ← mkAppM ``LE.le #[zero, x]
    if x.isAppOfArity ``Nat.cast 3 then return (pr, some (← mkAppM ``Int.natCast_nonneg #[x.getArg! 2]))
    else return (pr, none)
  pure #[(← mkEq p.r p.R, none), ← nonneg p.c0, ← nonneg p.C,
         (← mkAppM ``LE.le #[p.c0, ce], none),
         (← mkAppM ``LT.lt #[ce, ← mkAppM ``HAdd.hAdd #[p.c0, wdI]], none)]

/-- `x` is the numeral `0` (as an `Int` or `Nat` literal or the cast of one). -/
private def isZero (x : Lean.Expr) : Bool :=
  x.nat? == some 0 || x.int? == some 0 || (x.isAppOfArity ``Nat.cast 3 && (x.getArg! 2).nat? == some 0)

/-- Remove the `+ 0`, `- 0` and `↑numeral` the substitution leaves (for readable witnesses and
messages; never applied to a term whose type a lemma fixes). -/
private def tidy (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun x => do
    if x.isAppOfArity ``HSub.hSub 6 && isZero (x.getArg! 5) then return .done (x.getArg! 4)
    else if x.isAppOfArity ``HAdd.hAdd 6 && isZero (x.getArg! 5) then return .done (x.getArg! 4)
    else if x.isAppOfArity ``HAdd.hAdd 6 && isZero (x.getArg! 4) then return .done (x.getArg! 5)
    else if x.isAppOfArity ``Nat.cast 3 && (x.getArg! 0).isConstOf ``Int then
      match (x.getArg! 2).nat? with
      | some n => return .done (mkIntLit n)
      | none => return .continue
    else return .continue)

/-! ## Solving the witnesses -/

/-- The coefficient of the variable `v` in the linear `Int`/`Nat` expression `x` (`none`: not linear in `v`). -/
partial def coeff (v : FVarId) (x : Lean.Expr) : MetaM (Option Int) := do
  if !x.containsFVar v then return some 0
  if x.isFVar then return (if x.fvarId! == v then some 1 else none)
  let args := x.getAppArgs
  match x.getAppFn with
  | .const n _ =>
    if n == ``Nat.cast && args.size == 3 then coeff v args[2]!
    else if (n == ``HAdd.hAdd || n == ``HSub.hSub) && args.size == 6 then
      let isSub := n == ``HSub.hSub
      if isSub && (← whnfR args[0]!).isConstOf ``Nat then return none
      match ← coeff v args[4]!, ← coeff v args[5]! with
      | some a, some b => return some (if isSub then a - b else a + b)
      | _, _ => return none
    else if n == ``HMul.hMul && args.size == 6 then
      if !args[4]!.containsFVar v then
        match ← getIntValue? args[4]!, ← coeff v args[5]! with
        | some k, some b => return some (k * b)
        | _, _ => return none
      else if !args[5]!.containsFVar v then
        match ← coeff v args[4]!, ← getIntValue? args[5]! with
        | some a, some k => return some (a * k)
        | _, _ => return none
      else return none
    else if n == ``Neg.neg && args.size == 3 then
      match ← coeff v args[2]! with
      | some a => return some (-a)
      | none => return none
    else return none
  | _ => return none

/-- The witness (a `Nat` expression) for the equation `lhs = T`, `lhs` linear in `v`, `T` free of `v`:
`(T - lhs₀) / a`, `lhs₀` the left side with `v` set to `0` and `a` the coefficient (the division is exact
exactly when the equation has a solution; the condition `lhs(w) = T` that the rule states keeps it honest). -/
private def witness (v : FVarId) (lhs T : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let some a ← coeff v lhs | return none
  if a == 0 then return none
  let rest ← tidy (lhs.replaceFVar (mkFVar v) (mkNatLit 0))
  let ty ← whnfR (← inferType lhs)
  if ty.isConstOf ``Int then
    let q ← if a > 0 then mkAppM ``HSub.hSub #[T, rest] else mkAppM ``HSub.hSub #[rest, T]
    let q ← if a == 1 || a == -1 then pure q else mkAppM ``HDiv.hDiv #[q, mkIntLit a.natAbs]
    return some (← mkAppM ``Int.toNat #[q])
  else if ty.isConstOf ``Nat && a == 1 then
    return some (← mkAppM ``HSub.hSub #[T, rest])
  else return none

/-- Solve the unknowns from the equations `lhs = T`: repeatedly take an equation with exactly one
unknown (unit coefficient), solve it, substitute. `none` when some unknown stays unsolved. -/
private def solveAll (unk : Array FVarId) (eqs : Array (Lean.Expr × Lean.Expr)) :
    MetaM (Option (Array Lean.Expr)) := do
  let mut sol : Array (Option Lean.Expr) := unk.map fun _ => none
  let mut eqs := eqs
  let mut progress := true
  while progress do
    progress := false
    for i in [0:unk.size] do
      if sol[i]!.isSome then continue
      -- an equation in which `unk[i]` is the only unsolved unknown
      let mut pick : Option Nat := none
      for j in [0:eqs.size] do
        let (lhs, T) := eqs[j]!
        if pick.isSome then break
        let some a ← coeff unk[i]! lhs | continue
        if a == 0 then continue
        let mut only := true
        for k in [0:unk.size] do
          if k != i && sol[k]!.isNone && (lhs.containsFVar unk[k]! || T.containsFVar unk[k]!) then only := false
        if only && !T.containsFVar unk[i]! then pick := some j
      if let some j := pick then
        let (lhs, T) := eqs[j]!
        if let some w ← witness unk[i]! lhs T then
          sol := sol.set! i (some w)
          eqs := (eqs.eraseIdxIfInBounds j).map fun (l, t) => (l.replaceFVar (mkFVar unk[i]!) w, t.replaceFVar (mkFVar unk[i]!) w)
          progress := true
  if sol.any Option.isNone then return none
  return some (sol.map Option.get!)

/-! ## The plan of one disjunct -/

private inductive Item where
  | wit (x : FVarId)
  | atom (p : Lean.Expr)
  | win (n : Lean.Expr)

/-- Walk the `∃ … ∧ …` spine of a disjunct with its `Nat` binders as local variables. -/
private partial def spine {α : Type} (d : Lean.Expr) (items : Array Item)
    (k : Array Item → MetaM α) : MetaM α := do
  if d.isAppOfArity ``Exists 2 then
    unless (← whnfR d.appFn!.appArg!).isConstOf ``Nat do
      throwError "sv_cover: a binder that is not a Nat"
    let .lam n t b bi := d.appArg! | throwError "sv_cover: a quantifier that is not a lambda"
    withLocalDecl n bi t fun x => spine (b.instantiate1 x) (items.push (.wit x.fvarId!)) k
  else if d.isAppOfArity ``And 2 then
    if (matchWin d).isSome then k (items.push (.win d))
    else spine d.appArg! (items.push (.atom d.appFn!.appArg!)) k
  else k (items.push (.atom d))

/-- The witnesses of one disjunct and the components of its linear condition `L`. -/
structure Plan where
  ws : Array Lean.Expr
  /-- the components of the condition: a proposition and, when it needs no search, its proof -/
  slots : Array (Lean.Expr × Option Lean.Expr)

/-- The components that make up `L`. -/
def Plan.inL (p : Plan) : Array Lean.Expr := p.slots.filterMap fun (c, pf) => if pf.isNone then some c else none

/-- All the proofs the disjunct needs, given the projections of `L`. -/
def Plan.fullHs (p : Plan) (pr : Array Lean.Expr) : Array Lean.Expr := Id.run do
  let mut out := #[]
  let mut i := 0
  for (_, pf) in p.slots do
    match pf with
    | some x => out := out.push x
    | none => out := out.push pr[i]!; i := i + 1
  pure out

private def planOf (d : Lean.Expr) : MetaM Plan :=
  spine d #[] fun items => do
    let unk := items.filterMap fun | .wit x => some x | _ => none
    let hasWin := items.any fun | .win _ => true | _ => false
    -- the equations of the read
    let mut eqs : Array (Lean.Expr × Lean.Expr) := #[]
    for it in items.reverse do
      match it with
      | .win n =>
        let some p := matchWin n | pure ()
        eqs := eqs.push (p.r, p.R)
        if (← getNatValue? p.wd) == some 1 then
          let eI ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, p.e]
          eqs := eqs.push (p.c0, ← mkAppM ``HAdd.hAdd #[p.C, eI])
      | .atom a =>
        if !hasWin then
          if let some (l, r) := cmpSides? ``LE.le a then
            if unk.any (l.containsFVar ·) && !unk.any (r.containsFVar ·) then eqs := eqs.push (l, r)
            else if unk.any (r.containsFVar ·) && !unk.any (l.containsFVar ·) then eqs := eqs.push (r, l)
      | .wit _ => pure ()
    let some ws ← solveAll unk eqs | throwError "sv_cover: cannot solve the witnesses of a disjunct"
    let fv := unk.map mkFVar
    let mut comps : Array (Lean.Expr × Option Lean.Expr) := #[]
    for it in items do
      match it with
      | .wit _ => pure ()
      | .atom a => comps := comps.push (a.replaceFVars fv ws, none)
      | .win n =>
        let some p := matchWin n | throwError "sv_cover: internal error (window)"
        let sub (x : Lean.Expr) := x.replaceFVars fv ws
        let p' : WinParts := { W := sub p.W, r := sub p.r, c0 := sub p.c0, R := sub p.R, C := sub p.C,
                               e := sub p.e, wd := sub p.wd }
        comps := comps ++ (← winPremises p')
    pure { ws := ws, slots := comps }

/-- `c₁ ∧ (c₂ ∧ … cₙ)`. -/
private def mkAndAll (cs : Array Lean.Expr) : Lean.Expr :=
  cs.foldr (init := mkConst ``True) fun c acc => if acc.isConstOf ``True then c else mkApp2 (mkConst ``And) c acc

/-- The projections `h.1, h.2.1, …, h.2…2` of `c₁ ∧ (… ∧ cₙ)`. -/
private def projs (h : Lean.Expr) (n : Nat) : MetaM (Array Lean.Expr) := do
  let mut out : Array Lean.Expr := #[]
  let mut cur := h
  for i in [0:n] do
    if i + 1 == n then out := out.push cur
    else
      out := out.push (← mkAppM ``And.left #[cur])
      cur ← mkAppM ``And.right #[cur]
  pure out

/-- The proof of the disjunct `d` from the proofs `hs` of the components of its condition. -/
private partial def build (d : Lean.Expr) (ws : List Lean.Expr) (hs : List Lean.Expr) :
    MetaM (Lean.Expr × List Lean.Expr × List Lean.Expr) := do
  if d.isAppOfArity ``Exists 2 then
    let w :: ws' := ws | throwError "sv_cover: internal error (witnesses)"
    let .lam _ _ b _ := d.appArg! | throwError "sv_cover: internal error (lambda)"
    let body := b.instantiate1 w
    let (pf, ws'', hs') ← build body ws' hs
    return (mkApp4 (mkConst ``Exists.intro d.getAppFn.constLevels!) d.appFn!.appArg! d.appArg! w pf, ws'', hs')
  else if d.isAppOfArity ``And 2 then
    if let some p := matchWin d then
      match hs with
      | hr :: h0 :: hC :: h1 :: h2 :: hs' =>
        let pf ← mkAppOptM ``rmN_win_suff #[some p.W, some p.r, some p.c0, some p.R, some p.C,
          some p.e, some p.wd, some hr, some h0, some hC, some h1, some h2]
        return (pf, ws, hs')
      | _ => throwError "sv_cover: internal error (window components)"
    else
      let h :: hs' := hs | throwError "sv_cover: internal error (components)"
      let (pf, ws', hs'') ← build d.appArg! ws hs'
      return (mkApp4 (mkConst ``And.intro) d.appFn!.appArg! d.appArg! h pf, ws', hs'')
  else
    let h :: hs' := hs | throwError "sv_cover: internal error (components)"
    return (h, ws, hs')

/-- The first window read of a disjunct (`rmN W R C`, `+ e` if any), for the error message. -/
private partial def readOf? (d : Lean.Expr) : Option Lean.Expr :=
  if d.isAppOfArity ``Exists 2 then
    match d.appArg! with
    | .lam _ _ b _ => readOf? b
    | _ => none
  else if d.isAppOfArity ``And 2 then
    match matchWin d with
    | some p =>
        let x := mkApp3 (mkConst ``LeanModels.Sv.CombView.rmN) p.W p.R p.C
        some (if p.e == mkNatLit 0 then x else mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) (mkConst ``Nat)
          (mkConst ``Nat) (mkConst ``Nat) (mkApp2 (mkConst ``instHAdd [0]) (mkConst ``Nat) (mkConst ``instAddNat)) x p.e)
    | none => (readOf? d.appFn!.appArg!).orElse fun _ => readOf? d.appArg!
  else none

/-! ## The walk -/

/-- The error of a goal the rule reads and cannot prove: the prefix is how `sv_cover` tells it from a
shape it does not read. -/
def diagPrefix : String := "sv_cover: the cell is not covered"

/-- Prove the cover statement `g` (a disjunction of writers, one writer, a window, a conjunction of
such, or a linear fact). `store` holds the conjuncts proved so far. -/
partial def coverGoal (store : IO.Ref (Array (Lean.Expr × Lean.Expr))) (g : MVarId) : TacticM Unit := do
  g.withContext do
    let T ← instantiateMVars (← g.getType)
    for (ty, pf) in ← store.get do
      if ty == T then
        g.assign pf
        return
    if T.isAppOfArity ``Or 2 || T.isAppOfArity ``Exists 2 || (matchWin T).isSome then
      chain #[] g
    else if T.isAppOfArity ``And 2 then
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      let [ga, gb] := gs | throwError "sv_cover: internal error (And.intro)"
      coverGoal store ga
      store.modify (·.push (← instantiateMVars (← ga.getType), ← instantiateMVars (mkMVar ga)))
      coverGoal store gb
    else
      setGoals [g]
      evalTactic (← `(tactic| omega))
      unless (← getGoals).isEmpty do throwError "sv_cover: a linear fact is not provable"
where
  /-- Is `L` refuted by the hypotheses alone (one `omega` call on `L → False`)? Then that writer cannot
  be the one, and the walk goes on without splitting on it: the last `omega` is spared one negated
  conjunction (each carries `Int.toNat` and division, that is, case splits). -/
  refuted (L : Lean.Expr) : TacticM Bool := do
    let saved ← saveState
    let m ← mkFreshExprSyntheticOpaqueMVar (mkForall `h .default L (mkConst ``False))
    let (_, m') ← m.mvarId!.intro1
    setGoals [m']
    let ok ← try
        evalTactic (← `(tactic| omega))
        pure (← getGoals).isEmpty
      catch _ => pure false
    unless ok do saved.restore
    pure ok
  chain (tried : Array Lean.Expr) (g : MVarId) : TacticM Unit := do
    g.withContext do
      let T ← instantiateMVars (← g.getType)
      if T.isAppOfArity ``Or 2 then
        let d := T.appFn!.appArg!
        let rest := T.appArg!
        let plan ← planOf d
        let L := mkAndAll plan.inL
        let skip ← refuted L
        if skip then
          let gs' ← g.apply (mkApp2 (mkConst ``Or.inr) d rest)
          let [g''] := gs' | throwError "sv_cover: internal error (Or.inr)"
          chain (tried.push L) g''
        else
          let emL ← mkAppM ``Classical.em #[L]
          let gs ← g.apply (← mkAppOptM ``Or.elim #[some L, some (mkNot L), some T, some emL])
          let [gl, gr] := gs | throwError "sv_cover: internal error (Or.elim)"
          let (hl, gl') ← gl.intro1
          gl'.withContext do
            let hs := plan.fullHs (← projs (mkFVar hl) plan.inL.size)
            let (pf, _, _) ← build d plan.ws.toList hs.toList
            unless (← isDefEq (← inferType pf) d) do throwError "sv_cover: internal error (ill-typed proof)"
            gl'.assign (mkApp3 (mkConst ``Or.inl) d rest pf)
          let (_, gr') ← gr.intro1
          let gs' ← gr'.apply (mkApp2 (mkConst ``Or.inr) d rest)
          let [g''] := gs' | throwError "sv_cover: internal error (Or.inr)"
          chain (tried.push L) g''
      else
        let plan ← planOf T
        let L := mkAndAll plan.inL
        let gL ← mkFreshExprSyntheticOpaqueMVar L
        setGoals [gL.mvarId!]
        let ok ← try
            evalTactic (← `(tactic| first | omega | trivial))
            pure (← getGoals).isEmpty
          catch _ => pure false
        unless ok do
          let tried := tried.push L
          let mut lines : MessageData := m!""
          for (c, i) in tried.toList.zipIdx do
            lines := lines ++ m!"\n  ({i + 1}) {← tidy c}"
          let rd := (readOf? T).getD T
          throwError "{diagPrefix}{indentExpr rd}\nneeds, for one of its writers (witnesses solved from the read's index), one of:{lines}\nand none of them follows from the hypotheses"
        let hs := plan.fullHs (← projs gL plan.inL.size)
        let (pf, _, _) ← build T plan.ws.toList hs.toList
        unless (← isDefEq (← inferType pf) T) do throwError "sv_cover: internal error (ill-typed proof)"
        g.assign pf

/-- The 2-D rule on the main goal (after `intros`). It fails with an ordinary exception on a shape it does
not read, and with a message that starts with `diagPrefix` on a goal it reads and cannot prove. -/
def coverCells : TacticM Unit := do
  let goal ← getMainGoal
  let store ← IO.mkRef (#[] : Array (Lean.Expr × Lean.Expr))
  coverGoal store goal
  unless ← goal.isAssigned do throwError "sv_cover: internal error (goal left open)"
  setGoals []

end CombCover
end LeanModels.Sv
