import Lean
import LeanModels.Sv.CombKnownBits
import LeanModels.Sv.CombViewArith

/-!
# `sv_bridge`: from the printed equations of `sv_equations` to Nat-indexed facts (WP-P3)

`sv_equations` states each equation with the indices of the netlist in the form the summary computes
them: `Int` affine expressions of the loop variables, cast from `Nat` (`2 * ↑k + 1`, `↑N + ↑j + -1`),
1-D reads through `Int.toNat`, 2-D reads through `rmN W r c` (`CombViewArith.lean`). The arithmetic of a
proof (a multiplier, an adder) is stated over `Nat`-indexed Boolean functions: `S : Nat → Nat → Bool`
with hypotheses such as `S k c = (th (2 * k + 1) && S (2 * k + 1) c) || …` and `k - 1`, `N - 1 + j` in
their indices. Between the two sits a layer of casts, one `show … rw [show ((2 * k + 1 : Nat) : Int) = 2 *
↑k + 1 by omega, …]; exact e_x k (by omega) c (by omega)` per equation, and a theorem that restates every
printed equation as a hypothesis so that the `eq_*` can be passed to it (about 100 to 180 lines for the
multiplier references, `svgolf/PROVING.md`).

## The canonical view

`SvState.cell st n W r c` is bit `(r, c)` of the 2-D signal `n` whose rows are `W` bits wide, with the
coordinates in `Nat`: `st.boolAt n (rmN W r c)`. The arithmetic of a proof instantiates its 2-D functions
with `st.cell "S" (2 * (N : Int))`; a 1-D function is `st.boolAt "ae"`.

## The tactic

`sv_bridge e` closes a goal of the Nat-indexed form

    ∀ k, k < N - 1 → ∀ c, c < 2 * N →
      st.cell "S" W k c = (st.boolAt "th" (2 * k + 1) && st.cell "S" W (2 * k + 1) c) || …

from the raw hypothesis `e` (an `eq_*` that `sv_equations` produced, or a term applying one to explicit
arguments). It

1. introduces the binders of the goal;
2. instantiates `e`: its `Nat`/`Int` binders take the goal's index variables in order (a binder the goal
   does not bind is given explicitly: `sv_bridge (eq_s_plain_0 N (by omega))`), its premises are proved
   by `omega` from the goal's;
3. rewrites the instance with `rmN_add_col` (a read `s[r][c0 +: n]` is `rmN W r c0 + k`) and with the
   lemmas of the `with` clause, side conditions by `omega` (`sv_bridge eq_ae_plain_1 with ba` turns the
   input bit `st.boolAt "a" k` into `x.getLsbD k`; `with if_pos` resolves the packed `if k < N then …`);
4. compares the goal with the instance by congruence along the Boolean structure (`&&`, `||`, `^^`,
   `st.boolAt`, `rmN`), and proves every pair of index terms that differs by `omega`; the second closer
   unfolds `rmN` first, for a row-0 cell against a flat index (`rmN W 0 c` against `c`).

Everything the tactic builds is a proof term (`Eq.trans`, congruence lemmas, `omega`'s proofs), checked
by the kernel; a failure is an error that names the index equation it could not prove, never a
silently different statement. -/

namespace LeanModels.Sv

open CombView

/-- **The canonical row-major cell**: bit `(r, c)` of the 2-D signal `n`, whose rows are `W` bits wide,
in `Nat` coordinates (the flat bit `r * W + c`, through `rmN`). -/
@[reducible] def SvState.cell (st : SvState) (n : String) (W : Int) (r c : Nat) : Bool :=
  st.boolAt n (rmN W (r : Int) (c : Int))

namespace CombBridge

open Lean Meta Elab Tactic

/-- Close the goal `g : a = b`, where `a` and `b` differ only in `Nat`/`Int` index terms. Congruence at
the Boolean structure and at `rmN`; `omega` at the index leaves. `read` is the pair of bit reads being
matched (for the error message). -/
partial def bridgeEq (g : MVarId) (read : Option (Lean.Expr × Lean.Expr) := none) : TacticM Unit := do
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (α, a0, b0) := ty.eq? | throwError "sv_bridge: not an equation: {ty}"
    let a ← whnfR a0
    let b ← whnfR b0
    if ← withReducible (isDefEq a b) then
      g.assign (← mkEqRefl a0)
      return
    let α ← whnfR α
    let isRmN (e : Lean.Expr) := e.getAppFn.isConstOf ``LeanModels.Sv.CombView.rmN
    if (α.isConstOf ``Nat || α.isConstOf ``Int) && !(isRmN a && isRmN b) then
      setGoals [g]
      let ok ← try
          evalTactic (← `(tactic| first | omega | (simp only [rmN, Int.toNat_natCast]; omega)))
          pure (← getGoals).isEmpty
        catch _ => pure false
      unless ok do
        match read with
        | some (ra, rb) =>
            throwError "sv_bridge: cannot prove the index equality{indentExpr (← mkEq a b)}\nwhile matching the read{indentExpr ra}\nof the goal against{indentExpr rb}\nof the equation"
        | none => throwError "sv_bridge: cannot prove the index equality{indentExpr (← mkEq a b)}"
      return
    let read := if a.getAppFn.isConstOf ``LeanModels.Sv.SvState.boolAt then some (a, b) else read
    let g' ← g.replaceTargetDefEq (← mkEq a b)
    -- `closePost := false`: the default-transparency `rfl` that `congrN` tries on a pair it cannot split
    -- unfolds `SvState.boolAt` and is wasted work here
    let gs ← g'.congrN (depth := 1) (closePre := true) (closePost := false)
    -- no progress (the sides have different heads, e.g. a constant against a read): `congrN` returns the goal
    -- itself, and recursing on it would loop until the heartbeat limit hides the message (a wrong design)
    let noProgress ← match gs with
      | [g1] => pure ((← instantiateMVars (← g1.getType)) == (← instantiateMVars (← g'.getType)))
      | _ => pure false
    if noProgress then
      let rd := match read with
        | some (ra, rb) => m!"\nwhile matching the read{indentExpr ra}\nof the goal against{indentExpr rb}\nof the equation"
        | none => m!""
      throwError "sv_bridge: the goal and the equation have different shapes here{indentExpr a}\nagainst{indentExpr b}{rd}"
    for g'' in gs do bridgeEq g'' read

/-- `sv_bridge e` / `sv_bridge e with h₁, …, hₙ` — see the module docstring. -/
syntax (name := svBridge) "sv_bridge " term (" with " term,+)? : tactic

@[tactic svBridge] def evalSvBridge : Tactic := fun stx => do
  let e : TSyntax `term := ⟨stx[1]⟩
  let goal ← getMainGoal
  let (fvs, g1) ← goal.intros
  g1.withContext do
    let eT ← Tactic.elabTerm e none
    let eTy ← inferType eT
    -- the goal's index variables, in order
    let mut idx : Array FVarId := #[]
    for f in fvs do
      let t ← whnfR (← f.getType)
      if t.isConstOf ``Nat || t.isConstOf ``Int then idx := idx.push f
    -- instantiate the equation: index binders from the goal, premises as goals for `omega`
    let mut cur := eT
    let mut curTy ← whnfR eTy
    let mut di := 0
    let mut prem : Array MVarId := #[]
    repeat
      let .forallE _ d b _ := curTy | break
      let dT ← whnfR d
      if dT.isConstOf ``Nat || dT.isConstOf ``Int then
        let some x := idx[di]? | throwError
          "sv_bridge: the equation binds more indices than the goal; give the remaining ones explicitly: sv_bridge (e a b …)"
        di := di + 1
        cur := mkApp cur (mkFVar x)
        curTy := b.instantiate1 (mkFVar x)
      else
        let m ← mkFreshExprSyntheticOpaqueMVar d
        prem := prem.push m.mvarId!
        cur := mkApp cur m
        curTy := b.instantiate1 m
    for m in prem do
      setGoals [m]
      let ok ← try
          evalTactic (← `(tactic| omega))
          pure (← getGoals).isEmpty
        catch _ => pure false
      unless ok do
        throwError "sv_bridge: cannot discharge a premise of the equation from the goal's hypotheses{indentExpr (← m.getType)}"
    curTy ← instantiateMVars curTy
    -- the instance, with the normalizations of the `with` clause
    let g2 ← g1.assert `hraw curTy cur
    let (_, g3) ← g2.intro1P
    setGoals [g3]
    let extras : Array (TSyntax `term) :=
      if stx[2].isNone then #[] else stx[2][1].getSepArgs.map (⟨·⟩)
    let simpArgs ← extras.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    try evalTactic (← `(tactic| simp (disch := omega) only
          [LeanModels.Sv.CombView.rmN_add_col, $simpArgs,*] at $(mkIdent `hraw):ident))
    catch _ => pure ()
    if !extras.isEmpty then
      try evalTactic (← `(tactic| simp (disch := omega) only [$simpArgs,*])) catch _ => pure ()
    let g3 ← getMainGoal
    g3.withContext do
      let some hraw := (← getLCtx).findFromUserName? `hraw
        | throwError "sv_bridge: internal error (the instance was lost)"
      let hTy ← instantiateMVars hraw.type
      let gTy ← instantiateMVars (← g3.getType)
      let some (_, L, R) := gTy.eq?
        | throwError "sv_bridge: the goal is not an equation: {gTy}"
      let some (_, L', R') := hTy.eq?
        | throwError "sv_bridge: the hypothesis is not an equation: {hTy}"
      let gL ← mkFreshExprSyntheticOpaqueMVar (← mkEq L L')
      let gR ← mkFreshExprSyntheticOpaqueMVar (← mkEq R' R)
      g3.assign (← mkEqTrans (← mkEqTrans gL hraw.toExpr) gR)
      bridgeEq gL.mvarId!
      bridgeEq gR.mvarId!
      setGoals []

end CombBridge
end LeanModels.Sv
