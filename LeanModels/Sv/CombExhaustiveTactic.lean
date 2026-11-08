import LeanModels.Sv.CombExhaustiveSound
import LeanModels.Sv.CombProcTactic
import LeanModels.Sv.ProcNoQualified

/-!
# `sv_exhaustive`: a fixed-size combinational task by exhaustive kernel evaluation

`theorem solution : Goal := by sv_exhaustive` for a flat, parameterless design (every site plain) whose task
has few input bits. It reads the design's SUMMARY (`X.sem`, `PDesign.instantiateGD2`, does not reduce in the
kernel; the summary does), computes each site's depth (the rank of `sv_structure`, no table), compiles the
sites in depth order once into a gate program over one packed `Nat` (`compileNet`, checked once), and closes
each output by one `decide +kernel` over all inputs of the run against the task's function (`exh_out`).
`X.sem` is the alias-guarded family (`PDesign.instantiateGDAlias2`, ls-sv 7c9b7ac59): the comb theorems are
applied at the unguarded `PDesign.instantiateGD2` along `PDesign.instantiateGDAlias2_of_lowerComb` for a design
with `always_comb` processes (it lowers; `sv_structure` shows the guard inert at the guarded family, from the
summary's names where the design also has continuous assigns, `CombProcAlias.lean`) and along
`PDesign.instantiateGDAlias2_of_aliasInert` for a continuous-only one (`CombAliasInert.lean`), and the
no-qualified-`case` premise is `NoQ.semAlias_noQ` with the design passed
explicitly (left to unification it is a metavariable: `X.sem` does not unfold to `?d.instantiateGDAlias2 ?args`
below the `processes` projection).
A failing output reports the first input and output bit where the netlist and the task differ.

The kernel rule (measured on the 113-gate S-box): NO QUADRATIC OR STRING-KEYED CHECKS IN THE KERNEL; PROVE
STRUCTURE ONCE. A pairwise layout-disjointness check over the 107 names did not finish in 600 s, and a per-name
"is it written" scan over the sites was of the same kind; both are now theorems (`layout_inj` from the layout's
construction, `known_of_prog` from the compiled program). What the kernel still checks: one pass over the
sites (the compile check, one layout lookup per read), and the order and coverage over bit indices (`Nat`, no
string). Each output's exhaustive
decision is its own
auxiliary theorem: inside the main proof term the same closed decision did not finish in 900 s, on its own it
checks in about 22 s (measured, cause not identified).
-/

namespace LeanModels.Sv.Exh

open CombView

/-- Each site's depth at `σ`: 1 + the deepest site writing a window one of its reads overlaps. -/
def depths (s : Summary) (σ : String → Int) : List Nat :=
  let n := s.lsites.length
  let tg := s.lsites.map fun l => l.site.tgt.win σ (s.dw σ)
  let rd := s.lsites.map fun l => l.site.rds.map (·.win σ (s.dw σ))
  (List.range n).foldl (fun d _ => (List.range n).map fun i => 1 + ((List.range n).filter (fun j =>
    (rd.getD i []).any fun r => Win.overlaps r (tg.getD j ("", 0, 0)))).foldl (fun m j => max m (d.getD j 0)) 0)
    (List.replicate n 0)

end LeanModels.Sv.Exh

namespace SvExhaustive

open Lean Elab Tactic Meta LeanModels.Sv.CombView LeanModels.Sv.Exh

/-- `sv_decide`: a closed decidable goal, evaluated natively now and by the kernel at the end. -/
elab "sv_decide" : tactic => withMainContext do
  let g ← getMainGoal
  try unsafe closeByDecide g "false" catch e => throwError "sv_exhaustive: the check {← g.getType} failed: {e.toMessageData}"

/-- The first input tuple (all of `ws` bits) at which the Boolean `f` is false. -/
partial def firstFail (f : List Nat → MetaM Bool) : List Nat → List Nat → MetaM (Option (List Nat))
  | [], acc => do return if ← f acc.reverse then none else some acc.reverse
  | w :: ws, acc => do
      for v in List.range (2 ^ w) do
        if let some c ← firstFail f ws (v :: acc) then return some c
      return none

unsafe def runSvExhaustive : TacticM Unit := withDeepRec do
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  let some semN := (ty.find? fun e => e.isConst && e.constName!.getString! == "sem").map (·.constName!)
    | throwError "sv_exhaustive: no design `X.sem` in the goal"
  let pd := mkConst (semN.getPrefix ++ `pdesign)
  -- a design with `always_comb` processes is read by the procedural recognizer, through its lowering
  let (proc, s) ← match ← evalSummary pd with
    | .ok s => pure (false, s)
    | .error _ => match ← evalSummaryP pd with
      | .ok s => pure (true, s)
      | .error e => throwError "sv_exhaustive: the design is outside the comb fragment: {e}"
  unless s.lsites.all (·.hdrs.isEmpty) do throwError "sv_exhaustive: the design has a generate loop"
  let σ := s.val []
  let dep := depths s σ
  let ord := (List.range s.lsites.length).mergeSort fun i j => dep.getD i 0 ≤ dep.getD j 0
  let rk := (List.range ((s.lsites.map (·.site.pos)).foldl max 0 + 1)).map fun p =>
    ((s.lsites.zip dep).find? (·.1.site.pos == p)).elim 0 (·.2)
  let some prog := compileNet s σ (layout s σ) ord
    | throwError "sv_exhaustive: a site is outside the bitwise fragment (or reads past a declared width)"
  let lit (str : String) : TermElabM Term := do
    let .ok stx := Parser.runParserCategory (← getEnv) `term str | throwError "sv_exhaustive: internal: {str}"
    pure ⟨stx⟩
  let D := mkIdent semN
  let PD := mkIdent (semN.getPrefix ++ `pdesign)
  let S ← if proc then `((LeanModels.Sv.PDesign.summaryP $PD).toOption.getD default)
    else `((LeanModels.Sv.PDesign.summary $PD).toOption.getD default)
  let (OFF, ORD, PROG, RK) := (← `(layout $S (Summary.val $S [])), ← lit (toString (repr ord)),
    ← lit (toString (repr prog)), ← lit (toString (repr rk)))
  -- `X.sem` is the alias-guarded family (ls-sv 7c9b7ac59); the comb theorems below are stated at the unguarded one
  -- (`hA`). A design with `always_comb` processes lowers (`hl`, which `sv_structure` proves at the guarded family,
  -- for an `always_comb` beside continuous assigns too: `Summary.aliasOk`, `CombProcAlias.lean`), and a guarded
  -- design that lowers is its own guard (`PDesign.instantiateGDAlias2_of_lowerComb`); a continuous-only design is
  -- its own guard by the static check (`PDesign.instantiateGDAlias2_of_aliasInert`).
  if proc then evalTactic (← `(tactic| (
    obtain ⟨d', hl, hc, ha⟩ : ∃ d', LeanModels.Sv.Design2.lowerComb $D = some d' ∧ LeanModels.Sv.CombDesign d' ∧
        LeanModels.Sv.Acyclic d' := by
      sv_structure (rank := rippleRank (fun p => ($RK : List Nat).getD p 0) (fun _ _ _ => 0)); all_goals (intros; omega)
    have hA : $D = LeanModels.Sv.PDesign.instantiateGD2 $PD [] :=
      LeanModels.Sv.PDesign.instantiateGDAlias2_of_lowerComb (d := $PD) (args := []) hl
    refine $(mkIdent `SvGolf.CombTask.satisfiedAt_of_lowered) (by sv_interface) hl hc ha
      (LeanModels.Sv.NoQ.semAlias_noQ (d := $PD) (by sv_decide) _) ?_)))
  else evalTactic (← `(tactic| (
    have hA : $D = LeanModels.Sv.PDesign.instantiateGD2 $PD [] :=
      LeanModels.Sv.PDesign.instantiateGDAlias2_of_aliasInert (d := $PD) (by sv_decide) []
    obtain ⟨hc, ha⟩ : LeanModels.Sv.CombDesign $D ∧ LeanModels.Sv.Acyclic $D := by
      sv_structure (rank := rippleRank (fun p => ($RK : List Nat).getD p 0) (fun _ _ _ => 0))
    refine $(mkIdent `SvGolf.CombTask.satisfiedAt_of_comb) (by sv_interface) hc ha ?_)))
  evalTactic (← `(tactic| intro st heqs hs v hv))
  -- the task: its constant, its input names and widths
  let hvT ← withMainContext do whnfR (← instantiateMVars (← inferType (← getLCtx).lastDecl.get!.toExpr))
  let insE := hvT.getAppArgs[1]!
  let tC := insE.getAppArgs[0]!.getAppFn
  unless tC.isConst do throwError "sv_exhaustive: the task is not a named constant: {insE}"
  let insV ← unsafe evalExpr (List (String × Nat)) (← inferType insE) insE
  for i in List.range insV.length do evalTactic (← `(tactic| obtain ⟨$(mkIdent (.mkSimple s!"x{i}")), v⟩ := v))
  evalTactic (← `(tactic| obtain ⟨⟩ := v))
  let comp (i : Nat) : TacticM Lean.Expr := withMainContext do  -- the `i`-th input
    return (← getLocalDeclFromUserName (.mkSimple s!"x{i}")).toExpr
  evalTactic (← `(tactic|
    simp only [$(mkIdent tC.constName!):ident, $(mkIdent `SvGolf.HoldAll_cons):ident, $(mkIdent `SvGolf.HoldAll_nil):ident, and_true] at hv ⊢))
  let lst (ts : List Term) : TacticM Term := match ts with
    | [t] => pure t
    | _ => `(⟨$(ts.toArray),*⟩)
  let hvI (i : Nat) : TacticM Term := do
    let mut t ← `(hv)
    for _ in [0:i] do t ← `($t.2)
    if i + 1 < insV.length then `($t.1) else pure t
  let XS ← `([$((← (List.range insV.length).mapM fun i => do
    `(($(Syntax.mkStrLit insV[i]!.1), BitVec.toNat $(mkIdent (.mkSimple s!"x{i}"))))).toArray),*])
  let NAMES ← lit (toString (repr (insV.map (·.1))))
  let hinKs ← lst (← s.inputNames.mapM fun n => do
    `(LeanModels.Sv.CombEq.inKnown_ofBitVec (W := Summary.dw $S (Summary.val $S []) $(Syntax.mkStrLit n))
        $(← hvI (insV.findIdx (·.1 == n))) (by sv_decide)))
  let hxss ← lst (← (List.range insV.length).mapM fun i => do
    `(in_of_ofBitVec (s := $S) (σ := Summary.val $S []) $(← hvI i) (by sv_decide)))
  evalTactic (← `(tactic| (
    have hinK : Summary.InKnown $S (Summary.val $S []) st := by
      rw [Summary.InKnown, show Summary.inputNames $S = $(← lit (toString (repr s.inputNames))) from rfl]
      simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]; exact $hinKs
    have key := $(← if proc then `(LeanModels.Sv.CombEq.eq_viewL (s := $S) (args := []) (hs := rfl) (harity := rfl)
      (h1 := rfl) (hag := rfl) (hok := by sv_decide) (hfrag := by sv_decide)
      (hauto := Summary.autoObl_of_plain _ _ _ (by sv_decide) (by sv_decide))
      (hin := Summary.inRangeObl_of_plain _ _ (by sv_decide) (by sv_decide))
      (hself := noSelfRead_of_plain (by sv_decide) (by sv_decide) (by sv_decide))
      (hwid := widthOblL_of_plain (by sv_decide) (by sv_decide))
      (hbit := Summary.bitReadObl_of_plain _ _ (by sv_decide) (by sv_decide))
      (hcov := Summary.coverObl_of_plain _ _ (by sv_decide) (by sv_decide)) (hinK := hinK)
      (Eq.mp (congrArg (fun x => LeanModels.Sv.Design2.lowerComb x = some d') hA) hl) hc ha heqs hs)
      else `(eqsL_of_eqs (by sv_decide) (LeanModels.Sv.CombEq.eq_view (s := $S) (args := []) (hs := rfl)
      (harity := rfl) (h1 := rfl) (hag := rfl) (hok := by sv_decide) (hfrag := by sv_decide)
      (hauto := Summary.autoObl_of_plain _ _ _ (by sv_decide) (by sv_decide))
      (hin := Summary.inRangeObl_of_plain _ _ (by sv_decide) (by sv_decide))
      (hwid := Summary.widthObl_of_plain _ _ (by sv_decide) (by sv_decide))
      (hbit := Summary.bitReadObl_of_plain _ _ (by sv_decide) (by sv_decide))
      (hcov := Summary.coverObl_of_plain _ _ (by sv_decide) (by sv_decide)) (hinK := hinK)
      (Eq.mp (congrArg LeanModels.Sv.CombDesign hA) hc) (Eq.mp (congrArg LeanModels.Sv.Acyclic hA) ha)
      (Eq.mp (congrArg (fun x => LeanModels.Sv.CombEqs x st) hA) heqs)
      (Eq.mp (congrArg (fun x => LeanModels.Sv.StateShape x st) hA) hs))))
    have hc : compileNet $S (Summary.val $S []) $OFF $ORD = some $PROG := by sv_decide
    have hxs : ∀ p ∈ $XS, p.2 < 2 ^ Summary.dw $S (Summary.val $S []) p.1 ∧
        ∀ i < Summary.dw $S (Summary.val $S []) p.1, st.boolAt p.1 i = p.2.testBit i := by
      simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]; exact $hxss
    have ht : topoG (inBits $OFF (Summary.dw $S (Summary.val $S [])) $NAMES) [] $PROG = true := by sv_decide)))
  -- one goal per output, each closed by one exhaustive decision (the target is under an `mdata` here: a design with
  -- several outputs has a conjunction behind it)
  if (← getMainTarget).consumeMData.isAppOfArity ``And 2 then
    evalTactic (← `(tactic| repeat' refine And.intro ?_ ?_))
  for g in ← getGoals do
    setGoals [g]
    let some (_, lhs, _) := (← g.getType').eq? | throwError "sv_exhaustive: an output goal is not an equation: {← g.getType}"
    let .lit (.strVal y) := lhs.getAppArgs[1]! | throwError "sv_exhaustive: an output goal is not a port lookup"
    let some W := (s.decls.find? (·.name == y)).map (·.width σ) | throwError "sv_exhaustive: no output `{y}`"
    evalTactic (← `(tactic| rw [exh_out (xs := $XS) (y := $(Syntax.mkStrLit y)) key hc ht hxs
      (W := $(Syntax.mkNumLit (toString W))) (by sv_decide) (by decide) (by sv_decide)]))
    -- decide an equation of `BitVec`s: `LVec`'s `Array.ofFn` is well-founded recursion, slow in the kernel
    evalTactic (← `(tactic| refine congrArg (fun b => some (LeanModels.Sv.LVec.ofBitVec b)) ?_))
    let g ← getMainGoal
    g.withContext do
      let gty ← g.getType'
      let ws := (insV.map (·.2)).toArray
      let xfv ← (List.range ws.size).toArray.mapM comp
      let inst (bvs : Array Lean.Expr) : MetaM Lean.Expr := pure (gty.replaceFVars xfv bvs)  -- at the inputs `bvs`
      let stmt ← withLocalDeclsD (ws.mapIdx fun i w => (Name.mkSimple s!"n{i}",
        fun _ => pure (mkApp (mkConst ``Fin) (toExpr (2 ^ w))))) fun ns => do
          mkForallFVars ns (← inst ((ns.zip ws).map fun (n, w) => mkApp2 (mkConst ``BitVec.ofFin) (toExpr w) n))
      let hdec ← mkFreshExprMVar stmt
      try closeByDecide hdec.mvarId! "" catch _ =>
        let fin (vs : List Nat) := (vs.toArray.zip ws).map fun (v, w) => mkApp2 (mkConst ``BitVec.ofNat) (toExpr w) (toExpr v)
        let some c ← firstFail (fun vs => do
            let p ← inst (fin vs)
            evalExpr Bool (mkConst ``Bool) (mkApp2 (mkConst ``Decidable.decide) p (← synthInstance (mkApp (mkConst ``Decidable) p))))
          (ws.toList) [] | throwError "sv_exhaustive: the decision failed, but no input fails"
        let some (_, l, r) := (← inst (fin c)).eq? | throwError "sv_exhaustive: internal"
        let nat (e : Expr) : MetaM Nat := do
          evalExpr Nat (mkConst ``Nat) (mkApp2 (mkConst ``BitVec.toNat) (toExpr W) e)
        let (a, b) := (← nat l, ← nat r)
        let j := ((List.range W).find? fun j => a.testBit j != b.testBit j).getD 0
        throwError "sv_exhaustive: output `{y}` differs at inputs {List.zip (insV.map (·.1)) c}: the netlist gives {a}, the task {b}; first differing bit {y}[{j}]"
      let aux ← mkAuxTheorem stmt (← instantiateMVars hdec)  -- the kernel checks the decision on its own
      g.assign (mkAppN aux (← (List.range ws.size).toArray.mapM fun i => do mkAppM ``BitVec.toFin #[← comp i]))

/-- `sv_exhaustive`: see the module docstring. -/
elab "sv_exhaustive" : tactic => unsafe runSvExhaustive

end SvExhaustive
