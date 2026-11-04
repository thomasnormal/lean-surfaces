import LeanModels.Sv.Comb2Proc

/-!
# Statement fuel of an `always_comb` body is sufficient (debt D-X1f, first half)

`Design2.combFuel` (`Comb2Base.lean`) bounds the fuel a pass needs: the right-hand side of every
assign, and since D-X1f the statement fuel of every `always_comb` body (`Stmt2.combFuelB`, the
`alwaysComb` arm of `Process2.rhsSize`). Before, that arm was `0`, so `Design2.settleFuel` was too
small for designs with `always_comb` blocks (MEASURED in `svgolf/design/architecture/X1-NOTE.md`
§10: `combSettle2` timed out at `settleFuel` on G-B's `mux1` and on `ibex`).

* `Stmt2.combFuelB_eq_fuelB`: the bound is `Comb2Proc`'s `Stmt2.fuelB`.
* `runCombProcess2_alwaysComb_of_combFuelB`: **sufficiency**. For a body the lowering accepts
  (the scope the assign arm has too: the comb profile), `runCombProcess2` completes at every fuel
  from the bound on. `runCombProcess2_alwaysComb_of_combFuel`: hence at `Design2.combFuel`.

**Scope: the comb profile only.** A body outside the lowering (a dynamic index target, an NBA, a
self-read, an `.unsupported` statement) has no claim: `Stmt2.combFuelB` does not count target index
expressions, so it is not a bound for such bodies, and nothing here says it is.

Termination of `combSettle2` on designs that are only window-acyclic is debt D-X1f2 (planned:
`CombPassSeq` of the per-window design, then `combSettle2_ok_of_stable`, then `CombSim`).
-/

namespace LeanModels.Sv

mutual

theorem Stmt2.combFuelB_eq_fuelB : ∀ s : Stmt2, s.combFuelB = s.fuelB
  | .blockingAssign _ _ => by simp only [Stmt2.combFuelB, Stmt2.fuelB]
  | .ifStmt _ t e => by
      simp only [Stmt2.combFuelB, Stmt2.fuelB, Stmt2.combFuelB_eq_fuelB t,
        Stmt2.optCombFuelB_eq_optFuelB e]
  | .block body => by
      simp only [Stmt2.combFuelB, Stmt2.fuelB, Stmt2.listCombFuelB_eq_listFuelB body.toList]
  | .caseStmt _ items dflt _ _ => by
      simp only [Stmt2.combFuelB, Stmt2.fuelB, Stmt2.optCombFuelB_eq_optFuelB dflt,
        CaseItem2.listCombFuelB_eq_listFuelB _ items.toList]
  | .nbaAssign _ _ => by simp only [Stmt2.combFuelB, Stmt2.fuelB]
  | .unsupported _ _ => by simp only [Stmt2.combFuelB, Stmt2.fuelB]
termination_by structural s => s

theorem Stmt2.optCombFuelB_eq_optFuelB : ∀ o : Option Stmt2, Stmt2.optCombFuelB o = Stmt2.optFuelB o
  | none => rfl
  | some s => by simp only [Stmt2.optCombFuelB, Stmt2.optFuelB, Stmt2.combFuelB_eq_fuelB s]
termination_by structural o => o

theorem Stmt2.listCombFuelB_eq_listFuelB :
    ∀ ss : List Stmt2, Stmt2.listCombFuelB ss = Stmt2.listFuelB ss
  | [] => rfl
  | s :: ss => by
      simp only [Stmt2.listCombFuelB, Stmt2.listFuelB, Stmt2.combFuelB_eq_fuelB s,
        Stmt2.listCombFuelB_eq_listFuelB ss]
termination_by structural ss => ss

theorem CaseItem2.combFuelB_eq_fuelB : ∀ it : CaseItem2, it.combFuelB = it.fuelB
  | .mk _ body => by simp only [CaseItem2.combFuelB, CaseItem2.fuelB, Stmt2.combFuelB_eq_fuelB body]
termination_by structural it => it

theorem CaseItem2.listCombFuelB_eq_listFuelB (fd : Nat) :
    ∀ its : List CaseItem2, CaseItem2.listCombFuelB fd its = CaseItem2.listFuelB fd its
  | [] => rfl
  | it :: rest => by
      simp only [CaseItem2.listCombFuelB, CaseItem2.listFuelB, CaseItem2.combFuelB_eq_fuelB it,
        CaseItem2.listCombFuelB_eq_listFuelB fd rest]
termination_by structural its => its

end

/-- **The statement fuel is sufficient** (the comb profile): for an `always_comb` body the
lowering accepts, `runCombProcess2` completes, with the lowered assign's write, at every fuel from
`Stmt2.combFuelB` on, on every state with the lowered design's shape. -/
theorem runCombProcess2_alwaysComb_of_combFuelB {d d' : Design2} (hl : d.lowerComb = some d')
    (hd' : CombDesign d') {i : Nat} {body : Stmt2} (hp : d.processes[i]? = some (.alwaysComb body))
    {st : SvState} (hs : StateShape d' st) {f : Nat} (hf : body.combFuelB ≤ f) :
    ∃ r, runCombProcess2 f st (.alwaysComb body) = .ok r := by
  obtain ⟨q, hq, hq'⟩ := Design2.lowerComb_proc hl hp
  obtain ⟨S, hsym, -, rfl⟩ := Process2.lowerComb_alwaysComb hq
  obtain ⟨v, -, hrun⟩ := runCombProcess2_alwaysComb_fwd hd' (Design2.lowerComb_spec hl).2.1 hsym hq'
    hs (by rw [← Stmt2.combFuelB_eq_fuelB]; exact hf)
  exact ⟨_, hrun⟩

/-- Hence at `Design2.combFuel`, and every fuel above it. -/
theorem runCombProcess2_alwaysComb_of_combFuel {d d' : Design2} (hl : d.lowerComb = some d')
    (hd' : CombDesign d') {i : Nat} {body : Stmt2} (hp : d.processes[i]? = some (.alwaysComb body))
    {st : SvState} (hs : StateShape d' st) {f : Nat} (hf : d.combFuel ≤ f) :
    ∃ r, runCombProcess2 f st (.alwaysComb body) = .ok r :=
  runCombProcess2_alwaysComb_of_combFuelB hl hd' hp hs
    (Nat.le_of_lt (Nat.lt_of_lt_of_le (Design2.combFuelB_lt_combFuel hp) hf))

#print axioms Stmt2.combFuelB_eq_fuelB
#print axioms runCombProcess2_alwaysComb_of_combFuelB
#print axioms runCombProcess2_alwaysComb_of_combFuel

end LeanModels.Sv
