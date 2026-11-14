import LeanModels.Sv.Kernel.ArrayE

/-!
# Direct flat-array E executor

The original array executor snapshots a function-valued `Store` after every
micro-step.  This companion route keeps flat continuous-assignment writes in
the array directly; non-flat and procedural processes fall back to the
authoritative executor.  The source AST and E evaluator are unchanged.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

structure FastConfig where
  cells : Array Val
  fallback : Store
  active : List ProcId
  k : Nat := 0

def FastConfig.store (c : FastConfig) : Store := arrayStore c.cells c.fallback

def FastConfig.ofConfig (E : Elab) (c : Config) : FastConfig :=
  { cells := arrayCells c.store E.decls.size, fallback := c.store,
    active := c.active, k := c.k }

def FastConfig.toConfig (c : FastConfig) : Config :=
  { store := c.store, active := c.active, k := c.k }

/-! The array view starts extensionally equal to the authoritative function
store.  This is the first refinement lemma for the direct route; subsequent
write lemmas can use it to relate a flat array update to `Store.set`. -/
theorem FastConfig.ofConfig_store (E : Elab) (c : Config) :
    (FastConfig.ofConfig E c).store = c.store := by
  unfold FastConfig.ofConfig FastConfig.store
  exact arrayStore_cells c.store E.decls.size

def fastWriteWins (E : Elab) (fallback : Store) (a : Array Val)
    (value : LVec) : List (Win × Nat) → Res (Array Val)
  | [] => .ok a
  | ((name, lo, width), off) :: rest =>
      match E.resolve name with
      | none => .unsupported s!"10.3.2: continuous assignment target '{name}' is undeclared"
      | some x =>
          match x.path with
          | _ :: _ => .unsupported "10.3.2: non-flat continuous assignment target"
          | [] =>
              let old := a.getD x.decl (fallback x)
              fastWriteWins E fallback
                (a.setIfInBounds x.decl (old.write lo (value.extract off width))) value rest

def fastActivateAssign (E : Elab) (c : FastConfig) (t : Lhs2) (e : Expr2) : Res (Array Val) := do
  let some ws := t.windows? E.toDesign2
    | .unsupported "10.3.2: continuous assignment target has no static window"
  let v ← evalPure2 (E.view c.store) e
  fastWriteWins E c.fallback c.cells (v.resizeU (Win.sumWidth ws)) (Win.placed ws)

def fastTriggered (E : Elab) (before after : FastConfig) : List ProcId :=
  E.triggered (E.view before.store) (E.view after.store)

def fastStep (E : Elab) (ch : Choice) (c : FastConfig) : Res (Option FastConfig) :=
  match ch.choose c.k c.active with
  | [] => .ok none
  | p :: rest =>
      match E.procs[p]? with
      | some (.assign t e) => do
          let cells ← fastActivateAssign E c t e
          let after : FastConfig := { c with cells, active := [], k := c.k + 1 }
          return some { after with
            active := rest ++ (fastTriggered E c after).filter (fun q => decide (q ∉ rest)) }
      | _ =>
          match step E ch c.toConfig with
          | .next c' => return some (FastConfig.ofConfig E c')
          | .slotClosed _ => return none
          | .refused r => .unsupported r.observable.2

def fastExec (E : Elab) (ch : Choice) : Nat → FastConfig → Res FastConfig
  | 0, _ => .timeout
  | n + 1, c =>
      match fastStep E ch c with
      | .ok none => .ok c
      | .ok (some c') => fastExec E ch n c'
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

def fastRun (E : Elab) (ch : Choice) (fuel : Nat) (env : List SvState) :
    Res (List FastConfig) :=
  match env with
  | [] => .ok []
  | entry :: rest =>
      let c := FastConfig.ofConfig E (Config.start E entry)
      match fastExec E ch fuel c with
      | .ok c' =>
          match fastRun E ch fuel rest with
          | .ok rows => .ok (c' :: rows)
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

end LeanModels.Sv.Kernel
