import LeanModels.Sv.Ast

/-!
# SV M0 cycle/scheduler semantics (`LeanModels.Sv`)

The executable cycle-level semantics of `docs/sv-design-m0.md` ("Scheduler
core M0"). A run is a *deterministic* function of
`(design, stimulus, σ : ScheduleOracle, fuel)`; all LRM same-region ordering
freedom is concentrated in σ, so `∀ σ` theorems mean "for all legal
schedules" and a concrete σ is an executable simulator.

## The schedule oracle

`ScheduleOracle` bundles a choice function with its legality proof:

* `choose : Nat → List Nat → List Nat` — invocation counter and the ready
  list (indices into `Design.processes`) in, execution order out;
* `choose_perm` — every invocation yields a **permutation** of the ready
  list (the LRM never lets a simulator drop or duplicate a ready process).

Bundling the proof makes `∀ σ` theorems quantify over exactly the legal
schedules with no side conditions. The invocation counter `k` is threaded
through the whole run (never reset at cycle boundaries) and incremented at
every oracle invocation — one invocation per comb-settle **pass** and one
per edge phase — so a schedule may order every region of every cycle
independently, which is the LRM's actual freedom. `σ_src` (source order,
`choose := fun _ ready => ready`) is the executable default and matches
Xcelium's empirical order on the M0 examples; `σ_rev` reverses every
invocation; `ScheduleOracle.revWhen p` reverses exactly the invocations
with `p k = true` (witness-builder for race theorems).

## One cycle (`cycleStep`, the contract's 5 sub-steps)

1. Overwrite **declared input ports** from the cycle's stimulus entry
   (`applyInputs`). Stimulus names that are not input ports are ignored —
   the stimulus can never clobber internal state (essential for `∀ stim`
   theorems); an input absent from the entry holds its previous value.
2. Comb settle (`combSettle`): σ-ordered passes over the `always_comb` +
   continuous-`assign` processes until a pass changes nothing; the pass
   count is fuel-bounded, exhaustion = combinational loop = `.timeout`.
3. Edge phase (`edgePass`): every `@(posedge clk)` process runs **once**, in
   σ order. Blocking assigns hit the state immediately (this is what makes
   `race_blk` schedule-dependent); nonblocking assigns append to an NBA
   queue, so their reads see the sequential (pre-commit) state — the LRM's
   Active/NBA region split at cycle granularity.
4. NBA commit (`commitNba`) in queue order — last write to a name wins.
5. Comb settle again. The result is the cycle's trace snapshot.

`run` starts from `initState`: declaration initializers where present,
all-x otherwise (LRM §6.8 startup — verified: pre-reset `counter` is x).

## Semantic decisions beyond the contract text

* The clock is *implicit*: every `cycleStep` is one posedge of the (single)
  M0 clock, and every edge process fires each cycle. The recorded `clock`
  name and the value of a `clk` input in the state are not consulted.
* `unsupported` **processes** are scheduled in the comb phase
  (`Process.isCombPhase`), so any `cycleStep` on a design containing one is
  loud (`.unsupported`) instead of silently dropping the process (an
  ignored `initial` block would be silently wrong). Unsupported
  statements/expressions are loud only when actually *reached* — an
  untaken `if` branch may contain them harmlessly.
* A nonblocking assign inside `always_comb` (legal SV, absent from the M0
  examples) is `.unsupported` — its LRM semantics needs NBA scheduling
  inside the settle loop, which is the next tier.
* Reading an identifier that is not in the state is `.unsupported` (cannot
  arise from extracted designs — the extractor resolves all names).
* Fuel is a *depth* bound with the Python lane's discipline: every fueled
  function matches fuel first (`0 => .timeout`) and passes the decremented
  fuel to every recursive call (siblings share it). One `fuel` bounds both
  expression/statement depth and the number of settle passes.
* Out-of-range process indices and mid-phase process-kind mismatches are
  benign no-ops; `choose_perm` makes both unreachable — no theorem should
  rely on the fallback.
-/

namespace LeanModels.Sv

/-! ## Results -/

/-- Interpreter results — the Python lane's `Res` minus the exception arm
(M0 SV has no exceptions). `unsupported` = outside the M0 tier (loud),
`timeout` = fuel exhausted (in particular: combinational loop in settle).
Unification with `Core/` is an integration-checklist item. -/
inductive Res (α : Type) where
  | ok (a : α)
  | timeout
  | unsupported (msg : String)
deriving Repr, BEq, DecidableEq, Inhabited

instance : Monad Res where
  pure := .ok
  bind r f :=
    match r with
    | .ok a => f a
    | .timeout => .timeout
    | .unsupported msg => .unsupported msg

/-- Drop the failure information. -/
def Res.toOption : Res α → Option α
  | .ok a => some a
  | _ => none

/-! ## State -/

/-- Simulation state: association list signal-name ↦ current 4-state value
(same discipline as the Python lane's `Env`: first match wins, `set`
replaces in place). All writes target declared names, so a state built from
`initState` keeps declaration order forever — snapshots of different
schedules are comparable with `==`. `SvState` is an abbrev, so helpers must
be called by full name (`SvState.lookup st n`, not `st.lookup n`). -/
abbrev SvState := List (String × LVec)

/-- First match wins (there are no duplicates in states built by `run`). -/
def SvState.lookup : SvState → String → Option LVec
  | [], _ => none
  | (k, v) :: rest, name => if k == name then some v else SvState.lookup rest name

/-- Replace an existing binding in place, else append at the end. -/
def SvState.set : SvState → String → LVec → SvState
  | [], name, v => [(name, v)]
  | (k, w) :: rest, name, v =>
    if k == name then (name, v) :: rest else (k, w) :: SvState.set rest name v

/-- Display helper for tests/harness: the `%b` string of `name` in a state
(`"?"` when absent — cannot happen for declared signals). -/
def SvState.showSignal (st : SvState) (name : String) : String :=
  match SvState.lookup st name with
  | some v => v.toBinString
  | none => "?"

/-- Pending nonblocking updates of the current edge phase, in issue order.
Committed by `commitNba`; last write to a name wins. -/
abbrev NbaQueue := List (String × LVec)

/-! ## The schedule oracle -/

/-- A legal schedule: at invocation `k`, orders the ready process list.
`choose_perm` is the legality proof — every invocation is a permutation of
the ready list — so `∀ σ : ScheduleOracle` ranges over exactly the legal
schedules. See the module docstring for the invocation-counter protocol. -/
structure ScheduleOracle where
  /-- Invocation counter and ready process indices in, execution order out. -/
  choose : Nat → List Nat → List Nat
  /-- Every invocation yields a permutation of the ready list. -/
  choose_perm : ∀ (k : Nat) (ready : List Nat), (choose k ready).Perm ready

/-- Source/declaration order — the executable default. Xcelium empirically
follows this order on the M0 examples. -/
def σ_src : ScheduleOracle where
  choose := fun _ ready => ready
  choose_perm := fun _ ready => List.Perm.refl ready

/-- Reverse order at every invocation — the canonical second `race_blk`
witness. -/
def σ_rev : ScheduleOracle where
  choose := fun _ ready => ready.reverse
  choose_perm := fun _ ready => List.reverse_perm ready

/-- Reverse exactly the invocations with `p k = true`, source order
elsewhere — builds targeted schedule witnesses for race theorems. -/
def ScheduleOracle.revWhen (p : Nat → Bool) : ScheduleOracle where
  choose := fun k ready => if p k then ready.reverse else ready
  choose_perm := fun k ready => by
    split
    · exact List.reverse_perm ready
    · exact List.Perm.refl ready

instance : Inhabited ScheduleOracle := ⟨σ_src⟩

/-! ## Expression evaluation (pure helpers) -/

/-- Read a signal; an unknown identifier is outside the tier (loud), never
a default value. -/
def readSignal (st : SvState) (name : String) : Res LVec :=
  match SvState.lookup st name with
  | some v => .ok v
  | none => .unsupported s!"unknown identifier '{name}' (not a declared signal)"

/-- M0 unary operator on an evaluated operand (dispatches into the
`Basic.lean` op library — there is no second operator table). -/
def evalUnaryOp : UnaryOp → LVec → LVec
  | .bnot, v => v.not
  | .lnot, v => .ofLogic v.lnot
  | .neg, v => v.neg

/-- M0 binary operator on evaluated operands. 1-bit SV results
(`== != < <= > >=`) are lifted with `LVec.ofLogic`. -/
def evalBinOp : BinOp → LVec → LVec → LVec
  | .add, a, b => a.add b
  | .sub, a, b => a.sub b
  | .and, a, b => a.and b
  | .or, a, b => a.or b
  | .xor, a, b => a.xor b
  | .eq, a, b => .ofLogic (a.eqLogical b)
  | .ne, a, b => .ofLogic (a.neLogical b)
  | .lt, a, b => .ofLogic (a.lt b)
  | .le, a, b => .ofLogic (a.le b)
  | .gt, a, b => .ofLogic (a.gt b)
  | .ge, a, b => .ofLogic (a.ge b)

/-! ## The fueled interpreter core

Every function matches fuel first (`0 => .timeout`) and passes the
decremented fuel to every recursive call (the Python lane's discipline —
fuel is a depth bound, siblings share it; proofs do induction on fuel). -/

mutual

/-- Evaluate an expression in a state. M0 expressions are side-effect-free,
so a conditional evaluates **both** arms (`LVec.ternary` merges them when
the condition is ambiguous, §11.4.11) — an `unsupported` node in the
not-taken arm is therefore still loud, which is deliberately conservative. -/
def evalExpr (fuel : Nat) (st : SvState) (e : Expr) : Res LVec :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match e with
    | .lit v => .ok v
    | .ident name => readSignal st name
    | .unary op a => do
        return evalUnaryOp op (← evalExpr fuel st a)
    | .binary op l r => do
        let a ← evalExpr fuel st l
        let b ← evalExpr fuel st r
        return evalBinOp op a b
    | .ternary c t f => do
        let cv ← evalExpr fuel st c
        let tv ← evalExpr fuel st t
        let fv ← evalExpr fuel st f
        return LVec.ternary cv tv fv
    | .concat parts => do
        let vs ← evalExprs fuel st parts.toList
        return LVec.concatMany vs.toArray
    | .unsupported svKind _ => .unsupported s!"unsupported expression '{svKind}'"

/-- Evaluate a list of expressions left to right (concat parts, source
order — `parts[0]` most significant, per `LVec.concatMany`). -/
def evalExprs (fuel : Nat) (st : SvState) (es : List Expr) : Res (List LVec) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match es with
    | [] => .ok []
    | e :: rest => do
        let v ← evalExpr fuel st e
        let vs ← evalExprs fuel st rest
        return v :: vs

/-- Execute one statement: blocking assigns update the state immediately;
nonblocking assigns append `(target, value-now)` to the NBA queue (the value
is evaluated against the *current* state, commitment happens later);
an `if` with an untrue condition and no else is a no-op (§12.4 — an x/z
condition HOLDS targets, latch-style). -/
def execStmt (fuel : Nat) (st : SvState) (nba : NbaQueue) (stmt : Stmt) :
    Res (SvState × NbaQueue) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match stmt with
    | .blockingAssign target value => do
        let v ← evalExpr fuel st value
        return (SvState.set st target v, nba)
    | .nbaAssign target value => do
        let v ← evalExpr fuel st value
        return (st, nba ++ [(target, v)])
    | .ifStmt cond thenBranch elseBranch => do
        let c ← evalExpr fuel st cond
        if c.condTrue then
          execStmt fuel st nba thenBranch
        else
          match elseBranch with
          | some s => execStmt fuel st nba s
          | none => .ok (st, nba)
    | .block body => execStmts fuel st nba body.toList
    | .unsupported svKind _ => .unsupported s!"unsupported statement '{svKind}'"

/-- Execute statements in order, threading state and NBA queue. -/
def execStmts (fuel : Nat) (st : SvState) (nba : NbaQueue) (ss : List Stmt) :
    Res (SvState × NbaQueue) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 =>
    match ss with
    | [] => .ok (st, nba)
    | s :: rest => do
        let (st', nba') ← execStmt fuel st nba s
        execStmts fuel st' nba' rest

end

/-! ## Phase classification -/

/-- Comb-phase processes: `always_comb` and continuous `assign` — plus
`unsupported` processes, which are scheduled here so that any `cycleStep`
on a design containing one is loud instead of silently dropping it. -/
def Process.isCombPhase : Process → Bool
  | .alwaysComb _ | .assign _ _ | .unsupported _ _ => true
  | .alwaysFF _ _ | .alwaysPlain _ _ => false

/-- Edge-phase processes: `always_ff @(posedge c)` and
`always @(posedge c)` (identical M0 cycle semantics). -/
def Process.isEdgePhase : Process → Bool
  | .alwaysFF _ _ | .alwaysPlain _ _ => true
  | _ => false

/-- Indices into `d.processes` of the comb-phase ready set, source order —
what the oracle permutes at each settle pass. -/
def Design.combIndices (d : Design) : List Nat :=
  (List.range d.processes.size).filter fun i =>
    match d.processes[i]? with
    | some p => p.isCombPhase
    | none => false

/-- Indices into `d.processes` of the edge-phase ready set, source order —
what the oracle permutes at the edge phase. -/
def Design.edgeIndices (d : Design) : List Nat :=
  (List.range d.processes.size).filter fun i =>
    match d.processes[i]? with
    | some p => p.isEdgePhase
    | none => false

/-! ## Comb settle (contract sub-steps 2 and 5) -/

/-- Run one comb-phase process. Edge processes are a no-op here (unreachable
from `Design.combIndices`); `unsupported` processes are loud. A nonblocking
assign inside `always_comb` is outside the M0 cycle semantics (see module
docstring). -/
def runCombProcess (fuel : Nat) (st : SvState) : Process → Res SvState
  | .assign target value => do
      let v ← evalExpr fuel st value
      return SvState.set st target v
  | .alwaysComb body => do
      let (st', nba) ← execStmt fuel st [] body
      match nba with
      | [] => .ok st'
      | (name, _) :: _ =>
          .unsupported
            s!"nonblocking assignment to '{name}' inside always_comb is outside the M0 cycle semantics"
  | .alwaysFF _ _ | .alwaysPlain _ _ => .ok st
  | .unsupported svKind _ => .unsupported s!"unsupported process '{svKind}'"

/-- One settle pass: run the listed comb-phase processes once, left to
right. Out-of-range indices are skipped (unreachable for oracle orders —
they are permutations of `Design.combIndices`). -/
def combPass (d : Design) (fuel : Nat) (st : SvState) : List Nat → Res SvState
  | [] => .ok st
  | i :: rest => do
      let st' ← match d.processes[i]? with
        | some p => runCombProcess fuel st p
        | none => pure st
      combPass d fuel st' rest

/-- Comb settle: σ-ordered passes until one changes nothing. Every pass is
one oracle invocation (`k` increments even on the final, stable pass). Fuel
bounds the pass count — exhaustion means a combinational loop
(`.timeout`). Returns the settled state and the next invocation counter. -/
def combSettle (d : Design) (σ : ScheduleOracle) (fuel : Nat) (st : SvState)
    (k : Nat) : Res (SvState × Nat) :=
  match fuel with
  | 0 => .timeout
  | fuel + 1 => do
      let st' ← combPass d fuel st (σ.choose k d.combIndices)
      if st' == st then .ok (st', k + 1)
      else combSettle d σ fuel st' (k + 1)

/-! ## Edge phase and NBA commit (contract sub-steps 3 and 4) -/

/-- Run one edge-phase process (comb processes are a no-op here,
unreachable from `Design.edgeIndices`). `always_ff` and plain `always`
posedge blocks are semantically identical in M0. -/
def runEdgeProcess (fuel : Nat) (st : SvState) (nba : NbaQueue) :
    Process → Res (SvState × NbaQueue)
  | .alwaysFF _ body => execStmt fuel st nba body
  | .alwaysPlain _ body => execStmt fuel st nba body
  | .alwaysComb _ | .assign _ _ => .ok (st, nba)
  | .unsupported svKind _ => .unsupported s!"unsupported process '{svKind}'"

/-- The edge phase: run the listed edge processes once each, left to right,
threading the sequential state (blocking assigns are immediately visible to
later processes in the order — the `race_blk` mechanism) and the NBA queue
(nonblocking reads see pre-commit values — the `swap_nba` mechanism). -/
def edgePass (d : Design) (fuel : Nat) (st : SvState) (nba : NbaQueue) :
    List Nat → Res (SvState × NbaQueue)
  | [] => .ok (st, nba)
  | i :: rest => do
      let (st', nba') ← match d.processes[i]? with
        | some p => runEdgeProcess fuel st nba p
        | none => pure (st, nba)
      edgePass d fuel st' nba' rest

/-- Commit the NBA queue in issue order; sequential `SvState.set` makes the
last write to a name win. -/
def commitNba (st : SvState) (nba : NbaQueue) : SvState :=
  nba.foldl (fun s u => SvState.set s u.1 u.2) st

/-! ## The cycle (contract sub-step 1 + assembly) -/

/-- Overwrite **declared input ports** from the cycle's stimulus entry.
Only names in `d.inputNames` are consulted: the stimulus can never touch
internal state or outputs, and an input absent from the entry holds its
previous value. -/
def applyInputs (d : Design) (inputs : SvState) (st : SvState) : SvState :=
  d.inputNames.foldl
    (fun s name =>
      match SvState.lookup inputs name with
      | some v => SvState.set s name v
      | none => s)
    st

/-- LRM startup state (§6.8): declaration initializers where present,
all-x otherwise, in declaration order. -/
def initState (d : Design) : SvState :=
  d.decls.toList.map fun dc => (dc.name, dc.init.getD (LVec.xVec dc.width))

/-- One clock cycle — exactly the contract's 5 sub-steps. `k` is the oracle
invocation counter carried across cycles (default `0` gives the
contract-shaped call `cycleStep d σ fuel inputs s`); the settled state is
the cycle's trace snapshot, returned with the next counter. -/
def cycleStep (d : Design) (σ : ScheduleOracle) (fuel : Nat) (inputs : SvState)
    (st : SvState) (k : Nat := 0) : Res (SvState × Nat) := do
  let st0 := applyInputs d inputs st                                    -- 1. inputs
  let (st1, k1) ← combSettle d σ fuel st0 k                             -- 2. comb settle
  let (st2, nba) ← edgePass d fuel st1 [] (σ.choose k1 d.edgeIndices)   -- 3. edge phase
  let st3 := commitNba st2 nba                                          -- 4. NBA commit
  combSettle d σ fuel st3 (k1 + 1)                                      -- 5. comb settle

/-- Run the remaining stimulus from a given state and invocation counter —
one snapshot per stimulus entry (`run` unfolds to this; induction over
cycles is induction over `stim` with `st`/`k` generalized). -/
def runFrom (d : Design) (σ : ScheduleOracle) (fuel : Nat) (st : SvState)
    (k : Nat) : List SvState → Res (List SvState)
  | [] => .ok []
  | inputs :: rest => do
      let (st', k') ← cycleStep d σ fuel inputs st k
      let tr ← runFrom d σ fuel st' k' rest
      return st' :: tr

/-- The contract entry point: initial state from declaration initializers
(all other signals all-x), one `cycleStep` and one trace snapshot per
stimulus entry. -/
def run (d : Design) (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
    Res (List SvState) :=
  runFrom d σ fuel (initState d) 0 stim

end LeanModels.Sv
