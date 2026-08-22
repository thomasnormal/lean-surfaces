/-
**The monadic rebuild's SCRIPT EXECUTOR** — running a whole PROGRAM.

`docs/python-monadic-rebuild.md` §7 ranked this last, gated on the closed-function
surface being mostly green. It is, so here it is.

# THE ONE PIPELINE, and why the executor exists at all

A module frame's locals ARE its globals. `runScript` therefore executes EVERY
top-level statement from an EMPTY world and PUBLISHES the frame's locals into
`World.globals` after each one — so a call made by a later statement reads exactly
what an earlier one bound. Nothing is folded, so nothing can be skipped, rolled
back, or read stale.

That per-statement publish is the whole reason this is not just `execOpenList`:
every compound statement needs a CONTROL SHELL that runs its body through the
publishing loop rather than delegating the statement wholesale. The trunk records
what happens without one — `scriptFlushCoherent`, the guard that refuses a
compound whose bindings a function body might read stale — and it is kept here.

# THE ADMISSION MACHINERY IS REUSED WHOLE

Everything above the trunk's executor is PURE and is imported, not rebuilt:
`classesCreationPure`, `defsBoundBefore`, `scriptFlushCoherent`, `scriptView`,
`publishScriptGlobals`, `scriptRebindMsg`, `benignImportBinds`,
`benignImportNames`, `dunderShaped`. That is roughly 530 of the trunk's 893
script lines. The rebuild owns the ~320 lines of CONTROL, exactly as it owns
`evalOpen`'s control and none of `evalBinOp`'s arithmetic.

# THE SHELLS RIDE A SECOND KNOT RECORD

Every shell is fuel-recursive (a `while` re-tests, a cursor re-reads), so none of
them can be a member of a structural block. `SKont` is the same
recursion-knot-boundary device `Kont` already is, for the script layer: each
shell is an ORDINARY non-recursive function of `S`, and every loop step goes
through a field, i.e. one fuel level down — precisely the trunk's
`execScriptStmts m fuel` recursion re-expressed.

Zero `sorry`. Zero `native_decide`.
-/
import LeanModels.Python.Monadic.Eval
import LeanModels.Python.Script

open LeanModels LeanModels.Python

namespace LeanModels.Python.Monadic

/-- The script layer's knot record — `Kont` for control shells. -/
structure SKont where
  /-- Top-level statements, PUBLISHING after each. -/
  stmts : List Stmt → SemF RFlow
  /-- One top-level statement. -/
  one : Stmt → SemF RFlow
  /-- `for … in d.items():` — CPython's dict_items iterator. -/
  items : Addr → Nat → Nat → Expr → List Stmt → SemF RFlow
  /-- `for` over an immutable value sequence. -/
  forSeq : Expr → List RVal → List Stmt → SemF RFlow
  /-- `for` over a heap list — the LIVE index cursor. -/
  forList : Expr → Addr → Nat → List Stmt → SemF RFlow
  /-- `for` over a generator — the LAZY cursor. -/
  forGen : Expr → Addr → List Stmt → SemF RFlow
  /-- `while … else`. -/
  whileL : Expr → List Stmt → List Stmt → SemF RFlow

/-- Fuel exhausted: every shell answers `.timeout`. -/
def SKont.bottom : SKont where
  stmts   := fun _ => exhausted
  one     := fun _ => exhausted
  items   := fun _ _ _ _ _ => exhausted
  forSeq  := fun _ _ _ => exhausted
  forList := fun _ _ _ _ => exhausted
  forGen  := fun _ _ _ => exhausted
  whileL  := fun _ _ _ => exhausted

/-- THE PUBLISH: a top-level binding IS a module global. A rebind the static
tables already own is the loud refusal, never a silent shadow. -/
def publishM (m : Module) : SemF Unit := do
  let st ← get
  match publishScriptGlobals m st with
  | some st' => set st'
  | Option.none => refuse scriptRebindMsg

/-- Bind a loop target and publish it BEFORE the body runs — the loop variable
is a module global too, and a function called from inside the body must see it. -/
def bindAndPublish (m : Module) (target : Expr) (v : RVal) : SemF Unit := do
  assignM target v
  publishM m

/-- Route a loop body's flow: `next`/`cont` continue, `brk` ends the loop
normally, `ret` propagates. Shared by all four cursors. -/
def loopFlow (again : SemF RFlow) : RFlow → SemF RFlow
  | .next | .cont => again
  | .brk => pure .next
  | .ret v => pure (.ret v)

/-! ## §1 THE SHELLS — ordinary functions of `S`, one fuel level per step -/

/-- Top-level statements, flushing after each. `break`/`continue` escape to an
enclosing shell; `return` is the top-level refusal. -/
def scriptStmtsAt (S : SKont) (m : Module) : List Stmt → SemF RFlow
  | [] => pure .next
  | s :: rest => do
      let flow ← S.one s
      publishM m
      match flow with
      | .next => S.stmts rest
      | .ret _ => refuse "'return' at module top level (CPython: SyntaxError at compile time)"
      | flow => pure flow

/-- `for target in d.items():` — the LIVE entries re-read per step, a SIZE
change the faithful `RuntimeError`. This is the one `for` the ordinary statement
executor cannot express, and the shipped sunfish padding loop is its target. -/
def scriptItemsAt (S : SKont) (m : Module) (a n i : Nat) (target : Expr)
    (body : List Stmt) : SemF RFlow := do
  match Heap.get? (← frameHeap) a with
  | some (.dict entries _) =>
      if entries.size ≠ n then
        raisePy (.runtimeError "dictionary changed size during iteration")
      else if hlt : i < entries.size then do
        bindAndPublish m target (.tuple #[entries[i].1, entries[i].2])
        loopFlow (S.items a n (i + 1) target body) (← S.stmts body)
      else pure .next
  | _ => refuse "internal: items-loop receiver is not a dict (report this)"

/-- The VALUE-sequence cursor (tuples, namedtuples, boundary lists, str code
points, materialized ranges — the snapshot IS the live semantics for all of
them, because every one of them is immutable). -/
def scriptForAt (S : SKont) (m : Module) (target : Expr) (xs : List RVal)
    (body : List Stmt) : SemF RFlow :=
  match xs with
  | [] => pure .next
  | x :: rest => do
      bindAndPublish m target x
      loopFlow (S.forSeq target rest body) (← S.stmts body)

/-- The LIVE INDEX CURSOR over a heap list — re-read each step, so in-place
mutation, growth and `pop`-shrinkage during iteration are observed exactly as
CPython's listiterator observes them. The referent dispatch and every one of its
refusals are the interpreter's verbatim. -/
def scriptForListAt (S : SKont) (m : Module) (target : Expr) (a i : Nat)
    (body : List Stmt) : SemF RFlow := do
  match Heap.get? (← frameHeap) a with
  | some (.cell _) => refuse cellInternal
  | some (.list xs) =>
      if i < xs.size then do
        bindAndPublish m target (xs.getD i .none)
        loopFlow (S.forList target a (i + 1) body) (← S.stmts body)
      else pure .next
  | some (.dict _ _) =>
      refuse "'for' over a dict is outside the tier (live dict iteration is deliberately NOT in the inventory — no snapshot shortcut; docs/memory-model.md)"
  | some (.instance _ _) => raisePy (.typeError "'object' object is not iterable")
  | some (.generator ..) =>
      if moduleGenFree m then
        refuse "internal: a generator object in a module with no generator defs (heap well-formedness violation — report this)"
      else S.forGen target a body
  | some (.closure ..) => refuse "internal: a list cursor over a function object (report this)"
  | some (.pyset _) => refuse "internal: a list cursor over a set (report this)"
  | Option.none => refuse "internal: a dangling heap address (report this)"

/-- The LAZY generator cursor: one `stepIter` per element, so the generator's own
body effects interleave exactly as they do under the interpreter's loop. -/
def scriptForGenAt (S : SKont) (K : Kont) (m : Module) (target : Expr) (a : Addr)
    (body : List Stmt) : SemF RFlow := do
  match ← inFrame (K.stepIter a) with
  | Option.none => pure .next
  | some v => do
      bindAndPublish m target v
      loopFlow (S.forGen target a body) (← S.stmts body)

/-- `while … else` over script statements. The `else` block runs on EXHAUSTION
and is SKIPPED by `break`; a `break` inside the `orelse` belongs to an ENCLOSING
loop and propagates. The tier is unchanged from the interpreter's `while` — only
the publish granularity differs. -/
def scriptWhileAt (S : SKont) (K : Kont) (m : Module) (test : Expr)
    (body orelse : List Stmt) : SemF RFlow := do
  let t ← evalOpen K m test
  let b ← truthyM t
  if b then loopFlow (S.whileL test body orelse) (← S.stmts body)
  else S.stmts orelse

/-- ONE top-level statement. `if`, `while`, `try` and every admitted `for` run
through control shells so the per-statement publish happens INSIDE them; a
whitelisted `import` is skipped (it binds through the static view, and running
one observes nothing); every LEAF statement is delegated to the interpreter, so
the TIER is the interpreter's and not a second one. -/
def scriptOneAt (S : SKont) (K : Kont) (m : Module) : Stmt → SemF RFlow
  | .whileLoop test body orelse _ => S.whileL test body.toList orelse.toList
  | .ifStmt test body orelse _ => do
      let t ← evalOpen K m test
      let b ← truthyM t
      if b then S.stmts body.toList else S.stmts orelse.toList
  | .forStmt target (.call (.attribute d "items" _) #[] #[] Option.none _) body orelse _ =>
      if orelse.isEmpty then do
        let dv ← evalOpen K m d
        match dv with
        | .ref a =>
            match Heap.get? (← frameHeap) a with
            | some (.dict entries _) => S.items a entries.size 0 target body.toList
            | _ =>
                refuse "'.items()' on a non-dict receiver is outside the tier (docs/memory-model.md §the one pipeline)"
        | _ =>
            refuse "'.items()' on a non-dict receiver is outside the tier (docs/memory-model.md §the one pipeline)"
      else refuse "'for … else' at module top level is outside the tier"
  | .forStmt target iter body orelse _ =>
      if orelse.isEmpty then do
        let it ← evalOpen K m iter
        match it with
        | .listV xs => S.forSeq target xs.toList body.toList
        | .tuple xs => S.forSeq target xs.toList body.toList
        | .ntuple _ _ xs => S.forSeq target xs.toList body.toList
        | .str t => S.forSeq target (strCharVals t) body.toList
        | .rangeV lo hi step => do
            let xs ← liftRes (rangeVals lo hi step)
            S.forSeq target xs body.toList
        | .ref a => S.forList target a 0 body.toList
        | v => raisePy (.typeError s!"'{v.typeName}' object is not iterable")
      else refuse "'for … else' is outside the v0 tier"
  | .tryStmt body excName handler tryUnsupported _ =>
      -- The admission is the interpreter's verbatim; only the body and handler
      -- statements move to the publishing loop.
      match tryUnsupported with
      | some reason =>
          refuse s!"try/except uses unsupported features ({reason}) — outside the tier (docs/memory-model.md §exceptions)"
      | Option.none => do
        let st ← get
        if (Env.lookup st.locals excName).isSome
            || (lookupG (moduleGlobals m).1 excName).isSome
            || (Env.lookup st.world.globals excName).isSome
            || (findFunction m excName).isSome then
          refuse s!"'except {excName}:': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
        else
          match findClass m excName with
          | Option.none =>
              if importErrorHandlerMatch excName then
                tryCatch (S.stmts body.toList) (fun e =>
                  match e with
                  | .importError _ => S.stmts handler.toList
                  | e => raisePy e)
              else
                refuse s!"'except {excName}:': only an admitted exception class (`class N(Exception): pass`) or the pinned import-error names (`ImportError`/`ModuleNotFoundError` — docs/memory-model.md §import forms) can be matched — wider builtin-name matching is outside the tier (docs/memory-model.md §exceptions)"
          | some (ci, c) =>
              if !c.isExc then
                refuse s!"'except {excName}:': class '{excName}' is not an admitted exception class — outside the tier (docs/memory-model.md §exceptions)"
              else
                tryCatch (S.stmts body.toList) (fun e =>
                  match e with
                  | .user cid _ => if cid == ci then S.stmts handler.toList else raisePy e
                  | e => raisePy e)
  | .unsupported "Import" text sp =>
      if (benignImportBinds text).isSome then pure .next
      else execOpen K m (.unsupported "Import" text sp)
  | .unsupported "ImportFrom" text sp =>
      if (benignImportBinds text).isSome then pure .next
      else execOpen K m (.unsupported "ImportFrom" text sp)
  | .delStmt names _ => do
      -- THE MODULE-SCOPE `del`. The frame's locals ARE the module globals and
      -- the one pipeline keeps them COMPLETE, so a locals HIT removes exactly
      -- CPython's module global. A MISS is decided in CPython's own order of
      -- authority, and the PARTIAL left-to-right effect is retained on the raise
      -- (`del x, nosuch` really removes `x`). Deletion never consults builtins:
      -- CPython's `del len` is the same `NameError`.
      let st ← get
      match delNames st.locals names.toList with
      | (env, Option.none) => do envPut env; pure .next
      | (env, some n) =>
          if dunderShaped n then
            refuse s!"'del {n}': deleting a module dunder is outside the tier (the model resolves dunder reads statically; CPython's removal uncovers the BUILTINS module's binding — docs/backlog.md §del RECONCILED)"
          else if (benignImportNames m).contains n then
            refuse s!"'del {n}': the name is bound by a whitelisted import, which the model binds statically — outside the tier (docs/backlog.md §del RECONCILED)"
          else if (findFunction m n).isSome || (findClass m n).isSome
              || m.namedtuples.any (·.name == n) then
            refuse s!"'del {n}': a module 'def'/'class'/namedtuple name is a static table entry; only a TRAILING del of it is admitted (rewritten at ingestion — docs/backlog.md §del RECONCILED)"
          else do envPut env; raisePy (.nameError n)
  | s => execOpen K m s

/-! ## §2 THE FUELED KNOT for the script layer -/

def skont (m : Module) : Nat → SKont
  | 0 => SKont.bottom
  | fuel + 1 =>
    let S := skont m fuel
    let K := kont m fuel
    { stmts   := scriptStmtsAt S m
      one     := scriptOneAt S K m
      items   := scriptItemsAt S m
      forSeq  := scriptForAt S m
      forList := scriptForListAt S m
      forGen  := scriptForGenAt S K m
      whileL  := scriptWhileAt S K m }
  termination_by structural fuel => fuel

/-! ## §3 THE BOUNDARY — same type as the trunk's `runScriptClock` -/

/-- Run a whole script under a SEEDED CLOCK TRACE: the three boundary admissions,
then THE ONE PIPELINE — every top-level statement executed, in order, from an
EMPTY world, against the `scriptView`. The decided outcome's world carries the
accumulated stdout. -/
def runScriptClockMono (m : Module) (clock : List Int) (fuel : Nat) :
    Run World Unit :=
  if !classesCreationPure m then
    .unsupported "a class whose CREATION does something observable (an unrecognized base, a metaclass keyword, a decorator on the class OR on one of its methods, or a class-level statement beyond undecorated methods/pass/docstring/literal attributes): CPython runs that at the `class` statement and the model executes no class body, so leanpy refuses rather than silently skip the effect"
  else if !defsBoundBefore m m.topLevel.toList then
    .unsupported "a top-level statement mentions a name this module defines LATER (`def`/`class`/namedtuple): CPython would raise NameError there, and the model's definition tables are position-independent, so leanpy refuses rather than run a definition that does not exist yet"
  else if !scriptFlushCoherent m then
    .unsupported "a compound top-level statement the executor does not run through a control shell (a 'for … else') binds a name some function body reads: top-level bindings become module globals only when the statement ENDS, so a call made from inside it would read that name stale — a control shell for the statement is the recorded fix, as `if`/`while`/`while … else`/`try`/`for` each got"
  else
    match toRun
        (inWorld [] ((skont (scriptView m) fuel).stmts m.topLevel.toList))
        { heap := #[], globals := [], stdout := [], clock := clock } with
    | .ok w flow =>
        match flow with
        | .next => .ok w ()
        | .ret _ => .unsupported "'return' at module top level (CPython: SyntaxError at compile time)"
        | .brk => .unsupported "'break' at module top level (CPython: SyntaxError at compile time)"
        | .cont => .unsupported "'continue' at module top level (CPython: SyntaxError at compile time)"
    | .exn w e => .exn w e
    | .timeout => .timeout
    | .unsupported msg => .unsupported msg

/-- The empty trace: any reachable `time.time()` refuses with the loud
fuel-independent underrun, never a fabricated reading. -/
def runScriptMono (m : Module) (fuel : Nat) : Run World Unit :=
  runScriptClockMono m [] fuel

/-! ## §4 NON-VACUITY — the pipeline RUNS, and the kernel decides it -/

private def spS : Span := ⟨0, 0, 0, 0⟩

private def pipeProg : Module :=
  { functions := #[], classes := #[], namedtuples := #[]
    topLevel := #[
      .assign #[.name "x" spS] (.constant (.int 1) spS) spS,
      .assign #[.name "y" spS] (.binOp (.name "x" spS) .add (.constant (.int 2) spS) spS) spS,
      .exprStmt (.call (.name "print" spS) #[.name "y" spS] #[] Option.none spS) spS ] }

/- THE ONE PIPELINE, end to end: three top-level statements, the second READING
what the first published, and `print` appending to the world's stdout. -/
#guard (match runScriptMono pipeProg 4096 with
        | .ok w _ => w.stdout == ["3"] && Env.lookup w.globals "y" == some (.int 3)
        | _ => false)

private def forProg : Module :=
  { functions := #[], classes := #[], namedtuples := #[]
    topLevel := #[
      .assign #[.name "t" spS] (.constant (.int 0) spS) spS,
      .forStmt (.name "i" spS)
        (.tuple #[.constant (.int 1) spS, .constant (.int 2) spS,
                  .constant (.int 3) spS] spS)
        #[ .augAssign (.name "t" spS) .add (.name "i" spS) spS ] #[] spS ] }

/- A top-level `for` runs through its CONTROL SHELL, so the loop variable is a
module global on EVERY iteration — which is exactly what the per-statement
publish granularity buys, and what delegating the statement wholesale would
lose. -/
#guard (match runScriptMono forProg 4096 with
        | .ok w _ => Env.lookup w.globals "t" == some (.int 6)
                     && Env.lookup w.globals "i" == some (.int 3)
        | _ => false)

#print axioms runScriptMono
#print axioms skont

end LeanModels.Python.Monadic
