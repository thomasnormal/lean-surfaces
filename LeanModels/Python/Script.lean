import LeanModels.Python.Semantics

/-!
# `leanpy` v0 — module-level script execution (docs/backlog.md, owner-directed)

Run a whole current-tier Python FILE under the Lean semantics: execute the
module's top level in one world, collecting `print` output into
`World.stdout` (effects are data — docs/memory-model.md §effects). The
runner boundary (Main.lean `--script`) maps the outcome to stdout + an
exit status; the differential side is `harness/script_corpus.py` (stdout +
exit code against the pinned CPython 3.9, first-unsupported-construct
telemetry).

## The consistency architecture (v0)

`Module` splits functions from `topLevel` and G1 folds the whole top
level at import time, while a script also EXECUTES it — two views of one
scope. v0 keeps them provably coherent by splitting the top level at the
**G1-faithful prefix boundary**:

* the PREFIX — the leading run of plain `NAME = …` / tuple binds,
  docstrings, and `pass` — is exactly what the G1 fold executes
  faithfully into `initWorld` (values, heaps, dict identities). The live
  run SKIPS it: top-level reads fall through locals to the very objects
  function bodies resolve, so identity and mutation stay shared.
* the SUFFIX — everything from the first other statement — runs LIVE
  (`execStmt`, plus the control shells below), binding into the script's
  locals. Suffix heap mutations (`tt[k] = v`) act on the shared world and
  are visible to calls; suffix NAME bindings are visible only at top
  level, and `suffixConsistent` refuses the script whenever a function
  body reads a suffix-assigned name, so a call never sees one stale.

THE MODULE THE LIVE RUN THREADS IS THE PREFIX VIEW (`runScript`'s
`mPre`, `topLevel := g1Prefix …`): the G1 fold — dirty-name poisoning
included — must see ONLY the statements whose effects are claimed by
`initWorld`, because the suffix is EXECUTED, not folded. Folding the
whole top level poisoned prefix-bound names the suffix rebinds or
stores into (`n = n + 2` in a loop, `tt[1] = 11`) although the live run
replays exactly those statements — the 2026-08-10 corpus regression
(fib_loop/tt_script/list_script, broken by the dirty-name pass
6a79764, bisected and fixed the same day). The prefix view is all
`g1Shape`, so its fold is always `analysable`; a top-level name miss is
then a FAITHFUL `NameError`, which is sound because suffix bindings are
visible in the script's locals and every suffix statement whose binding
set the executor cannot honour refuses loudly before any later read.

Refusals — every one LOUD, never wrong:

* a function definition whose span does not precede every SUFFIX
  statement (a live statement could call it before CPython would have
  bound it);
* a suffix (nested-)assignment to ANY name some function body reads
  (`funcGlobalReads`): a prefix-bound name would go stale for calls, and
  a fresh suffix global would resolve to a fake `NameError` under the
  prefix view (the ordered `ModuleItem` representation is the recorded
  fix);
* a `print` under a live LOCAL binding of `print` (a suffix `print = …`
  already executed — CPython would call the shadow);
* `print` of containers/heap values (repr subtleties), a shadowed
  `print`, `print` in expression position or inside a function body (the
  effect must thread the mutual block to land there — this v0 keeps the
  proof-relevant interpreter untouched);
* top-level `return`/`break`/`continue` (CPython compile-time
  SyntaxErrors the extractor happily ships).

The executor is FUELED like the mutual block and lives OUTSIDE it. The
`while`/`if` arms below are CONTROL SHELLS mirroring `execWhile`/
`execStmt` exactly (test, `truthyH`, flow routing) so `print` works
inside top-level loops; leaf statements still run through `execStmt`, so
the tier is the interpreter's. `for` bodies are delegated wholesale
(prints inside a top-level `for` are loud — extend the shell when the
corpus wants it).
-/

namespace LeanModels.Python

/-- CPython `str()` of the printable scalar tier (`print` v0): ints in
decimal, `True`/`False`, `None`, strings raw. `none` = not printable in
v0 (containers, refs — loud at the call site). -/
def strOfRVal : RVal → Option String
  | .int n => some (toString n)
  | .bool b => some (if b then "True" else "False")
  | .none => some "None"
  | .str s => some s
  | _ => Option.none

/-- Space-join `print` arguments (default `sep`); first unprintable wins. -/
def strOfArgs : List RVal → Option String
  | [] => some ""
  | [v] => strOfRVal v
  | v :: vs => do
    let s ← strOfRVal v
    let rest ← strOfArgs vs
    return s ++ " " ++ rest

/-- Is `print` unshadowed at module level? A module `def print` or a
top-level `print` binding (valued or poisoned) refuses loudly — CPython
would call the shadow. -/
def printUnshadowed (m : Module) : Bool :=
  (findFunction m "print").isNone && (lookupG (moduleGlobals m).1 "print").isNone

/-! ### Name walkers (the function-global consistency guard) -/

mutual
  /-- Every `Name` occurring in the expression (reads overapproximated). -/
  def Expr.allNames : Expr → List String
    | .constant .. => []
    | .name id _ => [id]
    | .binOp l _ r _ => l.allNames ++ r.allNames
    | .unaryOp _ e _ => e.allNames
    | .boolOp _ vs _ => Expr.allNamesList vs.toList
    | .compare l _ cs _ => l.allNames ++ Expr.allNamesList cs.toList
    | .call f args kwargs _ _ =>
      f.allNames ++ Expr.allNamesList args.toList
        ++ Expr.allNamesKw kwargs.toList
    | .list es _ => Expr.allNamesList es.toList
    | .tuple es _ => Expr.allNamesList es.toList
    | .subscript v i _ => v.allNames ++ i.allNames
    | .dict ks vs _ => Expr.allNamesList ks.toList ++ Expr.allNamesList vs.toList
    | .attribute v _ _ => v.allNames
    | .ifExp t b o _ => t.allNames ++ b.allNames ++ o.allNames
    | .slice v l u st _ => v.allNames ++ l.allNames ++ u.allNames ++ st.allNames
    | .genExp e t it ifs wb _ =>
      e.allNames ++ t.allNames ++ it.allNames ++ Expr.allNamesList ifs.toList
        ++ Expr.allNamesKw wb.toList
    | .unsupported .. => []

  /-- Elementwise `Expr.allNames`. -/
  def Expr.allNamesList : List Expr → List String
    | [] => []
    | e :: es => e.allNames ++ Expr.allNamesList es

  /-- `Expr.allNames` over keyword-argument values (H6). -/
  def Expr.allNamesKw : List (String × Expr) → List String
    | [] => []
    | (_, e) :: rest => e.allNames ++ Expr.allNamesKw rest

end

mutual
  /-- Every `Name` occurring in the statement. -/
  def Stmt.allNames : Stmt → List String
    | .ret Option.none _ => []
    | .ret (some e) _ => e.allNames
    | .assign tgts v _ => Expr.allNamesList tgts.toList ++ v.allNames
    | .augAssign t _ v _ => t.allNames ++ v.allNames
    | .whileLoop t b o _ =>
      t.allNames ++ Stmt.allNamesList b.toList ++ Stmt.allNamesList o.toList
    | .forStmt t it b o _ =>
      t.allNames ++ it.allNames ++ Stmt.allNamesList b.toList
        ++ Stmt.allNamesList o.toList
    | .defStmt _ _ _ _ _ _ body _ _ => Stmt.allNamesList body.toList
    | .ifStmt t b o _ =>
      t.allNames ++ Stmt.allNamesList b.toList ++ Stmt.allNamesList o.toList
    | .exprStmt e _ => e.allNames
    | .yieldStmt e _ => e.allNames
    | .yieldFromStmt v _ => v.allNames
    -- exceptions tier: the handler class name is a read too
    | .raiseStmt exc cause _ =>
      (exc.map Expr.allNames).getD [] ++ (cause.map Expr.allNames).getD []
    | .tryStmt b excName hnd _ _ =>
      excName :: Stmt.allNamesList b.toList ++ Stmt.allNamesList hnd.toList
    | .pass _ | .brk _ | .cont _ => []
    | .unsupported .. => []

  /-- Elementwise `Stmt.allNames`. -/
  def Stmt.allNamesList : List Stmt → List String
    | [] => []
    | s :: ss => s.allNames ++ Stmt.allNamesList ss
end

/-- Target names of an assignment-like target expression (plain and tuple
targets; subscript primaries bind nothing). -/
def targetBoundNames : Expr → List String
  | .name id _ => [id]
  | .tuple es _ | .list es _ => (targetNamesG es.toList).getD []
  | _ => []

mutual
  /-- Every name the statement (nested included) ASSIGNS — CPython's
  static-locals collection, overapproximated. -/
  def Stmt.assignedNames : Stmt → List String
    | .assign tgts _ _ => (tgts.toList.map targetBoundNames).flatten
    | .augAssign t _ _ _ => targetBoundNames t
    | .whileLoop _ b o _ =>
      Stmt.assignedNamesList b.toList ++ Stmt.assignedNamesList o.toList
    | .forStmt t _ b o _ =>
      targetBoundNames t ++ Stmt.assignedNamesList b.toList
        ++ Stmt.assignedNamesList o.toList
    | .ifStmt _ b o _ =>
      Stmt.assignedNamesList b.toList ++ Stmt.assignedNamesList o.toList
    | .tryStmt b _ hnd _ _ =>
      Stmt.assignedNamesList b.toList ++ Stmt.assignedNamesList hnd.toList
    | _ => []

  /-- Elementwise `Stmt.assignedNames`. -/
  def Stmt.assignedNamesList : List Stmt → List String
    | [] => []
    | s :: ss => s.assignedNames ++ Stmt.assignedNamesList ss
end

/-- Names a function body reads from MODULE scope: every name occurrence
minus its params, its (CPython-static) locals, module function names, and
builtins. Overapproximates reads — refusing more is sound. -/
def funcGlobalReads (m : Module) (f : FunctionDefn) : List String :=
  let locals := f.params.toList.map Param.arg ++ Stmt.assignedNamesList f.body.toList
  let fnames := m.functions.toList.map FunctionDefn.name
  let cnames := m.classes.toList.map ClassDefn.name
  (Stmt.allNamesList f.body.toList).filter fun n =>
    !locals.contains n && !fnames.contains n && !cnames.contains n
      && !isBuiltinName n

/-- All module-scope names any function reads. -/
def moduleGlobalReads (m : Module) : List String :=
  (m.functions.toList.map (funcGlobalReads m)).flatten

/-! ### The prefix boundary -/

/-- Statement shapes the G1 fold executes FAITHFULLY (while complete):
plain name/tuple binds, constant expression statements (docstrings), and
`pass`. -/
def g1Shape : Stmt → Bool
  | .assign tgts _ _ =>
    match tgts.toList with
    | [.name _ _] => true
    | [.tuple es _] => (targetNamesG es.toList).isSome
    | _ => false
  | .exprStmt (.constant ..) _ => true
  | .pass _ => true
  | _ => false

/-- The live SUFFIX: everything from the first non-G1-shape statement. -/
def liveSuffix : List Stmt → List Stmt
  | [] => []
  | s :: rest => if g1Shape s then liveSuffix rest else s :: rest

/-- The G1-faithful PREFIX: the leading run of `g1Shape` statements —
`liveSuffix`'s complement (`g1Prefix ss ++ liveSuffix ss = ss`). The live
run folds `initWorld` over THIS list only (`runScript`'s `mPre`): the
suffix is executed, so folding it too would poison prefix-bound names the
suffix rebinds or stores into — effects the replay is about to perform. -/
def g1Prefix : List Stmt → List Stmt
  | [] => []
  | s :: rest => if g1Shape s then s :: g1Prefix rest else []

/-- The span of a statement (every constructor carries one last). -/
def scriptStmtSpan : Stmt → Span
  | .ret _ sp | .assign _ _ sp | .augAssign _ _ _ sp
  | .whileLoop _ _ _ sp | .forStmt _ _ _ _ sp | .ifStmt _ _ _ sp
  | .exprStmt _ sp | .yieldStmt _ sp | .yieldFromStmt _ sp
  | .pass sp | .brk sp | .cont sp
  | .defStmt _ _ _ _ _ _ _ _ sp
  | .raiseStmt _ _ sp | .tryStmt _ _ _ _ sp
  | .unsupported _ _ sp => sp

/-- The last line at which the module's `def` / `class` / recognized
namedtuple statements BIND the plain name `n`, if any. Duplicate
definitions resolve last-wins everywhere in the model, so the LAST one is
the binding a reference must come after. Flattened method names carry a
`.` and synthesized genexp functions a leading `<` — neither is a Python
identifier, so neither can be the `n` of a source reference. -/
def defBindEnd (m : Module) (n : String) : Option Nat :=
  let ends :=
    (m.functions.toList.filterMap fun f =>
        if f.name == n then some f.span.endLineno else Option.none)
      ++ (m.classes.toList.filterMap fun c =>
        if c.name == n then some c.span.endLineno else Option.none)
      ++ (m.namedtuples.toList.filterMap fun nt =>
        if nt.name == n then some nt.span.endLineno else Option.none)
  ends.foldl (fun acc e => some (max (acc.getD 0) e)) Option.none

/-- ORDERED ADMISSION (2026-08-12 — replaces the blanket "every definition
precedes all live code"). `Module` splits definitions out of `topLevel`
into position-independent tables, so the model can reach a function CPython
has not bound yet; the blanket rule bought soundness by refusing every
interleaved file, which the first completeness survey measured as the top
blocker of real Python (146 of 158 stdlib refusals).

The precise condition is per statement and per NAME: a top-level statement
may mention a name the module binds by `def`/`class`/namedtuple only if
that definition ENDS before the statement begins. Then the model's
position-independent table and CPython's sequential binding agree on every
reference actually made — and a reference to a not-yet-bound name, where
CPython raises `NameError` and the model would happily call, refuses
loudly instead.

The check covers ALL of `topLevel`, not just the live suffix: the G1
prefix is folded (and, when the fold refuses, EXECUTED) at its own
position, so `x = f()` above `def f` is the same hazard there.
`Stmt.allNames` overapproximates reads, so the answer errs toward
refusing. A SYNTHESIZED genexp function (`<genexpr@n>`) is exempt for the
old reason: its name is unnameable in Python, and CPython builds the same
implicit function at exactly the expression it replaced. -/
def defsBoundBefore (m : Module) (stmts : List Stmt) : Bool :=
  stmts.all fun s =>
    let ln := (scriptStmtSpan s).lineno
    (Stmt.allNames s).all fun n =>
      n.startsWith "<" ||
        match defBindEnd m n with
        | some e => decide (e < ln)
        | Option.none => true

/-- `__name__ = "__main__"` — the RUNNER-SUPPLIED global (docs/memory-model.md
§effects: the same family as `argv`, marshalled in at world initialization).

CPython's import machinery binds `__name__` before the first statement
runs, and for a file executed AS A PROGRAM — which is exactly what leanpy
does — its value is `"__main__"`. The model has no import machinery, so a
read used to refuse loudly ("bound by the import machinery, not by a
statement"), which walled off every `if __name__ == "__main__":` block in
real Python. Script mode therefore PREPENDS this binding to the prefix
view the G1 fold sees: static resolution finds it before the dunder arm,
and a file that rebinds `__name__` itself still wins, since its own
statement comes later in the fold.

Span line 0 is below every real statement, so the binding cannot disturb
the ordering admission (which reads `m.topLevel`, not the prefix view).
The other module dunders (`__file__`, `__doc__`, `__spec__`, …) keep the
loud refusal: only `__name__` has a value the runner boundary fixes. -/
def scriptNameBinding : Stmt :=
  let sp : Span := { lineno := 0, colOffset := 0, endLineno := 0, endColOffset := 0 }
  .assign #[.name "__name__" sp] (.constant (.str "__main__") sp) sp

/-- CLASS CREATION IS AN EFFECT (docs/memory-model.md §class creation).
CPython evaluates a class's bases and runs its body AT the `class`
statement; the model builds `ClassDefn` at ingestion and executes nothing.
For a `creationPure` class that is invisible — methods, `pass`, docstrings
and literal attribute bindings can neither print nor raise. For any other
class it is a silently skipped effect, which is the one thing this project
never does, so the whole script refuses.

Found by pointing `tools/leanpy` at `class C: print("x")`: CPython printed
and the model did not, a WRONG ANSWER rather than a refusal. The closed
FUNCTION surface is unaffected — it makes no claim about module stdout,
and the one class-body effect that could reach a call's result, a
class-level `global`, is already tracked by `ClassDefn.hasGlobal`. -/
def classesCreationPure (m : Module) : Bool :=
  m.classes.all (·.creationPure)

/-- The stale-table guard: no suffix (nested-)assignment to ANY name some
function reads. Under the prefix view (`runScript`'s `mPre`) BOTH halves
of the old table-bound condition are hazards, so the condition is gone:
a prefix-bound name rebound by the suffix would read STALE from the
table inside a call (the suffix binding lands in the script's locals,
invisible to function frames), and a FRESH suffix global would resolve
to a fake `NameError` (the prefix view is always analysable). CPython
makes both module globals; leanpy refuses the script loudly. -/
def suffixConsistent (m : Module) (suffix : List Stmt) : Bool :=
  let reads := moduleGlobalReads m
  (Stmt.assignedNamesList suffix).all fun n => !reads.contains n

/-! ### The executor -/

mutual
  /-- Execute live-suffix statements: `print` statements intercepted,
  `while`/`if` run through control shells (mirroring `execWhile`/
  `execStmt` exactly) so prints work inside them, everything else
  delegated to `execStmt`. -/
  def execScriptStmts (m : Module) (fuel : Nat) (st : FrameState) :
      List Stmt → Run FrameState RFlow
    | ss =>
      match fuel with
      | 0 => .timeout
      | fuel + 1 =>
        match ss with
        | [] => .ok st .next
        | .exprStmt (.call (.name "print" _) args #[] Option.none _) _ :: rest =>
          -- Module-level shadows via `printUnshadowed`; a LIVE local
          -- shadow (a suffix `print = …` already executed — invisible to
          -- the prefix view's globals) via the locals probe, dynamically
          -- exact: CPython calls the shadow only once its binding ran.
          if printUnshadowed m && (Env.lookup st.locals "print").isNone then
            Run.bind (evalExprs m fuel st args.toList) fun st vs =>
            match strOfArgs vs with
            | some line =>
              execScriptStmts m fuel
                { st with world :=
                    { st.world with stdout := st.world.stdout ++ [line] } }
                rest
            | Option.none =>
              .unsupported "print() of a container or heap value is outside leanpy v0 (scalar str() only)"
          else
            .unsupported "a shadowed 'print' is outside leanpy v0"
        | .whileLoop test body orelse sp :: rest =>
          match orelse.toList with
          | [] =>
            Run.bind (execScriptWhile m fuel st test body.toList) fun st flow =>
            match flow with
            | .next => execScriptStmts m fuel st rest
            | .ret _ => .unsupported "'return' at module top level (CPython: SyntaxError at compile time)"
            | _ => .unsupported "loop flow escaped a top-level while"
          | _ :: _ =>
            -- no shell for while-else; delegate (prints inside stay loud)
            Run.bind (execStmt m fuel st (.whileLoop test body orelse sp))
              fun st flow => contFlow m fuel st flow rest
        | .ifStmt test body orelse _ :: rest =>
          Run.bind (evalExpr m fuel st test) fun st t =>
          Run.bind (Run.liftRes st (truthyH st.world.heap t)) fun st b =>
          Run.bind
            (if b then execScriptStmts m fuel st body.toList
             else execScriptStmts m fuel st orelse.toList) fun st flow =>
          match flow with
          | .next => execScriptStmts m fuel st rest
          | flow => .ok st flow   -- brk/cont escape to an enclosing shell
        | s :: rest =>
          Run.bind (execStmt m fuel st s) fun st flow =>
          contFlow m fuel st flow rest

  /-- Route a delegated statement's flow: `next` continues, loop flow
  escapes to an enclosing shell, `return` is the top-level refusal. -/
  def contFlow (m : Module) (fuel : Nat) (st : FrameState) (flow : RFlow)
      (rest : List Stmt) : Run FrameState RFlow :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match flow with
      | .next => execScriptStmts m fuel st rest
      | .ret _ => .unsupported "'return' at module top level (CPython: SyntaxError at compile time)"
      | flow => .ok st flow

  /-- The `execWhile` control shell over script statements (same test,
  same truthiness, same flow routing — body prints intercepted). -/
  def execScriptWhile (m : Module) (fuel : Nat) (st : FrameState)
      (test : Expr) (body : List Stmt) : Run FrameState RFlow :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      Run.bind (evalExpr m fuel st test) fun st t =>
      Run.bind (Run.liftRes st (truthyH st.world.heap t)) fun st b =>
      if b then
        Run.bind (execScriptStmts m fuel st body) fun st flow =>
        match flow with
        | .next | .cont => execScriptWhile m fuel st test body
        | .brk => .ok st .next
        | .ret v => .ok st (.ret v)
      else .ok st .next
end

/-- Run a whole script under a SEEDED CLOCK TRACE: boundary checks, then
the live suffix from the world G1-initialized over the PREFIX VIEW `mPre`
— the fold must see only the statements the live run skips, never the
suffix it is about to execute (the poisoning pass is retroactive, so a
whole-module fold clobbers prefix names the suffix rebinds/stores into:
the fib_loop/tt_script/list_script regression). `mPre` also threads
through the executor, so function frames resolve the same prefix globals.
The decided outcome's world carries the accumulated stdout.

`clock` is the trace `time.time()` consumes in order (pass 6,
docs/memory-model.md §the trace clock) — the script-mode counterpart of
`callFunctionClock`. It seeds the world AFTER `initWorld`, exactly as the
call boundary does: the G1 fold never reads the clock (a module-init
`time.time()` poisons its binding), so seeding before or after the fold
is the same world, and seeding after keeps the `runScript = runScriptClock
m []` equation definitional. -/
def runScriptClock (m : Module) (clock : List Int) (fuel : Nat) : Run World Unit :=
  let suffix := liveSuffix m.topLevel.toList
  if !classesCreationPure m then
    .unsupported "a class whose CREATION does something observable (an unrecognized base, a metaclass keyword, a decorator, or a class-level statement beyond methods/pass/docstring/literal attributes): CPython runs that at the `class` statement and the model executes no class body, so leanpy refuses rather than silently skip the effect"
  else if !defsBoundBefore m m.topLevel.toList then
    .unsupported "a top-level statement mentions a name this module defines LATER (`def`/`class`/namedtuple): CPython would raise NameError there, and the model's definition tables are position-independent, so leanpy refuses rather than run a definition that does not exist yet"
  else if !suffixConsistent m suffix then
    .unsupported "live top-level code rebinds a module global some function reads — outside leanpy v0 (the closed-function G1 table would go stale for calls, and a fresh live global would fake a NameError; ordered ModuleItem representation is the recorded fix)"
  else
    let mPre : Module :=
      { m with topLevel := (scriptNameBinding :: g1Prefix m.topLevel.toList).toArray }
    Run.toWorld <|
      Run.bind (execScriptStmts mPre fuel ⟨{ initWorld mPre with clock := clock }, []⟩ suffix)
        fun st flow =>
      match flow with
      | .next => .ok st ()
      | .ret _ => .unsupported "'return' at module top level (CPython: SyntaxError at compile time)"
      | .brk => .unsupported "'break' at module top level (CPython: SyntaxError at compile time)"
      | .cont => .unsupported "'continue' at module top level (CPython: SyntaxError at compile time)"

/-- Run a whole script on the EMPTY trace (`runScriptClock` at `[]`): any
reachable `time.time()` refuses with the loud fuel-independent underrun,
never a fabricated reading. -/
def runScript (m : Module) (fuel : Nat) : Run World Unit :=
  runScriptClock m [] fuel

end LeanModels.Python
