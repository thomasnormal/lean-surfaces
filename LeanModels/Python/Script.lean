import LeanModels.Python.Semantics

/-!
# `leanpy` — module-level script execution (docs/backlog.md, owner-directed)

Run a whole current-tier Python FILE under the Lean semantics: execute the
module's top level in one world, collecting `print` output into
`World.stdout` (effects are data — docs/memory-model.md §effects). The
runner boundary (Main.lean `--script`) maps the outcome to stdout + an
exit status; the differential side is `harness/script_corpus.py` (stdout +
exit code against the pinned CPython 3.9, first-unsupported-construct
telemetry).

## THE ONE PIPELINE (2026-08-12 — docs/memory-model.md §the one pipeline)

Until this pass leanpy ran a program through TWO pipelines: the G1 fold
built `initWorld` from a *prefix* of the top level, and the script
executor ran the *suffix*. Every soundness hole the completeness survey
found was the same shape — the fold's approximation (skip, poison, never
print) meeting the program surface's demand that every effect be
observable, in order. Three of them were WRONG ANSWERS rather than
refusals (a skipped class body, a rolled-back `x = talk()`, a swallowed
`x = 1 // 0`), each closed by one more guard on top of the split.

The split is now gone. **A program's top level is executed, statement by
statement, by this file's executor — all of it — and its bindings are
written to `World.globals`, the live view that function frames read
through the poisoned/absent arms.** `initWorld` is never called in script
mode: nothing is folded, so nothing can be skipped, rolled back, or go
stale, and `initNothingSkipped`/`suffixConsistent` (and the whole
prefix/suffix boundary) are deleted rather than tightened.

### How a live binding becomes visible to a call

The covenant that keeps world-symbolic theorems provable is that function
frames resolve module names STATICALLY FIRST (`moduleGlobals`), and that
table cannot contain execution results. The unification therefore does not
touch resolution at all — it removes the static table from the picture by
threading a module VIEW (`scriptView`) whose top level carries no program
statements:

* `scriptNameBinding` — `__name__ = "__main__"`, the runner-boundary
  global (`isModuleDunder` fires BEFORE the live-view consult, so this one
  has to be static);
* `scriptViewMarker` — an unnameable top-level `def` whose body calls
  `enumerate`, which turns OFF both module-level shortcuts
  (`topLevelDefFree`, `moduleGenFree`) so every arm guarded by them takes
  its DYNAMIC, faithful path: a module-level `lambda` bound by executed
  code is a live `Obj.closure` the heap-free shortcut would refuse to
  call, and a program's own `enumerate`/`count` calls are invisible to a
  view carrying no program statement;
* the module's IMPORT statements verbatim — the benign-import whitelist
  binds `time` POISONED there, which is both the loud refusal for a bare
  `time` and the precondition of the trace clock's census
  (`moduleClockOk`). Nothing else about them is executed.

Every other module global is then statically ABSENT, and that arm already
consults `World.globals` before deciding: hit → the live value, miss →
the faithful `NameError` (the view is trivially `analysable`). So
resolution is SEQUENTIALLY EXACT for free — a name is visible exactly once
the statement that binds it has run, which is what CPython does and what
the per-statement prefix views of module-init execution had to be built by
hand to imitate.

### The publish

`execStmt` binds into frame LOCALS, and CPython runs a module's top level
in a frame whose locals ARE its globals. After every statement the
executor re-establishes exactly that identification
(`publishScriptGlobals`: `World.globals := st.locals`, one shared list,
no copy). Top-level reads hit the frame, function frames hit the globals,
and both are the same binding. A name failing `initBindable` (a builtin,
or a `def`/`class`/namedtuple name — arms that fire BEFORE the live view)
refuses loudly, never a silently ignored shadow.

Keeping the frame's locals rather than draining them is load-bearing:
`x += 1` at module level must read the module global, while inside a
FUNCTION the same statement is a local by CPython's compile-time rule
(`+=` is a binding, so an unbound one is `UnboundLocalError`, never a
global read) — which is why `execStmt`'s augmented-assignment arm reads
locals only. The identification makes module scope come out right through
that very arm.

The publish is per STATEMENT, so a compound statement the executor
DELEGATES wholesale to `execStmt` (a `for`, a `try`, a `while … else`)
holds its inner bindings in the frame until it finishes — invisible to a
function called from inside it. `scriptFlushCoherent` refuses exactly
that: no name assigned inside a delegated compound may be a name some
function body reads. It is the narrow residue of the old
`suffixConsistent`, which refused this for the WHOLE suffix.

Refusals — every one LOUD, never wrong:

* a top-level statement mentioning a name the module binds by
  `def`/`class`/namedtuple LATER (`defsBoundBefore`): CPython raises
  `NameError` there and the model's definition tables are
  position-independent;
* a class whose CREATION does something observable
  (`classesCreationPure`);
* a mid-statement binding a function reads (`scriptFlushCoherent`);
* a top-level rebinding of a builtin/`def`/`class`/namedtuple name;
* `print` of containers/heap values (repr subtleties), a shadowed
  `print`, `print` in expression position or inside a function body (the
  effect must thread the mutual block to land there — this keeps the
  proof-relevant interpreter untouched);
* top-level `return`/`break`/`continue` (CPython compile-time
  SyntaxErrors the extractor happily ships).

The executor is FUELED like the mutual block and lives OUTSIDE it. The
`while`/`if` arms below are CONTROL SHELLS mirroring `execWhile`/
`execStmt` exactly (test, `truthyH`, flow routing) so `print` works
inside top-level loops, and `for k, v in d.items():` gets the shell
`execStmt` cannot express (the live entries re-read per step, a size
change the faithful `RuntimeError`) — the one that module-init execution
used to own. Every other statement runs through `execStmt`, so the tier
is the interpreter's; a general top-level `for` is still delegated
(prints inside one are loud — extend the shell when the corpus wants it).
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

/-! ### The ordering admission -/

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
the ordering admission (which reads `m.topLevel`, not the script view).
The other module dunders (`__file__`, `__doc__`, `__spec__`, …) keep the
loud refusal: only `__name__` has a value the runner boundary fixes. -/
def scriptNameBinding : Stmt :=
  let sp : Span := { lineno := 0, colOffset := 0, endLineno := 0, endColOffset := 0 }
  .assign #[.name "__name__" sp] (.constant (.str "__main__") sp) sp

/-! ### The script view (THE ONE PIPELINE — see the header) -/

/-- The unnameable top-level `def` the script view carries so that the two
module-level SHORTCUTS both read FALSE. Each is a claim that some arm is
unreachable in a well-behaved module, and each exists to keep `worldInv`
free of a heap-side invariant — a closed-function concern script mode does
not share. Turning both off makes every such arm take its DYNAMIC path,
which is the FAITHFUL one:

* `topLevelDefFree` (this is a `def`) — with it true, a `.ref` reached
  through the live globals answers a fake `'dict' object is not callable`
  instead of dispatching the closure. Module-level `lambda`s are exactly
  such live closures under the one pipeline (`padrow = lambda …` in
  sunfish's padding loop).
* `moduleGenFree` (the body calls `enumerate`) — the script view carries
  no program statement, so the module's own `enumerate`/`count` calls are
  invisible to it, and the generator arms would refuse a real `for i, c in
  enumerate(s):` with `internal: … report this`.

The leading `<` makes the name unnameable in Python (the synthesized
genexp precedent), so poisoning it in the fold cannot shadow anything, and
the body is never executed — only walked by the two predicates. -/
def scriptViewMarker : Stmt :=
  let sp : Span := { lineno := 0, colOffset := 0, endLineno := 0, endColOffset := 0 }
  .defStmt "<script>" #[] true true false false
    #[.exprStmt (.call (.name "enumerate" sp) #[] #[] Option.none sp) sp] #[] sp

/-- The module's `import` statements, verbatim. The script view keeps
them so the BENIGN-IMPORT whitelist still binds `time` POISONED (the
loud refusal for a bare `time`, and the precondition of the trace
clock's `moduleClockOk` census); the executor skips a whitelisted import
and refuses any other one loudly. -/
def scriptImports (m : Module) : List Stmt :=
  m.topLevel.toList.filter fun s =>
    match s with
    | .unsupported "Import" _ _ | .unsupported "ImportFrom" _ _ => true
    | _ => false

/-- THE SCRIPT VIEW: the module frames resolve names against while a
PROGRAM runs. Its top level carries no program statement, so
`moduleGlobals` values only `__name__` and every module global is
statically ABSENT — and that arm consults `World.globals`, the live view
the executor writes, before deciding the faithful `NameError`. Sequential
visibility is then exact by construction (a name resolves once its
statement has run), which is what the module-init pipeline's
per-statement prefix views had to imitate by hand.

`m.functions`/`m.classes`/`m.namedtuples` are UNTOUCHED: definitions stay
position-independent tables and `defsBoundBefore` is what makes that
agree with CPython's sequential binding. -/
def scriptView (m : Module) : Module :=
  { m with topLevel :=
      (scriptNameBinding :: scriptViewMarker :: scriptImports m).toArray }

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

/-! ### The publish (a module frame's locals ARE its globals) -/

/-- PUBLISH the script frame's locals as the module's globals. CPython
runs a module's top level in a frame whose locals *are* its globals; the
model keeps two fields, so the identification is re-established after
every statement — one list, shared, no copy.

Keeping the frame's own locals (rather than draining them into globals)
is load-bearing beyond tidiness: `x += 1` at module level must read the
module global, while INSIDE a function the same statement is always a
local by CPython's compile-time rule (`+=` is a binding, so an unbound
one is `UnboundLocalError`, never a global read) — which is why
`execStmt`'s augmented-assignment arm reads locals only. Identifying the
two envs makes the module-scope reading come out right through the very
same arm.

`none` = a name failing `initBindable` (a builtin, or a
`def`/`class`/namedtuple name): those resolution arms fire BEFORE the
live globals, so such a shadow would be silently ignored — loud
instead. -/
def publishScriptGlobals (m : Module) (st : FrameState) : Option FrameState :=
  if st.locals.all (fun p => initBindable m p.1) then
    some { st with world := { st.world with globals := st.locals } }
  else Option.none

/-! ### The mid-statement coherence guard -/

/-- Is this the `for k, v in d.items():` shape the executor runs through
its own shell (so its body statements flush per statement)? -/
def isItemsFor : Stmt → Bool
  | .forStmt _ (.call (.attribute _ "items" _) #[] #[] Option.none _) _ orelse _ =>
      orelse.isEmpty
  | _ => false

mutual
  /-- Names a top-level statement binds MID-STATEMENT: inside a compound
  statement the executor DELEGATES wholesale to `execStmt`, whose
  bindings sit in frame locals until the statement finishes. Shell-run
  statements (`if`, `while` without `else`, the items `for`) recurse —
  their bodies flush per statement — and a LEAF statement contributes
  nothing, because its own binding lands before anything can read it. -/
  def Stmt.scriptMidAssigns : Stmt → List String
    | .ifStmt _ b o _ =>
      Stmt.scriptMidAssignsList b.toList ++ Stmt.scriptMidAssignsList o.toList
    | .whileLoop _ b o _ =>
      if o.isEmpty then Stmt.scriptMidAssignsList b.toList
      else Stmt.assignedNamesList b.toList ++ Stmt.assignedNamesList o.toList
    -- the items shell publishes its TARGET before the body runs, so the
    -- loop variables are globals from the first body statement on
    | .forStmt t (.call (.attribute _ "items" _) #[] #[] Option.none _) b o _ =>
      if o.isEmpty then Stmt.scriptMidAssignsList b.toList
      else
        targetBoundNames t ++ Stmt.assignedNamesList b.toList
          ++ Stmt.assignedNamesList o.toList
    | .forStmt t _ b o _ =>
      targetBoundNames t ++ Stmt.assignedNamesList b.toList
        ++ Stmt.assignedNamesList o.toList
    | .tryStmt b _ h _ _ =>
      Stmt.assignedNamesList b.toList ++ Stmt.assignedNamesList h.toList
    | _ => []

  /-- Elementwise `Stmt.scriptMidAssigns`. -/
  def Stmt.scriptMidAssignsList : List Stmt → List String
    | [] => []
    | s :: ss => s.scriptMidAssigns ++ Stmt.scriptMidAssignsList ss
end

/-- The narrow residue of the old `suffixConsistent`: the flush is per
STATEMENT, so a name bound INSIDE a delegated compound statement is
invisible to a function called from inside that same statement (locals
are not globals until the statement ends). Refuse exactly that overlap —
never the whole live top level, which is what the prefix/suffix split had
to refuse. -/
def scriptFlushCoherent (m : Module) : Bool :=
  let reads := moduleGlobalReads m
  (Stmt.scriptMidAssignsList m.topLevel.toList).all fun n => !reads.contains n

/-! ### The executor -/

mutual
  /-- Execute top-level statements, FLUSHING the frame's locals into the
  world's globals after each one (the header's §the flush: a top-level
  binding IS a global, so a call made by a later statement reads exactly
  what this one bound). Flow routing: `next` continues, `break`/
  `continue` escape to an enclosing shell, `return` is the top-level
  refusal. -/
  def execScriptStmts (m : Module) (fuel : Nat) (st : FrameState) :
      List Stmt → Run FrameState RFlow
    | [] => .ok st .next
    | s :: rest =>
      match fuel with
      | 0 => .timeout
      | fuel + 1 =>
        Run.bind (execScriptOne m fuel st s) fun st flow =>
        match publishScriptGlobals m st with
        | some st =>
          (match flow with
           | .next => execScriptStmts m fuel st rest
           | .ret _ => .unsupported "'return' at module top level (CPython: SyntaxError at compile time)"
           | flow => .ok st flow)
        | Option.none =>
          .unsupported "a top-level statement rebinds a builtin or a name this module defines by 'def'/'class'/namedtuple: those resolution arms fire BEFORE the live module globals, so the shadow would be silently ignored"

  /-- Execute ONE top-level statement. `print` is intercepted; `if`,
  `while` (without `else`) and the `for … in d.items():` loop run through
  CONTROL SHELLS mirroring `execStmt`/`execWhile` exactly, so prints and
  the per-statement flush work inside them; a whitelisted `import` is
  skipped (it binds through the static view, and running one observes
  nothing); everything else is delegated to `execStmt`, so the tier is
  the interpreter's. -/
  def execScriptOne (m : Module) (fuel : Nat) (st : FrameState) (s : Stmt) :
      Run FrameState RFlow :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match s with
      | .exprStmt (.call (.name "print" _) args #[] Option.none _) _ =>
        -- Module-level shadows via `printUnshadowed`; a LIVE shadow (a
        -- top-level `print = …` already executed) via the frame probes,
        -- dynamically exact: CPython calls the shadow only once its
        -- binding ran. (`initBindable` refuses that binding at the
        -- flush, so the probes are belt and braces.)
        if printUnshadowed m && (Env.lookup st.locals "print").isNone
            && (Env.lookup st.world.globals "print").isNone then
          Run.bind (evalExprs m fuel st args.toList) fun st vs =>
          match strOfArgs vs with
          | some line =>
            .ok { st with world :=
                    { st.world with stdout := st.world.stdout ++ [line] } } .next
          | Option.none =>
            .unsupported "print() of a container or heap value is outside leanpy (scalar str() only)"
        else
          .unsupported "a shadowed 'print' is outside leanpy"
      | .whileLoop test body orelse sp =>
        if orelse.isEmpty then execScriptWhile m fuel st test body.toList
        else
          -- no shell for while-else; delegate (prints inside stay loud)
          execStmt m fuel st (.whileLoop test body orelse sp)
      | .ifStmt test body orelse _ =>
        Run.bind (evalExpr m fuel st test) fun st t =>
        Run.bind (Run.liftRes st (truthyH st.world.heap t)) fun st b =>
        if b then execScriptStmts m fuel st body.toList
        else execScriptStmts m fuel st orelse.toList
      | .forStmt target (.call (.attribute d "items" _) #[] #[] Option.none _)
          body orelse _ =>
        if orelse.isEmpty then
          Run.bind (evalExpr m fuel st d) fun st dv =>
          match dv with
          | .ref a =>
            (match Heap.get? st.world.heap a with
             | some (.dict entries _) =>
               execScriptItems m fuel st a entries.size 0 target body.toList
             | _ =>
               .unsupported "'.items()' on a non-dict receiver is outside the tier (docs/memory-model.md §the one pipeline)")
          | _ =>
            .unsupported "'.items()' on a non-dict receiver is outside the tier (docs/memory-model.md §the one pipeline)"
        else .unsupported "'for … else' at module top level is outside the tier"
      | .unsupported "Import" text sp =>
        if (benignImportBinds text).isSome then .ok st .next
        else execStmt m fuel st (.unsupported "Import" text sp)
      | .unsupported "ImportFrom" text sp =>
        if (benignImportBinds text).isSome then .ok st .next
        else execStmt m fuel st (.unsupported "ImportFrom" text sp)
      | s => execStmt m fuel st s

  /-- The `for target in d.items():` control shell — CPython's dict_items
  iterator: the LIVE entries re-read per step, a SIZE change the faithful
  `RuntimeError` (value updates visible mid-iteration; H1 acceptance
  row 10). `n` is the size at iterator creation. This is the one `for`
  `execStmt` cannot express; module-init execution owned it before the
  one pipeline, and the shipped sunfish padding loop is its target. -/
  def execScriptItems (m : Module) (fuel : Nat) (st : FrameState)
      (a : Addr) (n : Nat) (i : Nat) (target : Expr) (body : List Stmt) :
      Run FrameState RFlow :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match Heap.get? st.world.heap a with
      | some (.dict entries _) =>
        if entries.size ≠ n then
          .exn st (.runtimeError "dictionary changed size during iteration")
        else if hlt : i < entries.size then
          match assignToH st.world.heap st.locals target
              (.tuple #[entries[i].1, entries[i].2]) with
          | .ok env0 =>
            (match publishScriptGlobals m ⟨st.world, env0⟩ with
             | some st =>
               Run.bind (execScriptStmts m fuel st body) fun st flow =>
               (match flow with
                | .next | .cont => execScriptItems m fuel st a n (i + 1) target body
                | .brk => .ok st .next
                | .ret v => .ok st (.ret v))
             | Option.none =>
               .unsupported "a top-level statement rebinds a builtin or a name this module defines by 'def'/'class'/namedtuple: those resolution arms fire BEFORE the live module globals, so the shadow would be silently ignored")
          | .exn e => .exn st e
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
        else .ok st .next
      | _ => .unsupported "internal: items-loop receiver is not a dict (report this)"

  /-- The `execWhile` control shell over script statements (same test,
  same truthiness, same flow routing — body prints intercepted, body
  bindings flushed per statement). -/
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

/-- Run a whole script under a SEEDED CLOCK TRACE: the three boundary
admissions, then THE ONE PIPELINE — every top-level statement executed,
in order, from an EMPTY world, against the `scriptView` (see the header).
`initWorld` is not called: nothing is folded, so nothing can be skipped,
rolled back, or read stale. The decided outcome's world carries the
accumulated stdout.

`clock` is the trace `time.time()` consumes in order (pass 6,
docs/memory-model.md §the trace clock) — the script-mode counterpart of
`callFunctionClock`, seeded into the starting world, which keeps the
`runScript = runScriptClock m []` equation definitional. -/
def runScriptClock (m : Module) (clock : List Int) (fuel : Nat) : Run World Unit :=
  if !classesCreationPure m then
    .unsupported "a class whose CREATION does something observable (an unrecognized base, a metaclass keyword, a decorator, or a class-level statement beyond methods/pass/docstring/literal attributes): CPython runs that at the `class` statement and the model executes no class body, so leanpy refuses rather than silently skip the effect"
  else if !defsBoundBefore m m.topLevel.toList then
    .unsupported "a top-level statement mentions a name this module defines LATER (`def`/`class`/namedtuple): CPython would raise NameError there, and the model's definition tables are position-independent, so leanpy refuses rather than run a definition that does not exist yet"
  else if !scriptFlushCoherent m then
    .unsupported "a compound top-level statement the executor delegates wholesale (a 'for', a 'try', a 'while … else') binds a name some function body reads: top-level bindings become module globals only when the statement ENDS, so a call made from inside it would read that name stale — a control shell for the statement is the recorded fix"
  else
    Run.toWorld <|
      Run.bind
        (execScriptStmts (scriptView m) fuel
          ⟨{ heap := #[], globals := [], stdout := [], clock := clock }, []⟩
          m.topLevel.toList)
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
