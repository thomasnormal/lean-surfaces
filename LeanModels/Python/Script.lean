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
* `print` of a container or heap value (its `repr` is not guessed);
* top-level `return`/`break`/`continue` (CPython compile-time
  SyntaxErrors the extractor happily ships).

The executor is FUELED like the mutual block and lives OUTSIDE it. It no
longer intercepts `print` at all: since 2026-08-13 `print` is an ordinary
builtin inside the interpreter (docs/memory-model.md §effects), so it
works in a function body, in a nested call, and inside any statement the
executor delegates — the shells exist only for the per-statement PUBLISH.
The `while`/`if` arms below mirror `execWhile`/`execStmt` exactly (test,
`truthyH`, flow routing), and `for k, v in d.items():` gets the shell
`execStmt` cannot express (the live entries re-read per step, a size
change the faithful `RuntimeError`) — the one that module-init execution
used to own. Every other statement runs through `execStmt`, so the tier
is the interpreter's.
-/

namespace LeanModels.Python

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
    | .assertStmt t m _ =>
      t.allNames ++ (m.map Expr.allNames).getD []
    -- del RECONCILED: a target is a mention (so `defsBoundBefore` orders
    -- a surviving `del f` after `def f` ends — refusal above it is loud)
    | .delStmt ns _ => ns.toList
    | .tryStmt b excName hnd _ _ =>
      excName :: Stmt.allNamesList b.toList ++ Stmt.allNamesList hnd.toList
    -- Pass 0 (§import forms): an import reads no in-module names (its
    -- bound names are the binding censuses' business, `Stmt.g1Binds`)
    | .importFrom .. => []
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
    -- del RECONCILED: a removal is a binding CHANGE — inside a delegated
    -- compound it is exactly as invisible to called functions as a
    -- mid-compound bind, so `scriptFlushCoherent` must see it
    | .delStmt ns _ => ns.toList
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
  | .raiseStmt _ _ sp | .tryStmt _ _ _ _ sp | .assertStmt _ _ sp
  | .importFrom _ _ _ sp | .delStmt _ sp
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
and refuses any other one loudly.

Pass 0 (docs/memory-model.md §import forms): a STRUCTURED
`Stmt.importFrom` is deliberately NOT kept in the view. Keeping it
would poison its names in the static table (`Stmt.g1Binds`
over-reports), and a poisoned entry REFUSES the read instead of
consulting the live view — which would break the guarded fallback's
whole point (quopri's handler binds `a2b_qp = None` as a live global,
and later top-level reads must resolve through `World.globals`). This
opens no clock hole: in Pass 0 an `importFrom` NEVER binds (it raises
before any binding; the handler's rebinds land in the live view, which
`clockRecvOk` already consults), and program mode's `moduleClockOk`
census runs over the REAL top level, where the new `g1Binds` arms make
`from x import time` and any top-level star import fail it. -/
def scriptImports (m : Module) : List Stmt :=
  m.topLevel.toList.filter fun s =>
    match s with
    | .unsupported "Import" _ _ | .unsupported "ImportFrom" _ _ => true
    | _ => false

/-- Names the module's BENIGN-whitelisted imports bind (`time`, `count`,
`namedtuple`). They bind STATICALLY — never in the script frame's locals
— so the module-scope `del` arm has nothing to remove and refuses
LOUDLY: CPython's `import time; del time` succeeds silently, and a
faithful `NameError` here would be a wrong answer
(docs/backlog.md §`del` RECONCILED, measured row 3). -/
def benignImportNames (m : Module) : List String :=
  m.topLevel.toList.filterMap fun s =>
    match s with
    | .unsupported "Import" text _ | .unsupported "ImportFrom" text _ =>
      (benignImportBinds text).map Prod.fst
    | _ => Option.none

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

/-- The refusal a top-level rebinding of a builtin or a
`def`/`class`/namedtuple name earns: those resolution arms fire BEFORE
the live module globals, so the shadow would be silently ignored. -/
def scriptRebindMsg : String :=
  "a top-level statement rebinds a builtin or a name this module defines by 'def'/'class'/namedtuple: those resolution arms fire BEFORE the live module globals, so the shadow would be silently ignored"


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
    -- 2026-08-13: the general `for` got its own shell too, so only a
    -- `for … else` (which has none) is still delegated wholesale
    | .forStmt t _ b o _ =>
      if o.isEmpty then Stmt.scriptMidAssignsList b.toList
      else
        targetBoundNames t ++ Stmt.assignedNamesList b.toList
          ++ Stmt.assignedNamesList o.toList
    -- 2026-08-13: `try` got a shell too; a `while … else` is now the only
    -- compound the executor still delegates wholesale
    | .tryStmt b _ h _ _ =>
      Stmt.scriptMidAssignsList b.toList ++ Stmt.scriptMidAssignsList h.toList
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
          .unsupported scriptRebindMsg
  termination_by structural fuel

  /-- Execute ONE top-level statement. `if`, `while` (without `else`) and
  the `for … in d.items():` loop run through CONTROL SHELLS mirroring
  `execStmt`/`execWhile` exactly, so the per-statement PUBLISH happens
  inside them; a whitelisted `import` is skipped (it binds through the
  static view, and running one observes nothing); everything else is
  delegated to `execStmt`, so the tier is the interpreter's. -/
  def execScriptOne (m : Module) (fuel : Nat) (st : FrameState) (s : Stmt) :
      Run FrameState RFlow :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match s with
      | .whileLoop test body orelse sp =>
        if orelse.isEmpty then execScriptWhile m fuel st test body.toList
        else
          -- no shell for while-else; delegate wholesale
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
      | .forStmt target iter body orelse _ =>
        -- The GENERAL `for` shell (2026-08-13), mirroring `execStmt`'s
        -- dispatch arm for arm so the TIER is unchanged and only the
        -- PUBLISH granularity differs: body statements run through
        -- `execScriptStmts`, so a function called from inside the loop
        -- sees the loop's own bindings. Delegating the whole statement
        -- was the last seam in the unified pipeline
        -- (`scriptFlushCoherent`).
        if orelse.isEmpty then
          Run.bind (evalExpr m fuel st iter) fun st it =>
          match it with
          | .listV xs => execScriptFor m fuel st target xs.toList body.toList
          | .tuple xs => execScriptFor m fuel st target xs.toList body.toList
          | .ntuple _ _ xs => execScriptFor m fuel st target xs.toList body.toList
          | .str t => execScriptFor m fuel st target (strCharVals t) body.toList
          | .rangeV lo hi step =>
            Run.bind (Run.liftRes st (rangeVals lo hi step)) fun st xs =>
            execScriptFor m fuel st target xs body.toList
          | .ref a => execScriptForList m fuel st target a 0 body.toList
          | v => .exn st (.typeError s!"'{v.typeName}' object is not iterable")
        else .unsupported "'for … else' is outside the v0 tier"
      | .tryStmt body excName handler tryUnsupported sp =>
        -- The `try`/`except` shell (2026-08-13): the admission is
        -- `execStmt`'s verbatim — the same `tryUnsupported` reason, the
        -- same shadowing refusal, the same statically-first handler-class
        -- resolution, the same RETAINED-STATE covenant (a matching `.user`
        -- exn runs the handler from the state the raise left, no
        -- rollback) — and only the body and handler statements move to
        -- `execScriptStmts`, so their bindings publish per statement.
        (match tryUnsupported with
         | some reason =>
           .unsupported s!"try/except uses unsupported features ({reason}) — outside the tier (docs/memory-model.md §exceptions)"
         | Option.none =>
           if (Env.lookup st.locals excName).isSome
               || (lookupG (moduleGlobals m).1 excName).isSome
               || (Env.lookup st.world.globals excName).isSome
               || (findFunction m excName).isSome then
             .unsupported s!"'except {excName}:': the name is shadowed by a local/global/def binding — outside the tier (docs/memory-model.md §exceptions)"
           else
             match findClass m excName with
             | Option.none =>
               -- Pass 0 (docs/memory-model.md §import forms): the SECOND
               -- resolution site of the pinned two-name table — execStmt's
               -- arm verbatim, only the body/handler statements moving
               -- through `execScriptStmts` so their bindings publish per
               -- statement (the quopri shape: the handler's `a2b_qp =
               -- None` must be a live global for later top-level reads).
               if importErrorHandlerMatch excName then
                 match execScriptStmts m fuel st body.toList with
                 | .ok st' flow => .ok st' flow
                 | .exn st' e =>
                   (match e with
                    | .importError _ => execScriptStmts m fuel st' handler.toList
                    | e => .exn st' e)
                 | .timeout => .timeout
                 | .unsupported msg => .unsupported msg
               else
                 .unsupported s!"'except {excName}:': only an admitted exception class (`class N(Exception): pass`) or the pinned import-error names (`ImportError`/`ModuleNotFoundError` — docs/memory-model.md §import forms) can be matched — wider builtin-name matching is outside the tier (docs/memory-model.md §exceptions)"
             | some (ci, c) =>
               if !c.isExc then
                 .unsupported s!"'except {excName}:': class '{excName}' is not an admitted exception class — outside the tier (docs/memory-model.md §exceptions)"
               else
                 match execScriptStmts m fuel st body.toList with
                 | .ok st' flow => .ok st' flow
                 | .exn st' e =>
                   (match e with
                    | .user cid _ =>
                      if cid == ci then execScriptStmts m fuel st' handler.toList
                      else .exn st' e
                    | e => .exn st' e)
                 | .timeout => .timeout
                 | .unsupported msg => .unsupported msg)
      | .unsupported "Import" text sp =>
        if (benignImportBinds text).isSome then .ok st .next
        else execStmt m fuel st (.unsupported "Import" text sp)
      | .unsupported "ImportFrom" text sp =>
        if (benignImportBinds text).isSome then .ok st .next
        else execStmt m fuel st (.unsupported "ImportFrom" text sp)
      | .delStmt names _ =>
        -- The MODULE-scope `del` arm (docs/backlog.md §`del` RECONCILED
        -- with the one pipeline; docs/memory-model.md §the del
        -- statement). By §the publish the frame's locals ARE the module
        -- globals and the one pipeline keeps them COMPLETE, so a locals
        -- HIT removes exactly CPython's module global (published after
        -- the statement like any bind) and a MISS is decided in CPython's
        -- order of authority: a dunder target is loud (the model resolves
        -- dunder reads statically — and CPython's `del __name__` UNCOVERS
        -- builtins' own `__name__`, measured); a benign-import name is
        -- loud (it binds statically, so the removal has nothing to act
        -- on); a `def`/`class`/namedtuple/alias name is loud (a static
        -- table entry — the TRAILING position is rewritten away at
        -- ingestion, so reaching here means a non-trailing del of a
        -- definition); anything else is the faithful `NameError`, with
        -- the PARTIAL left-to-right effect retained on the raise
        -- (`del x, nosuch` really removes `x` — the recorded row 5).
        -- Deletion never consults builtins: CPython's `del len` is the
        -- same `NameError` (measured), so no `isPyBuiltinName` gate.
        (match delNames st.locals names.toList with
         | (env, Option.none) => .ok { st with locals := env } .next
         | (env, some n) =>
           if dunderShaped n then
             .unsupported s!"'del {n}': deleting a module dunder is outside the tier (the model resolves dunder reads statically; CPython's removal uncovers the BUILTINS module's binding — docs/backlog.md §del RECONCILED)"
           else if (benignImportNames m).contains n then
             .unsupported s!"'del {n}': the name is bound by a whitelisted import, which the model binds statically — outside the tier (docs/backlog.md §del RECONCILED)"
           else if (findFunction m n).isSome || (findClass m n).isSome
               || m.namedtuples.any (·.name == n) then
             .unsupported s!"'del {n}': a module 'def'/'class'/namedtuple name is a static table entry; only a TRAILING del of it is admitted (rewritten at ingestion — docs/backlog.md §del RECONCILED)"
           else .exn { st with locals := env } (.nameError n))
      | s => execStmt m fuel st s
  termination_by structural fuel

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
               .unsupported scriptRebindMsg)
          | .exn e => .exn st e
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
        else .ok st .next
      | _ => .unsupported "internal: items-loop receiver is not a dict (report this)"
  termination_by structural fuel

  /-- `execFor`'s VALUE-sequence cursor as a shell (immutable sources:
  tuples, namedtuples, boundary lists, str code points, materialized
  ranges — the snapshot IS the live semantics for all of them). -/
  def execScriptFor (m : Module) (fuel : Nat) (st : FrameState) (target : Expr)
      (xs : List RVal) (body : List Stmt) : Run FrameState RFlow :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match xs with
      | [] => .ok st .next
      | x :: rest =>
        Run.bind (Run.liftRes st (assignToH st.world.heap st.locals target x))
          fun st env1 =>
        match publishScriptGlobals m ⟨st.world, env1⟩ with
        | Option.none => .unsupported scriptRebindMsg
        | some st =>
          Run.bind (execScriptStmts m fuel st body) fun st flow =>
          match flow with
          | .next | .cont => execScriptFor m fuel st target rest body
          | .brk => .ok st .next
          | .ret v => .ok st (.ret v)
  termination_by structural fuel

  /-- `execForList`'s LIVE INDEX CURSOR as a shell — the object is re-read
  each step, so in-place mutation, growth and `pop`-shrinkage during
  iteration are observed exactly as CPython's listiterator observes them.
  The referent dispatch, and every one of its refusals, is
  `execForList`'s verbatim. -/
  def execScriptForList (m : Module) (fuel : Nat) (st : FrameState) (target : Expr)
      (a : Addr) (i : Nat) (body : List Stmt) : Run FrameState RFlow :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      match Heap.get? st.world.heap a with
      | some (.list xs) =>
        if i < xs.size then
          Run.bind (Run.liftRes st (assignToH st.world.heap st.locals target (xs.getD i .none)))
            fun st env1 =>
          match publishScriptGlobals m ⟨st.world, env1⟩ with
          | Option.none => .unsupported scriptRebindMsg
          | some st =>
            Run.bind (execScriptStmts m fuel st body) fun st flow =>
            match flow with
            | .next | .cont => execScriptForList m fuel st target a (i + 1) body
            | .brk => .ok st .next
            | .ret v => .ok st (.ret v)
        else .ok st .next
      | some (.dict _ _) =>
        .unsupported "'for' over a dict is outside the tier (live dict iteration is deliberately NOT in the inventory — no snapshot shortcut; docs/memory-model.md)"
      | some (.instance _ _) =>
        .exn st (.typeError "'object' object is not iterable")
      | some (.generator ..) =>
        if moduleGenFree m then
          .unsupported "internal: a generator object in a module with no generator defs (heap well-formedness violation — report this)"
        else execScriptForGen m fuel st target a body
      | some (.closure ..) =>
        .unsupported "internal: a list cursor over a function object (report this)"
      | some (.pyset _) =>
        .unsupported "internal: a list cursor over a set (report this)"
      | Option.none => .unsupported "internal: a dangling heap address (report this)"
  termination_by structural fuel

  /-- `execForGen`'s LAZY cursor as a shell: one `stepIter` per element, so
  the generator's own body effects interleave exactly as they do under the
  interpreter's loop. -/
  def execScriptForGen (m : Module) (fuel : Nat) (st : FrameState) (target : Expr)
      (a : Addr) (body : List Stmt) : Run FrameState RFlow :=
    match fuel with
    | 0 => .timeout
    | fuel + 1 =>
      Run.bind (Run.withLocals st.locals (stepIter m fuel st.world a)) fun st r =>
      match r with
      | Option.none => .ok st .next
      | some v =>
        Run.bind (Run.liftRes st (assignToH st.world.heap st.locals target v))
          fun st env1 =>
        match publishScriptGlobals m ⟨st.world, env1⟩ with
        | Option.none => .unsupported scriptRebindMsg
        | some st =>
          Run.bind (execScriptStmts m fuel st body) fun st flow =>
          match flow with
          | .next | .cont => execScriptForGen m fuel st target a body
          | .brk => .ok st .next
          | .ret v => .ok st (.ret v)
  termination_by structural fuel

  /-- The `execWhile` control shell over script statements (same test,
  same truthiness, same flow routing — body bindings published per
  statement). -/
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
  termination_by structural fuel
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
    .unsupported "a class whose CREATION does something observable (an unrecognized base, a metaclass keyword, a decorator on the class OR on one of its methods, or a class-level statement beyond undecorated methods/pass/docstring/literal attributes): CPython runs that at the `class` statement and the model executes no class body, so leanpy refuses rather than silently skip the effect"
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
