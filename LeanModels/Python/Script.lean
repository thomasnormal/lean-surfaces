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
  docstrings, and `pass` — is exactly what the G1 fold executed
  faithfully into `initWorld` (values, heaps, dict identities). The live
  run SKIPS it: top-level reads fall through locals to the very objects
  function bodies resolve, so identity and mutation stay shared.
* the SUFFIX — everything from the first other statement — runs LIVE
  (`execStmt`, plus the control shells below), binding into the script's
  locals. Suffix heap mutations (`tt[k] = v`) act on the shared world and
  are visible to calls; suffix NAME bindings are visible only at top
  level, and the G1 fold now POISONS post-boundary bindings
  (Semantics.lean), so a function-body read of one is loud, never stale.

Refusals — every one LOUD, never wrong:

* a function definition whose span does not precede every SUFFIX
  statement (a live statement could call it before CPython would have
  bound it);
* a suffix (nested-)assignment to a TABLE-BOUND name some function body
  reads (`funcGlobalReads`): the static table would go stale for calls
  (the ordered `ModuleItem` representation is the recorded fix);
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
    | .call f args _ _ => f.allNames ++ Expr.allNamesList args.toList
    | .list es _ => Expr.allNamesList es.toList
    | .tuple es _ => Expr.allNamesList es.toList
    | .subscript v i _ => v.allNames ++ i.allNames
    | .dict ks vs _ => Expr.allNamesList ks.toList ++ Expr.allNamesList vs.toList
    | .attribute v _ _ => v.allNames
    | .ifExp t b o _ => t.allNames ++ b.allNames ++ o.allNames
    | .slice v l u st _ => v.allNames ++ l.allNames ++ u.allNames ++ st.allNames
    | .genExp e t it ifs _ =>
      e.allNames ++ t.allNames ++ it.allNames ++ Expr.allNamesList ifs.toList
    | .unsupported .. => []

  /-- Elementwise `Expr.allNames`. -/
  def Expr.allNamesList : List Expr → List String
    | [] => []
    | e :: es => e.allNames ++ Expr.allNamesList es
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
    | .ifStmt t b o _ =>
      t.allNames ++ Stmt.allNamesList b.toList ++ Stmt.allNamesList o.toList
    | .exprStmt e _ => e.allNames
    | .yieldStmt e _ => e.allNames
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

/-- Every function AND class definition precedes every live-suffix
statement (a live statement could otherwise call/instantiate it before
CPython would have bound it). Flattened method spans sit inside their
class span, so the function half already covers them — the class check
adds the `class` line itself.

H4 exemption: a SYNTHESIZED genexp function (`<genexpr@n>` — ingestion's
lowering, Json.lean) is exempt. The hazard this guards against is a live
statement calling a name before CPython binds it, and such a name is
UNNAMEABLE in Python: its only call site is the expression it replaced,
where CPython builds the same implicit function at exactly that moment.
Recognized by the leading `<`, which no Python identifier can carry. -/
def defsBeforeLive (m : Module) (suffix : List Stmt) : Bool :=
  (m.functions.toList.all fun f =>
    f.name.startsWith "<" ||
      suffix.all fun s => f.span.endLineno < (stmtSpan s).lineno)
  && (m.classes.toList.all fun c =>
    suffix.all fun s => c.span.endLineno < (stmtSpan s).lineno)
where
  /-- The span of a statement (every constructor carries one last). -/
  stmtSpan : Stmt → Span
    | .ret _ sp | .assign _ _ sp | .augAssign _ _ _ sp
    | .whileLoop _ _ _ sp | .forStmt _ _ _ _ sp | .ifStmt _ _ _ sp
    | .exprStmt _ sp | .yieldStmt _ sp | .pass sp | .brk sp | .cont sp
    | .unsupported _ _ sp => sp

/-- The stale-table guard: no suffix (nested-)assignment to a TABLE-BOUND
name some function reads. -/
def suffixConsistent (m : Module) (suffix : List Stmt) : Bool :=
  let reads := moduleGlobalReads m
  (Stmt.assignedNamesList suffix).all fun n =>
    !(reads.contains n
        && (match lookupG (moduleGlobals m).1 n with
            | some (some _) => true
            | _ => false))

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
        | .exprStmt (.call (.name "print" _) args Option.none _) _ :: rest =>
          if printUnshadowed m then
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

/-- Run a whole script: boundary checks, then the live suffix from the
G1-initialized world with empty locals. The decided outcome's world
carries the accumulated stdout. -/
def runScript (m : Module) (fuel : Nat) : Run World Unit :=
  let suffix := liveSuffix m.topLevel.toList
  if !defsBeforeLive m suffix then
    .unsupported "a function defined after live top-level code is outside leanpy v0 (a live statement could call it before CPython binds it; the ordered ModuleItem representation is the recorded fix)"
  else if !suffixConsistent m suffix then
    .unsupported "live top-level code rebinds a module global some function reads — outside leanpy v0 (the closed-function G1 table would go stale for calls; ordered ModuleItem representation is the recorded fix)"
  else
    Run.toWorld <|
      Run.bind (execScriptStmts m fuel ⟨initWorld m, []⟩ suffix) fun st flow =>
      match flow with
      | .next => .ok st ()
      | .ret _ => .unsupported "'return' at module top level (CPython: SyntaxError at compile time)"
      | .brk => .unsupported "'break' at module top level (CPython: SyntaxError at compile time)"
      | .cont => .unsupported "'continue' at module top level (CPython: SyntaxError at compile time)"

end LeanModels.Python
