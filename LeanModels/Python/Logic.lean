import Lean
import LeanModels.Python.Json
import LeanModels.Python.Semantics

/-!
# Spec layer (`LeanModels.Python`)

The bridge from extracted programs to theorems, per `docs/DESIGN.md`:

* **`ToExpr` instances** for `Span` and every AST type, so elaboration-time
  code can quote a parsed `Module` as a literal Lean term. All instances are
  derived — the core `deriving ToExpr` handler on this toolchain handles the
  nested inductives (`Expr`/`Stmt` recurse through `Array`) fine.
* **`load_program <ident> from "<path>.json"`** — a command elaborator that
  reads an envelope JSON at *elaboration time* (path relative to the package
  root, i.e. the `lake build` cwd), parses it with `Json.lean`, and defines
  `<ident> : Module` as a **literal term**. It is never a runtime parse of an
  embedded string: proofs can unfold `<ident>` (e.g. `simp [tri]`, `unfold
  tri`, or plain kernel reduction via `rfl`/`decide`-style closed evaluation).
* **`#print_program <ident>`** — logs the `Repr` of a loaded program.
* **`CallsTo`** — the partial-correctness call relation (normative signature).
* **`@[spec]`** — the attribute for registered specification lemmas. On this
  toolchain it is core Lean's own `spec` attribute (the name is taken by the
  `mvcgen` spec registry, which also accepts plain simp-shaped theorems), so
  DESIGN.md's surface syntax works verbatim; see the section comment at the
  bottom of this file for details and the recorded deviation.
-/

namespace LeanModels.Python

/-! ## `ToExpr` instances (derived; used by `load_program` at elaboration time) -/

deriving instance Lean.ToExpr for Span
deriving instance Lean.ToExpr for BinOp
deriving instance Lean.ToExpr for UnaryOp
deriving instance Lean.ToExpr for BoolOp
deriving instance Lean.ToExpr for CmpOp
deriving instance Lean.ToExpr for Const
deriving instance Lean.ToExpr for Param
deriving instance Lean.ToExpr for Expr
deriving instance Lean.ToExpr for Stmt
deriving instance Lean.ToExpr for FunctionDefn
deriving instance Lean.ToExpr for Module

/-! ## `load_program` -/

open Lean Elab Command in
/--
`load_program tri from "Examples/python/tri/tri.json"` reads the standardized
envelope JSON at **elaboration time** and defines `tri : Module` as a
**literal** first-order term (via the `ToExpr` instances above), so proofs can
unfold it. The path is resolved relative to the current working directory,
which under `lake build` is the package root. Missing files and malformed
envelopes are clear elaboration errors, never silent.

The definition lands in the current namespace (companion files use the root
namespace). Rebuild-on-source-change is handled by the sha256 line in the
generated companion file, not by this command.
-/
elab "load_program " name:ident " from " path:str : command => do
  let pathStr := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathStr⟩).toBaseIO with
    | .ok c => pure c
    | .error e =>
        throwErrorAt path
          "load_program: cannot read '{pathStr}': {toString e}\n(relative paths resolve against the current working directory — the package root under `lake build`; current cwd: '{toString (← IO.currentDir)}')"
  let envl ←
    match parseEnvelopeString contents with
    | .error e =>
        throwErrorAt path "load_program: '{pathStr}' is not a valid envelope: {e}"
    | .ok envl => pure envl
  unless envl.language == "python" do
    throwErrorAt path
      "load_program: '{pathStr}' has language '{envl.language}', expected 'python'"
  let declName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declName then
    throwErrorAt name "load_program: '{declName}' has already been declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declName
      levelParams := []
      type := Lean.mkConst ``LeanModels.Python.Module
      value := Lean.toExpr envl.module
      hints := .abbrev
      safety := .safe }
    -- Without this, `simp [<ident>]` cannot realize the definition's
    -- equational lemmas ("enableRealizationsForConst must be called" error).
    enableRealizationsForConst declName
    addDocStringCore declName
      s!"Program module loaded by `load_program` from `{pathStr}` (source: `{envl.sourceFile}`, sha256 `{envl.sourceSha256}`). A literal `LeanModels.Python.Module` — proofs may unfold it."
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declName) (isBinder := true)

/-- `#print_program tri` logs the `Repr` of a program previously defined by
`load_program` (or any `Module`-typed constant). -/
macro "#print_program " name:ident : command => `(#eval (repr $name))

/-! ## Spec layer -/

/-- Partial correctness of a call, abstracted over fuel: `CallsTo m f args r`
holds iff *some* fuel makes `callFunction m f args fuel = .ok r`. Fuel
monotonicity is intentionally *not* baked in; theorems quantify over fuel in
the canonical `@[spec]` shape (see the `spec` attribute docstring). -/
def CallsTo (m : Module) (f : String) (args : Array Val) (r : Val) : Prop :=
  ∃ fuel, callFunction m f args fuel = .ok r

/-! ## Proof-automation seed

Reusable lemmas and the `py_simp` tactic for *symbolic execution* of the
interpreter inside proofs. The intended proof pattern for a canonical
partial-correctness theorem (`callFunction p "f" args fuel = .ok r → r = …`)
is:

1. `match fuel with` — split off the small fuels (each reduces to
   `.timeout = .ok r`, which `py_simp at h` closes) from `fuel + k`, where
   `k` bounds the straight-line depth of the function body.
2. `py_simp [p, callFunction, …] at h` — unfold the program literal and
   symbolically execute. Recursive-call boundaries (`callFunction`,
   `execWhile`) are **not** in the default simp set, so they stay frozen at
   symbolic fuel; unfold the outer one with `rw [callFunction.eq_2] at h`
   (resp. `execWhile.eq_2`) and pass them explicitly only where full
   unfolding is safe (non-recursive programs).
3. `Res.bind_eq_ok` (a global simp lemma) turns `x >>= f = .ok r` into
   `∃ a, x = .ok a ∧ f a = .ok r`, so after `py_simp` the hypothesis is a
   nest of existentials whose atoms are the frozen recursive calls:
   `obtain` them, discharge each with the induction hypothesis (induction on
   fuel — structural for loops, `Nat.strongRecOn` for recursion), `subst`,
   and `py_simp` again until `h` closes the goal.
-/

/-- `pure` on `Res` is `Res.ok` (do-notation normalization). -/
@[simp] theorem Res.pure_eq {α} (a : α) : (pure a : Res α) = .ok a := rfl

/-- Bind on an `ok` result steps into the continuation (do-notation
normalization; this is what advances symbolic execution). -/
@[simp] theorem Res.ok_bind {α β} (a : α) (f : α → Res β) :
    (Res.ok a >>= f) = f a := rfl

/-- Exceptions short-circuit bind. -/
@[simp] theorem Res.exn_bind {α β} (e : PyErr) (f : α → Res β) :
    ((Res.exn e : Res α) >>= f) = .exn e := rfl

/-- Timeouts short-circuit bind (this closes the small-fuel goals). -/
@[simp] theorem Res.timeout_bind {α β} (f : α → Res β) :
    ((Res.timeout : Res α) >>= f) = .timeout := rfl

/-- `unsupported` short-circuits bind. -/
@[simp] theorem Res.unsupported_bind {α β} (msg : String) (f : α → Res β) :
    ((Res.unsupported msg : Res α) >>= f) = .unsupported msg := rfl

/-- Inversion of a successful bind: the intermediate result must itself be
`ok`. Under `simp` this turns a symbolically-executed hypothesis into a nest
of existentials whose atoms are the frozen recursive calls — `obtain` them
and feed each to the induction hypothesis. -/
@[simp] theorem Res.bind_eq_ok {α β} {x : Res α} {f : α → Res β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

open Lean Lean.Parser.Tactic in
/-- `py_simp [extra, lemmas] at h` — one stack frame's worth of symbolic
execution of the Python interpreter: `simp` with every interpreter equation
*except* the recursion points `callFunction` and `execWhile`, which stay
frozen at symbolic fuel so induction hypotheses can be applied to them. Pass
them explicitly (`py_simp [callFunction, execWhile, tri] at h`) when full
unfolding is safe (no recursion, or concrete fuel), or unfold exactly one
step with `rw [callFunction.eq_2] at h` / `rw [execWhile.eq_2] at h`.
Program literals introduced by `load_program` must also be passed explicitly
(e.g. `py_simp [tri] at h`). `and_assoc` is included so that fully-reduced
existential nests collapse. -/
macro (name := pySimpTactic) "py_simp" "[" args:(simpStar <|> simpErase <|> simpLemma),* "]"
    loc:(location)? : tactic => do
  let extra : Syntax.TSepArray
      [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
       `Lean.Parser.Tactic.simpLemma] "," := ⟨args.elemsAndSeps⟩
  `(tactic| set_option linter.unusedSimpArgs false in
      simp [execStmts, execStmt, evalExpr, evalExprs, evalBoolChain,
            evalCompareChain, findFunction, mkCallEnv, Env.lookup, Env.set,
            Const.toVal, truthy, asInt, valEq, valEqList, intCmp, strCmp,
            evalCompareOp, evalBinOp, evalUnaryOp, lenVal, normIndex, indexVal,
            targetNames, bindAll, assignTo, and_assoc, $extra,*] $(loc)?)

@[inherit_doc pySimpTactic]
macro "py_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| py_simp [] $(loc)?)

/-!
### The `@[spec]` attribute

Specification lemmas are registered with **`@[spec]`**, exactly as DESIGN.md
prescribes. Canonical partial-correctness shape:

```
@[spec] theorem tri_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
    (h : callFunction tri "tri" #[.int n] fuel = .ok r) :
    r = .int (n * (n + 1) / 2)
```

**Mechanism (toolchain deviation, recorded):** DESIGN.md suggested
`register_simp_attr spec`, but on toolchain v4.33.0-rc1 the attribute name
`spec` is already taken by core Lean (the `mvcgen` spec attribute, initializer
`Lean.Elab.Tactic.Do.SpecAttr.mkSpecAttr` — "Marks Hoare triple specifications
**and simp theorems** for use with `mvcgen` tactics"). Attribute names are
global, so registering our own `spec` collides at initializer time in every
importing module. Resolution: we rely on the core attribute — it explicitly
accepts plain (conditional) simp-shaped theorems like the canonical shape
above, keeps them in a queryable registry (`Lean.Elab.Tactic.Do`'s spec-
theorem extension), and preserves DESIGN.md's surface syntax and intent
(automation can find callee specs) with zero custom code.

Consequences for later phases:
* `@[spec] theorem …` compiles verbatim — nothing changes in spec statements.
* There is no `simp [spec]` simp set; cite registered lemmas by name
  (`simp [tri_spec]`) or query the core spec registry programmatically.
* `native_decide` remains forbidden in `@[spec]` theorems (`#print axioms`
  must show only standard axioms).
-/

end LeanModels.Python
