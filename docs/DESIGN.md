# lean_models — Design (v0: Python vertical slice)

This document is the **authoritative interface contract** for v0. Components built
against it must match it exactly (names, signatures, formats). If you find a genuine
contradiction or impossibility, resolve it minimally and record the deviation.

## Project vision (context)

Prove correctness of real Python / C++ / Rust / SystemVerilog programs in Lean 4.
Four decoupled coverage axes:

1. **Parse coverage** — borrow each language's own frontend (CPython `ast`, Clang,
   slang, syn); extractors are thin dumpers into a standardized JSON envelope.
2. **Representation coverage** — full ASTs in Lean; unknown constructs become
   `Unsupported` nodes, so ingestion never fails.
3. **Semantic coverage** — tiered, executable, definitional interpreters that fail
   *loudly* (`Res.unsupported`) outside the supported tier. Coverage is measured on
   real corpora, never silently faked.
4. **Proof coverage** — spec/Hoare layer lags semantics.

Cross-cutting principles: programs stay source-shaped (legibility for AI provers);
all nondeterminism will be explicit oracle parameters (matters for SV later);
differential testing against the real implementation (CPython here) validates the
semantics; annotations ride in free-form `# lean[ ... # ]` comment blocks spliced
into a generated companion Lean file.

## Repo layout

```
lean-toolchain            # leanprover/lean4:v4.33.0-rc1 (pinned; already installed)
lakefile.toml             # libs LeanModels, Examples (globs Examples.+), exe leanmodels-run
LeanModels.lean           # root: imports Core + Python umbrella
LeanModels/Core/Basic.lean        # Span (already written)
LeanModels/Python.lean            # umbrella; import each new submodule here
LeanModels/Python/Ast.lean        # AST inductives
LeanModels/Python/Json.lean       # envelope JSON -> AST ingestion
LeanModels/Python/Semantics.lean  # fuel-based definitional interpreter
LeanModels/Python/Logic.lean      # ToExpr, load_program, CallsTo, @[spec]
LeanModels/Python/Tests.lean      # interpreter smoke tests (#guard / #eval)
extractors/python/extract.py      # extractor + lean-block scanner + companion gen
Examples/python/*.py              # example sources (+ generated .json)
Examples/<Name>.lean              # generated companions (one per example)
Main.lean                         # leanmodels-run CLI
harness/diff_test.py, harness/cases.json   # differential tests vs CPython
docs/DESIGN.md, docs/envelope-schema.md, README.md
```

Everything Lean lives under namespace `LeanModels` (Python lane under
`LeanModels.Python`). System Python is **3.9** — extractor/harness code must be
3.9-compatible. Build: `lake build` at repo root. Never `sorry`. Never commit to git.

## Python v0 semantic tier

Supported (interpreter must implement faithfully):

- Statements: `FunctionDef` (simple positional params only), `Return` (bare `return`
  and fall-off-end yield `Val.none`), `Assign` (single target: `Name` or a
  `Tuple`/`List` of `Name`s — tuple unpacking; arity mismatch → `ValueError`),
  `AugAssign` (target `Name` only; a **list**-valued target is `unsupported` —
  CPython `list += x` mutates in place, observable through aliases, which value
  semantics cannot reproduce; immutable-valued targets rebind faithfully),
  `While` (with `orelse`: runs on normal exit,
  skipped on `break`), `If`/elif/else, `Expr` (evaluate, discard), `Pass`, `Break`,
  `Continue`.
- Expressions: `Constant` (int/bool/str/None), `Name`, `BinOp`
  (`Add Sub Mult FloorDiv Mod Pow`), `UnaryOp` (`USub Not`), `BoolOp` (`And Or`),
  `Compare` (chained), `Call` (module-level user functions, positional args only;
  builtin `len`), `List`, `Tuple`, `Subscript` (index only, no slices).
- Recursion between module functions: supported (fuel bounds it).

Everything else is representable in the AST (as itself or as `Unsupported`) but the
interpreter returns `Res.unsupported` when it reaches it. Top-level statements other
than `def` are recorded in `Module.topLevel` and ignored by `callFunction`
(v0 limitation: no globals, no closures, no module init effects — document, don't hide).

### Semantic decisions (normative)

| Topic | Rule |
|---|---|
| Integers | Arbitrary precision → Lean `Int`, exact. JSON carries them as decimal strings. |
| `//`, `%` | Python floors: use `Int.fdiv` / `Int.fmod` (NOT `/`, `Int.div`, `%`, `Int.emod`). Divisor 0 → `ZeroDivisionError`. |
| `/` | True division yields float → `unsupported` in v0. |
| `**` | Exponent ≥ 0 only (`Int` result); negative exponent → `unsupported` (float in Python), EXCEPT `0 ** negative` → `ZeroDivisionError` (CPython raises, no float involved). |
| bool/int coercion | Python's `bool` is an `int` subtype. In arithmetic AND comparisons, coerce `Val.bool b` to `Int` (`True`→1). So `True + 1 = 2 : int`, `True == 1` is `True`, `True < 2` is `True`. Results of arithmetic are always `int`, never `bool`. |
| `+` | int/bool + int/bool → int; str+str; list+list; tuple+tuple. Else `TypeError`. |
| `==`/`!=` | Never raise. Numeric (int/bool) compare by value; str/list/tuple structural (lists/tuples elementwise, recursion is fine); `None == None` is True; cross-type (after bool→int) is `False` (`1 == "1"` is False). |
| `<` `<=` `>` `>=` | int/bool vs int/bool by value; str vs str lexicographic (Unicode code points, which is Lean `String` `<`); v0: comparing other types → `unsupported`. |
| Chained compare | `a < b < c` evaluates each operand **once**, left to right, short-circuits on first False (result False without evaluating the rest). |
| `and`/`or` | Short-circuit and **return the operand value**, not a bool: `0 or "x"` is `"x"`. |
| Truthiness | `bool(x)`: None→False; bool→itself; int→`≠0`; str/list/tuple→nonempty. Used by `if`, `while`, `and`/`or`, `not`. |
| Name resolution | local env → module function table (functions are first-class enough to call by name; referencing a function name as a *value* is `unsupported` in v0) → builtin `len` → `NameError`. CPython's static-locals rule (a name assigned anywhere in the body is local throughout; early reads raise `UnboundLocalError`) is NOT modeled dynamically: the extractor flags functions that *call* a name they also assign (`locals_unsupported` → `localsOk = false`) and the interpreter refuses them loudly; plain read-before-assign of a local yields `NameError` (harness canonicalizes CPython's `UnboundLocalError`, a `NameError` subclass, to `NameError`). Duplicate top-level `def`s: the LAST definition wins (each `def` rebinds, as in CPython). |
| Assignment | `Env.set`: replace existing binding in place, else append. Env is `List (String × Val)`, first match wins on lookup. |
| Indexing | `xs[i]` for list/tuple/str (str yields 1-char str). Negative indices Python-style (`len+i`). Out of range → `IndexError`. Index must be int/bool → else `TypeError`. |
| `len` | list/tuple/str → int. Else `TypeError`. |
| Exceptions | v0 has no try/raise, but runtime errors are real: `PyErr` ∷ `typeError`, `nameError (name)`, `zeroDivisionError`, `indexError`, `valueError` (+ payload msgs where useful). Canonical names for the harness: `TypeError`, `NameError`, `ZeroDivisionError`, `IndexError`, `ValueError`. |
| Evaluation order | Left-to-right everywhere (operands, call args, comparators), evaluate once. |

## Core Lean types (normative signatures)

```lean
namespace LeanModels.Python

inductive Val where
  | none | bool (b : Bool) | int (n : Int) | str (s : String)
  | list (xs : Array Val) | tuple (xs : Array Val)
-- deriving Repr, Inhabited, BEq at minimum; DecidableEq if deriving copes
-- (nested Array: if `deriving DecidableEq` fails, a hand-written BEq is enough;
--  #guard needs Decidable equality of Res Val — via DecidableEq or `==`-based checks).

inductive PyErr where
  | typeError (msg : String) | nameError (name : String)
  | zeroDivisionError | indexError | valueError (msg : String)

/-- Interpreter results. `unsupported` = outside the v0 tier (loud), NOT a Python error. -/
inductive Res (α : Type) where
  | ok (a : α) | exn (e : PyErr) | timeout | unsupported (msg : String)

instance : Monad Res where … -- pure = ok; bind propagates exn/timeout/unsupported

inductive Flow where | next | ret (v : Val) | brk | cont

abbrev Env := List (String × Val)
```

Module shape (mirrors the envelope): `Module` holds `functions : Array FunctionDefn`
(name, params, `paramsOk : Bool` — false when the source used defaults/varargs/kwargs,
in which case calling it is `unsupported`), body statements, and `topLevel` statements.

## Fuel discipline (normative)

Every interpreter function takes `fuel : Nat` and starts
`match fuel with | 0 => .timeout | fuel+1 => …`, passing the *decremented* `fuel` to
**every** recursive call (expressions included). Termination is then structural on
fuel — no well-founded recursion gymnastics — and proofs do induction on fuel.
Signatures (normative):

```lean
def evalExpr  (m : Module) (fuel : Nat) (env : Env) : Expr → Res Val
def execStmt  (m : Module) (fuel : Nat) (env : Env) : Stmt → Res (Env × Flow)
def execStmts (m : Module) (fuel : Nat) (env : Env) : List Stmt → Res (Env × Flow)
def callFunction (m : Module) (fname : String) (args : Array Val) (fuel : Nat) : Res Val
```

(Mutual block; exact argument order above matters — proofs and the harness use it.)
Expressions cannot mutate the caller's env in v0 (calls run in fresh envs; no
globals), hence `evalExpr` returns only `Res Val`.

## Spec layer (normative)

```lean
def CallsTo (m : Module) (f : String) (args : Array Val) (r : Val) : Prop :=
  ∃ fuel, callFunction m f args fuel = .ok r
```

`@[spec]` — an attribute for registered specification lemmas (simplest working
mechanism on this toolchain, e.g. `register_simp_attr spec`; intent: automation can
later find callee specs). Canonical partial-correctness shape:

```lean
@[spec] theorem tri_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
    (h : callFunction tri "tri" #[.int n] fuel = .ok r) :
    r = .int (n * (n + 1) / 2)
```

## `load_program` (normative)

Command macro, exact syntax the extractor emits:

```lean
load_program tri from "Examples/python/tri.json"
```

Reads the envelope JSON at **elaboration time** (path relative to package root, i.e.
the `lake build` cwd; on read/parse failure produce a clear elaboration error) and
defines `tri : LeanModels.Python.Module` as a **literal term** (via `ToExpr`
instances — derived if `deriving ToExpr` works on this toolchain, hand-written
otherwise). It must NOT be a runtime parse of an embedded string: proofs must be able
to unfold `tri` to a first-order AST value. Rebuild-on-source-change is handled by
the sha256 line in the generated companion file (content change ⇒ Lake rehash).

## `# lean[ ... # ]` blocks and companion files (normative)

Scanner (in extract.py): a block opens at a line matching `^\s*#\s*lean\[\s*$` and
closes at `^\s*#\s*\]\s*$`; inner lines strip the leading `^\s*#` and at most one
following space. Blocks never nest. Text is spliced verbatim. Lines starting with
`import ` inside blocks are hoisted (deduped, order-preserving) to the companion
header. Unclosed block = extractor error.

Companion file `Examples/<PascalCaseStem>.lean` (e.g. `tri.py` → `Examples/Tri.lean`),
exact format:

```lean
/-
AUTOGENERATED by extractors/python/extract.py — DO NOT EDIT.
source: Examples/python/tri.py
sha256: <hex sha256 of the source file bytes>
-/
import LeanModels
<hoisted imports, if any>

open LeanModels LeanModels.Python

load_program tri from "Examples/python/tri.json"

<block 1>

<block 2>
…
```

The program identifier is the source stem (must be a valid Lean ident; extractor
errors otherwise). Convention: every example's first block contains `#guard`
non-vacuity checks (concrete runs, e.g.
`#guard callFunction tri "tri" #[.int 10] 1000 == .ok (.int 55)`) so a partial-
correctness theorem can never be vacuously true because the interpreter got stuck.

## Runner + differential harness (normative I/O format)

`lake exe leanmodels-run <envelope.json> <function> [args…] [--fuel N]` (args parsed
as ints; default fuel 10000). Prints ONE line of JSON to stdout:

- `{"status":"ok","value":V}` | `{"status":"exn","exn":"ZeroDivisionError"}`
- `{"status":"timeout"}` | `{"status":"unsupported","msg":"…"}`

where `V` is: `{"t":"none"}` | `{"t":"bool","v":true}` | `{"t":"int","v":"55"}`
(decimal string) | `{"t":"str","v":"…"}` | `{"t":"list","v":[V…]}` |
`{"t":"tuple","v":[V…]}`.

`harness/diff_test.py` reads `harness/cases.json`
(`[{"file": "Examples/python/tri.py", "function": "tri", "args": [[10],[0],[-3],…],
"expect": "match"}]`; `"expect":"unsupported"` whitelists documented v0 gaps), runs
CPython on the source (import by path, call, map result/exception to the same
canonical JSON) and the Lean runner, compares, prints a table, exits non-zero on any
non-whitelisted mismatch.

## Definition of done (v0)

1. `lake clean && lake build` green on a fresh checkout; no `sorry`/`admit`;
   `#print axioms` of every `@[spec]` theorem shows only standard axioms.
2. `extract.py` is deterministic (double-run byte-identical) and regenerating all
   examples leaves the tree unchanged (companions in sync).
3. Examples `add.py`, `tri.py`, `fib.py` (+ `arith.py` for edge cases) extract,
   build, and their `#guard` checks pass; `tri_spec` (loop) and `add_spec`
   (straight-line) are proved; `fib` proved against a native Lean recurrence if
   feasible (report honestly if not).
4. `harness/diff_test.py` passes, including negative/zero/edge inputs
   (floor-div/mod signs, short-circuit values, chained comparisons, tuple unpack).
