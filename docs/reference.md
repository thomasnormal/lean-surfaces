# Reference — Python lane (v0)

Information-oriented lookup tables for the spec surface, tactics, types, and
CLI. Everything here is verified against the current tree; the normative
contracts live in [DESIGN.md](DESIGN.md) (interpreter, formats) and
[spec-surface.md](spec-surface.md) (surface design, including layers not yet
built). Task-oriented walkthroughs: [howto/](howto/).

Everything Lean below lives in namespace `LeanModels.Python` (the example
`spec.lean`/`proof.lean` files `open` it for you).

## The judgment family

Defined in [`LeanModels/Python/Surface.lean`](../LeanModels/Python/Surface.lean)
(the arrows and `PartialTo`/`Raises`) and
[`LeanModels/Python/Logic.lean`](../LeanModels/Python/Logic.lean) (`CallsTo`).
The callee identifier is both the loaded module constant and the Python
function name; a dotted identifier splits — `arith.floordiv(a, b)` is module
`arith`, function `"floordiv"`. Arguments and the result are marshalled
through `ToVal.toVal` (table below).

| Surface | Reading | Exact elaboration (from the tree) |
|---|---|---|
| `f(a, b) ==> v` | total: some fuel returns `v` | `CallsTo f "f" #[ToVal.toVal a, ToVal.toVal b] (ToVal.toVal v)` |
| `f(a, b) ⇓ r` | same judgment, hypothesis position: binds a typed result | identical to `==>` (`CallsTo …`); prints back as `==>` |
| `f(a, b) ==>! e` | terminates by raising `e` | `Raises f "f" #[ToVal.toVal a, ToVal.toVal b] (e : PyErr)` |
| `f(a, b) ~~> v` | strengthened partial: every run either times out or returns exactly `v` | `PartialTo f "f" #[ToVal.toVal a, ToVal.toVal b] (ToVal.toVal v)` |
| `PyTriple m P ss Q` (py_vcgen layer, [VC.lean](../LeanModels/Python/VC.lean); no surface syntax yet) | flow-aware total-correctness triple over a statement list: `Q : PyPost` has arms `next`/`ret`/`brk`/`cont`/`err`, timeout excluded by the threshold shape | `∀ env, P env → ∃ t, ∀ F ≥ t, Q.holds (execStmts m F env ss)` (statement level: `PyStmtTriple`; rules in VC.lean's docstring) |
| `callsTo_iff_triple` / `raises_iff_triple` (py_vcgen layer 2, [VC2.lean](../LeanModels/Python/VC2.lean): while rule, call rules, `@[py_spec]` registry) | arrow⇄triple bridges: `f(args) ==> v` (resp. `==>! e`) iff the whole-function-body triple from entry env `mkCallEnv f.params args` | `CallsTo m f args v ↔ PyTriple m (· = mkCallEnv …) body { next := fun _ => v = .none, ret := fun w _ => w = v }` (raise side through the `err` arm; recursion pattern: [VCTests.lean](../LeanModels/Python/VCTests.lean)) |

with (copied from the tree):

```lean
-- LeanModels/Python/Logic.lean
def CallsTo (m : Module) (f : String) (args : Array Val) (r : Val) : Prop :=
  ∃ fuel, callFunction m f args fuel = .ok r
```

```lean
-- LeanModels/Python/Surface.lean
def Raises (m : Module) (f : String) (args : Array Val) (e : PyErr) : Prop :=
  ∃ fuel, callFunction m f args fuel = .exn e

def PartialTo (m : Module) (f : String) (args : Array Val) (v : Val) : Prop :=
  ∀ fuel r, callFunction m f args fuel = r → r = .timeout ∨ r = .ok v
```

`~~>` is deliberately *not* "if it returns `.ok` then `v`" — that reading is
vacuously provable on raising/diverging programs. `PartialTo` rules out
exceptions, `unsupported`, and wrong values at every fuel; only timeout
remains possible. It does not assert termination. See the docstrings in
[Surface.lean](../LeanModels/Python/Surface.lean) for the full rationale.

Not yet implemented (normative design only, see
[spec-surface.md](spec-surface.md)): `≃` outcome equivalence,
`Py.Terminates`, contract triples `⦃P⦄ f(x) ⦃r, Q⦄`, and the `Py.*` spec-side
ops library. Current spec statements use `Int.fdiv` / `Int.fmod` directly,
plus the helpers at the bottom of Surface.lean (`|x|` notation,
`gcd_emod_step`, `gcd_fmod_step`).

### Converting between judgments

All in [Surface.lean](../LeanModels/Python/Surface.lean) /
[Obs.lean](../LeanModels/Python/Obs.lean), all consequences of fuel
monotonicity (`fuelMono`):

| Lemma | Statement shape |
|---|---|
| `CallsTo.partialTo` | `f(x) ==> v → f(x) ~~> v` |
| `PartialTo.callsTo` | `f(x) ~~> v → (∃ fuel, callFunction … ≠ .timeout) → f(x) ==> v` |
| `PartialTo.of_diverges` | a diverging call satisfies `~~> v` for *every* `v` (why `~~> → ==>` is false) |
| `CallsTo.eq_of_partialTo` | `f(x) ==> v → f(x) ~~> w → v = w` |
| `PartialTo.not_raises` | `f(x) ~~> v → f(x) ==>! e → False` |
| `CallsTo.functional` | `f(x) ⇓ v → f(x) ⇓ w → v = w` (determinism across fuels) |
| `CallsTo.not_raises` | `==>` and `==>!` are mutually exclusive |
| `CallsTo.at_least` | threshold form: `∃ f₀, ∀ F ≥ f₀, callFunction … F = .ok v` |
| `PartialTo.iff_obs` | `~~> v` ↔ the only `Obs` outcomes are `returns v` and `diverges` |

The `Obs` spine ([Obs.lean](../LeanModels/Python/Obs.lean)): outcomes
`PyOut ::= returns v | raises e | diverges | stuck msg`, judgment
`Obs m f args o`, with `Obs.det` (at most one outcome) and `Obs.total`
(classically, at least one). It is proof machinery, not theorem surface — the
delaborators deliberately leave it unsugared.

## Tactics

All defined in [Surface.lean](../LeanModels/Python/Surface.lean),
[LoopTactic.lean](../LeanModels/Python/LoopTactic.lean), and
[Logic.lean](../LeanModels/Python/Logic.lean); each has a thorough docstring —
this table is the index, the docstrings are the manual.

| Tactic | Syntax | Closes / does | Leaves |
|---|---|---|---|
| `py_prove` | `py_prove [prog, extras…]` | total goals `f(…) ==> v` and `f(…) ==>! e` for **loop-free** bodies, straight-line or branching (fuel witness 32, symbolic execution, `split`/`omega` mop-up) | nothing on success; fails on loops/recursion (use `py_begin`/`py_loop` or `py_lift`) |
| `py_begin` | `py_begin [prog]` | opener for loop proofs on a `==>`/`⇓` goal: symbolically executes the entry up to the `while`, unbrands `Py*` hypotheses for `omega`/`grind` | the goal unchanged plus `hentry : ∀ F, callFunction … (F + 32) = <entry form with frozen execWhile>` |
| `py_loop` | `py_loop (state := [a, b])? (inv := fun (x y : Int) => …) (dec := fun (x y : Int) => …)` (`state` comes first when present) | the whole loop, via the generic while rule; `inv` binder names must be the Python variable names unless `state` renames them ([howto](howto/handle-shadowed-loop-variables.md)) | pure-math goals, in order: exit algebra (primed variables, `hcont`, `hinv1…`), invariant preservation, measure decrease, initial invariant |
| `py_lift` | `py_lift ⟨f₀, h⟩ := e with [prog]` | puts a `CallsTo` fact `e` (typically a recursion IH) in fuel-threshold form and normalizes it | `h : ∀ F, f₀ ≤ F → callFunction … F = .ok v`, a conditional rewrite for `simp (disch := omega) only [h]` |
| `py_corollary` | `py_corollary [tot]` or `py_corollary [tot, extras…]` | any of the four standard corollaries of a total theorem `tot` ([howto](howto/derive-corollary-forms.md)) | nothing on success |
| `py_simp` | `py_simp [extras]` / `py_simp [extras] at h` | one frame of symbolic execution: `simp` with all interpreter equations *except* `callFunction`/`execWhile` (frozen at symbolic fuel); pass program literals explicitly (`py_simp [tri]`) | whatever `simp` leaves |
| `py_threshold` | `py_threshold k [extras]` / `py_threshold k` | a fuel-threshold obligation `∃ f₀, ∀ F, f₀ ≤ F → <run> = .ok v` for straight-line code, at threshold `k` | residual symbolic branches, if the `split <;> simp_all` mop-up cannot close them |
| `proofs` | `:= by proofs` (only in a three-file `spec.lean`) | closes a spec-file statement with its `proof.lean` twin: same declaration name, module `….spec` ↔ sibling namespace `….proof` | nothing on success; precise errors for a missing twin or a non-`spec` module |

## `#py_check` and other commands

| Command | Expands to / does |
|---|---|
| `#py_check f(a, b) = v` | `#guard callFunction f "f" #[ToVal.toVal a, ToVal.toVal b] 4096 == .ok (ToVal.toVal v)` — a concrete elaboration-time run (fixed generous fuel; cost is proportional to actual steps, not fuel) |
| `#py_check f(a, b) raises e` | same at `.exn (e : PyErr)`, e.g. `#py_check arith.mod(7, 0) raises .zeroDivisionError` |
| raw `#guard` | for what the surface form cannot say: `.unsupported` outcomes (`#guard (callFunction arith "powi" #[.int 2, .int (-1)] 20 matches .unsupported _)`) and spec-side math facts |
| `load_program tri from "Examples/python/tri/tri.json"` | reads the envelope at elaboration time, defines `tri : Module` as a literal term (path relative to the `lake build` cwd = repo root) |
| `#print_program tri` | logs the `Repr` of a loaded program |

Convention: every example's `spec.lean` **opens** with `#py_check`
non-vacuity runs, so the ∃-fuel theorems below them are demonstrably not
vacuous.

## `Py*` types and marshalling

From [Surface.lean](../LeanModels/Python/Surface.lean). The brands are
*transparent abbreviations* — documentary today, a migration seam later:

| Type | Definition | Note |
|---|---|---|
| `PyInt` | `abbrev PyInt := Int` | Python `int` is exactly mathematical `Int` |
| `PyBool` | `abbrev PyBool := Bool` | |
| `PyStr` | `abbrev PyStr := String` | caveat: CPython admits lone surrogates; may become a distinct type |

`ToVal` instances (spec-to-interpreter marshalling; each has a `@[simp]`
unfolding lemma `toVal_int`, `toVal_nat`, …):

| Instance | Sends |
|---|---|
| `ToVal Val` | `id` (raw values pass through) |
| `ToVal Int` | `n ↦ .int n` |
| `ToVal Nat` | `n ↦ .int ↑n` (Nat-valued specs like `Int.gcd`; bridged back by `Int.toNat_of_nonneg`, which `py_corollary` includes by default) |
| `ToVal Bool` | `b ↦ .bool b` |
| `ToVal String` | `s ↦ .str s` |
| `ToVal (List α)` given `ToVal α` | `xs ↦ .list (xs.map toVal).toArray` |

Gotcha (verified): `omega`'s atom matching is syntactic and does not see
through the brands — a comparison headed at `PyInt`, hypothesis or goal, is
invisible to it. `py_begin` unbrands hypotheses for you; in manual proofs
use `Int` binders where a proof ends in `omega`
(as `add_spec`/`tri_spec` do). When
restating a branded hypothesis instead, put an `Int`-typed term on the
comparison's **left** (`have hx' : (0 : Int) ≥ x := hx`) — ascribing the
branded variable does not unbrand — and close brand-headed *goals* with
`grind`, which unfolds reducibly
([tutorial 06, mode 5](tutorial/06-when-proofs-fail.md#5-omega-ignores-a-pyint-typed-hypothesis)).

## Error classes

`PyErr` ([Ast.lean](../LeanModels/Python/Ast.lean)) vs canonical Python names
(as printed by the runner and compared by the harness — `errName` in
[Main.lean](../Main.lean)):

| `PyErr` constructor | Payload | Python name |
|---|---|---|
| `.typeError (msg : String)` | message | `TypeError` |
| `.nameError (name : String)` | the unresolved name | `NameError` |
| `.zeroDivisionError` | — | `ZeroDivisionError` |
| `.indexError` | — | `IndexError` |
| `.valueError (msg : String)` | message | `ValueError` |

Notes:
- `Res.unsupported` is **not** an error class: it marks the v0 tier boundary
  (loud, never wrong), and the harness whitelists it only via
  `"expect": "unsupported"`.
- CPython's `UnboundLocalError` is a `NameError` subclass; the harness
  canonicalizes it to `NameError` (DESIGN.md name-resolution row).
- `==>!` compares the whole `PyErr` *value*, message included — payload-free
  classes (`.zeroDivisionError`, `.indexError`) are the practical targets
  ([howto](howto/spec-a-raising-function.md)).

## v0 semantic tier — summary

Normative tables: [DESIGN.md](DESIGN.md) ("Python v0 semantic tier" and
"Semantic decisions"). One paragraph: ints (exact, arbitrary precision),
bools, strs, lists, tuples, `None`; `while`/`if`/assignment/tuple
unpacking/`break`/`continue`/`pass`; calls to module-level functions
(positional args) plus builtin `len`; recursion; chained comparisons,
short-circuit `and`/`or` returning operand values; floor-division semantics
(`Int.fdiv`/`Int.fmod`). Outside the tier ⇒ `Res.unsupported` with a message
naming the construct — never a silently wrong value. Checking a specific
program: [howto/check-what-the-extractor-supports.md](howto/check-what-the-extractor-supports.md).

## CLI

| Command | What |
|---|---|
| `python3 extractors/python/extract.py <file.py> [more…] [--companion-dir DIR]` | writes `<file>.json` (envelope) next to the source + `<CompanionDir>/<PascalStem>.lean` (default companion dir: the source file's own directory) — the companion only when the source has `# lean[` blocks (block-less three-file sources get the envelope alone), and never over a hand-written file at that path; deterministic; out-of-vocabulary constructs become `Unsupported` nodes — errors on syntax errors, non-identifier stems, unclosed `# lean[` blocks, hand-written file at the companion path |
| `lake exe leanmodels-run <envelope.json> <function> [args…] [--fuel N]` | one JSON line: `{"status":"ok","value":…}` \| `{"status":"exn","exn":"…"}` \| `{"status":"timeout"}` \| `{"status":"unsupported","msg":"…"}`; args are integers; default fuel 10000; exit 0 for every canonical result |
| `python3 harness/diff_test.py [--cases F] [--fuel N] [--no-build] [--runner CMD]` | CPython vs Lean on `harness/cases.json`; exits non-zero on any non-whitelisted mismatch ([howto](howto/run-the-differential-harness.md)) |
| `python3 tools/docs_check.py [files…] [--list-unmarked]` | docs drift checker: every path-marked code block in `docs/**`, `README.md`, `AGENTS.md` must match the referenced file (marker convention in the script's header); exits non-zero listing drifted blocks. Full check triad: `lake build && python3 tools/docs_check.py && python3 harness/diff_test.py` |

## File map

| Path | What |
|---|---|
| `docs/DESIGN.md` | authoritative v0 interface contract |
| `docs/envelope-schema.md` | JSON envelope schema (v0.1, Python payload) |
| `docs/spec-surface.md` | spec-surface design: what is live, what is target |
| `LeanModels/Core/Basic.lean` | language-neutral core (`Span`) |
| `LeanModels/Python/Ast.lean` | AST inductives + `Val`/`PyErr`/`Res`/`Flow`/`Env` |
| `LeanModels/Python/Json.lean` | envelope JSON → AST ingestion |
| `LeanModels/Python/Semantics.lean` | fuel-based definitional interpreter (mutual block + pure helpers) |
| `LeanModels/Python/Logic.lean` | `ToExpr`, `load_program`, `CallsTo`, `@[spec]`, `py_simp` |
| `LeanModels/Python/Obs.lean` | fuel monotonicity, cross-fuel determinism, the `Obs` spine |
| `LeanModels/Python/Surface.lean` | `Py*` types, `ToVal`, the arrows, `#py_check`, `py_prove`/`py_lift`/`py_corollary`/`py_threshold`, while rule |
| `LeanModels/Python/LoopTactic.lean` | `py_begin` / `py_loop` |
| `LeanModels/Python/Delab.lean` | delaborators: goals print in arrow notation |
| `LeanModels/Python/Tests.lean` | interpreter smoke tests |
| `extractors/python/extract.py` | extractor + `# lean[` scanner + companion generator (inline mode) |
| `Examples/python/<name>/` | one directory per Python example, three-file layout: pure `<name>.py` + generated `<name>.json` envelope + hand-written `spec.lean` (statements, `:= by proofs`) / `proof.lean` (real proofs) — `proofs` tactic, Surface.lean |
| `Examples/python/sum_to/` | the one inline-mode example: `# lean[` blocks in `sum_to.py` + generated companion `SumTo.lean` |
| `Main.lean` | `leanmodels-run` CLI |
| `harness/diff_test.py`, `harness/cases.json` | differential harness vs CPython |
| `LeanModels/Sv/**`, `extractors/sv/**`, `harness/sv/**`, `docs/sv-*.md`, SV example dirs (`Examples/system-verilog/swap_nba/`, `Examples/system-verilog/counter/`, `Examples/system-verilog/race_blk/`, `Examples/system-verilog/adder/`, `Examples/system-verilog/xsel/`, `Examples/system-verilog/toggle/`) | SystemVerilog lane: M0 scheduler core + typed-surface slice (not imported by `LeanModels.lean`; the SV example specs build under the `Examples` glob — see [howto/sv-quickstart.md](howto/sv-quickstart.md)) |
