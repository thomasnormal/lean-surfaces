# lean_models

Prove real Python / C++ / Rust / SystemVerilog programs correct in Lean 4.

Each language gets a **deep embedding**: the program's real AST becomes a Lean
value, and a definitional interpreter gives it meaning. Programs stay
**source-shaped** — the Lean term mirrors the file you wrote — so specs and
proofs read against code you recognize, which is what makes AI-assisted proving
tractable.

## Design: four decoupled coverage axes

Coverage on each axis grows independently; nothing on a lower axis blocks a
higher one, and nothing is ever silently faked.

1. **Parse coverage** — borrow each language's own frontend (CPython `ast`,
   Clang, slang, syn). Extractors are thin dumpers into a standardized JSON
   envelope ([docs/envelope-schema.md](docs/envelope-schema.md)).
2. **Representation coverage** — full ASTs in Lean; constructs outside the
   supported vocabulary become `Unsupported` nodes, so ingestion never fails.
3. **Semantic coverage** — tiered, executable, definitional interpreters that
   fail *loudly* (`Res.unsupported`) outside the supported tier. Coverage is
   measured on real corpora.
4. **Proof coverage** — the spec/Hoare layer lags semantics, by design.

**The oracle principle:** all nondeterminism is an explicit oracle parameter of
the semantics. Irrelevant for straight-line Python; essential for
SystemVerilog, where the simulation scheduler's choices become a quantified
argument and theorems can range over *all* legal schedules.

**Validation:** the interpreter is differentially tested against the real
implementation (CPython here) on shared test cases — the semantics is checked
against ground truth, not against our own reading of the spec.

See [docs/DESIGN.md](docs/DESIGN.md) for the full normative contract.

## v0: the Python vertical slice

The workflow:

1. Write a Python file with theorems in `# lean[ ... # ]` comment blocks.
2. Run the extractor:
   `python3 extractors/python/extract.py Examples/python/sum_to.py`
   This emits `Examples/python/sum_to.json` (the AST envelope) and the
   companion file `Examples/SumTo.lean` with your blocks spliced in verbatim.
3. `lake build` — Lean ingests the JSON at elaboration time, defines
   `sum_to : Module` as a literal AST term, and checks your proofs.

Two worked examples (`Examples/tri/`, `Examples/gcd/`) use the **three-file
layout** instead: a pure `.py` (no lean-blocks; the extractor emits the
envelope and no companion), a hand-written `spec.lean` holding the
non-vacuity checks and every theorem *statement* (each proved `:= by
proofs`), and a `proof.lean` holding the real proofs (see the `proofs`
tactic in `LeanModels/Python/Surface.lean`).

### Example: `Examples/tri/`

```python
# Examples/tri/tri.py (the whole program)
def tri(n):
    total, i = 0, 0
    while i <= n:
        total += i
        i += 1
    return total
```

```lean
-- Examples/tri/proof.lean (the loop proof; statement + checks in Examples/tri/spec.lean)
theorem tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  py_begin [tri]
  py_loop (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1))
          (dec := fun (total i : Int) => (n + 1 - i).toNat)
  · obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind
```

The theorem says: for every `n ≥ 0`, running the *actual Python program* through
the verified interpreter terminates and returns `n(n+1)/2`. The user supplies
the loop invariant, the decreasing measure, and the closing arithmetic
(`omega`/`grind`) — the same content a pure-Lean proof of the same fact would
need (see `Examples/tri/spec.lean` for the statements, the `#py_check`
non-vacuity checks, and the derived `@[spec]` corollary forms).

The theorem is **partial correctness**: *if* the fuel-bounded interpreter
returns a value, that value is `n(n+1)/2`. That shape can be vacuously true if
the interpreter never returns `.ok` (bug, wrong tier, whatever). Hence the
**`#guard` non-vacuity convention**: every example's first block runs the
function on concrete inputs and checks the result at elaboration time, so the
"if" side is demonstrably inhabited before any theorem is trusted.

The runner and differential harness close the loop:

```
lake exe leanmodels-run Examples/tri/tri.json tri 10      # one-line JSON result
python3 harness/diff_test.py                              # Lean vs CPython on harness/cases.json
```

The full check before you finish any change (proofs *or* docs) is the triad:

```
lake build && python3 tools/docs_check.py && python3 harness/diff_test.py
```

`tools/docs_check.py` keeps the documentation honest: every path-marked code
block in `docs/`, this README, and `AGENTS.md` must match the referenced file
verbatim (marker convention in the script's header).

## Repo layout

| Path | What |
|---|---|
| `docs/DESIGN.md` | Authoritative interface contract (names, signatures, formats) |
| `docs/envelope-schema.md` | JSON envelope schema (v0.1, Python payload) |
| `LeanModels/Core/Basic.lean` | Language-neutral core (`Span`) |
| `LeanModels/Python/Ast.lean` | Python AST inductives |
| `LeanModels/Python/Json.lean` | Envelope JSON → AST ingestion |
| `LeanModels/Python/Semantics.lean` | Fuel-based definitional interpreter |
| `LeanModels/Python/Logic.lean` | `ToExpr`, `load_program` macro, `CallsTo`, `@[spec]` |
| `LeanModels/Python/Tests.lean` | Interpreter smoke tests (`#guard` / `#eval`) |
| `extractors/python/extract.py` | Extractor + `# lean[` scanner + companion generator |
| `Examples/python/*.py` | Example sources (+ generated `.json` envelopes) |
| `Examples/*.lean` | Generated companion files (one per lean-block example) |
| `Examples/tri/`, `Examples/gcd/` | Three-file examples: pure `.py` + envelope + hand-written `spec.lean`/`proof.lean` (`proofs` tactic, Surface.lean) |
| `Main.lean` | `leanmodels-run` CLI |
| `harness/` | Differential tests vs CPython (`diff_test.py`, `cases.json`) |
| `tools/docs_check.py` | Docs drift checker: path-marked doc code blocks must match the tree |

Toolchain: `leanprover/lean4:v4.33.0-rc1` (pinned), core Lean only — no package
dependencies. Extractor/harness require only Python ≥ 3.9 stdlib.

## v0 limitations (honest list)

- **Semantic tier is narrow.** Ints (arbitrary precision, exact), bools, strs,
  lists, tuples, `None`; `while`/`if`/assignment/tuple-unpacking; calls to
  module-level functions (positional args) and `len`; recursion. Anything else
  is representable but evaluates to `Res.unsupported` — loudly, never wrongly.
- **No floats.** True division `/` and negative `**` exponents are
  `unsupported`.
- **No globals, no closures, no module-init effects.** Top-level statements
  other than `def` are recorded but ignored; functions run in fresh
  environments.
- **No try/raise** — but runtime errors are real and faithful
  (`TypeError`, `NameError`, `ZeroDivisionError`, `IndexError`, `ValueError`).
- **Partial correctness via fuel.** Every interpreter function consumes fuel;
  out of fuel is `.timeout`. Theorems say "if it returns `.ok r`, then …" —
  termination is not proved (the `#guard` convention keeps this non-vacuous on
  concrete inputs).

## Roadmap (not built — do not expect it in this tree)

- **SystemVerilog**: scheduler core with 4-state values (`0/1/X/Z`); the event
  scheduler's nondeterminism as an explicit oracle, enabling schedule-oracle
  theorems ("for every legal schedule, …"). This is the payoff of the oracle
  principle.
- **C++ and Rust lanes**: same pipeline (Clang / syn frontends → envelope →
  deep embedding → tiered interpreter).
- **`mvcgen` integration**: hook the spec layer into Lean's verification
  condition generator instead of hand-rolled Hoare reasoning.
- **Differential testing at scale**: run the interpreters against reference
  implementations on real corpora as the standing semantics-validation
  methodology, with per-tier coverage numbers.
