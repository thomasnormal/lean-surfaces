# Python tier architecture

This page maps the Python tier for a new contributor: which files make up
the pipeline, what each one is responsible for, and where behaviour is
checked. The normative contracts are [DESIGN.md](DESIGN.md) (formats, fuel,
spec layer), [memory-model.md](memory-model.md) (heap, objects, and every
construct's semantics decision), and [spec-surface.md](spec-surface.md)
(what theorem statements look like).

## The pipeline

```
  foo.py ──extract.py──▶ foo.json ──load_program──▶ foo : Module ──interpreter──▶ Res Val
 (CPython ast)          (envelope)   (Json.lean,      (a literal        (fuel-bounded)
                                      at elaboration)  Lean term)
```

1. **Extraction.** `extractors/python/extract.py` parses the file with
   CPython's own `ast` module and writes a JSON envelope
   ([envelope-schema.md](envelope-schema.md)). The extractor makes no
   semantic decisions beyond classification. Constructs it cannot represent
   become explicit `Unsupported` nodes, so they cannot be silently
   dropped.
2. **Ingestion.** `load_program foo from "foo.json"` reads the envelope
   during Lean elaboration (`LeanModels/Python/Json.lean`). It produces
   `foo : Module`, a literal AST term that proofs can unfold. Ingestion
   also performs a small set of explicit, documented ingestion translations:
   class definitions remain structured source-order statements, with method bodies indexed for dispatch; generator expressions become
   synthesized generator functions, and dict views and `del d[k]` become
   synthetic builtins such as `<dictkeys>`. List/set/dict comprehensions and
   starred displays remain explicit loud AST boundaries. It also recognises
   `namedtuple` definitions.
3. **Interpretation.** A definitional interpreter gives the `Module`
   meaning. It is fuel-bounded: every run ends in `.ok v`, `.exn e`,
   `.timeout` (out of fuel), or `.unsupported msg` (outside the modelled
   tier). The heap, globals, stdout and a clock trace are threaded through
   a `World` ([memory-model.md](memory-model.md)).

## The definition and the theorem interpreter

The Python tier has one current definition and one legacy theorem target.
Contributors need to know which one a given check exercises.

| | theorem interpreter (legacy) | tier definition and runner |
|---|---|---|
| file | `LeanModels/Python/Semantics.lean` | `LeanModels/Python/Monadic/` |
| style | explicit fuel recursion, one big mutual block | do-notation over a state/error monad |
| used by | every theorem (`CallsTo`, `==>`, `CallsIn`, …), `#py_check` | `leanmodels-run`, and so `diff_test.py`, `tools/leanpy`, the coverage page |
| status | theorem statements still target the legacy deep interpreter | current definition of the published Python tier |

**Canonical statement:** theorems are stated over
`LeanModels/Python/Semantics.lean`. The shared pure-worker edge is already
kernel-checked by `twinAgrees_liftRes` and `twinAgrees_binOp` in
`Monadic/Prim.lean`; the remaining owed work is the control-level refinement
for the mutually recursive evaluators and stateful script layer.

The two interpreters share the pure workers: arithmetic, comparison,
string operations, rendering, and the dict and list primitives. Those live
in `Runtime.lean`, `Semantics.lean`'s helper sections and
`Monadic/Substrate.lean`. The control structure is written separately. New
constructs can therefore land in the monadic definition before the theorem
surface is re-founded on it; the proof interpreter may refuse programs that
the runner executes.

**How the proof interpreter is checked against CPython.**
`python3 harness/diff_test.py --proof-interpreter` runs the same
differential suite through `Semantics.lean`. A refusal there is recorded
rather than failed because that legacy theorem target is narrower. A wrong
answer, meaning a value or exception class different from CPython's, fails
exactly as it does for the runner. The monadic runner is checked separately;
these differential checks do not establish the remaining control-level
adequacy edge. Both modes run in CI, and both sets of numbers are on
[python-coverage.md](python-coverage.md).

## The proof layer

In reading order:

| file | role |
|---|---|
| `Runtime.lean` | values (`Val` at the public boundary, `RVal` inside), heap objects, `World` |
| `Semantics.lean` | the proof interpreter; `callFunction m f args fuel : Res Val` is the public entry |
| `Logic.lean` | `CallsTo`, `Raises`, the spec layer's judgments over `callFunction` |
| `Obs.lean` | fuel monotonicity and cross-fuel determinism: more fuel never changes a decided answer |
| `Surface.lean` | the typed surface (`Py*` binders, `ToVal`, `==>`/`⇓`/`==>!`/`~~>`), `py_prove`, `py_lift`, `py_corollary`, `#py_check` |
| `Delab.lean` | prints goals back in surface notation |
| `LoopTactic.lean` | `py_begin`/`py_loop` |
| `VC.lean`, `VC2.lean`, `VCTactic.lean` | flow-aware Hoare triples, loop and call rules, and the `py_vcgen` walker |
| `ClockErase.lean`, `PayloadBlind.lean`, `VCGen.lean`, … | reusable meta-theorems for stateful and clock-dependent programs; the sunfish proofs consume them from the separate sunfish repository |

A theorem such as `tri(n) ==> n * (n + 1) / 2` unfolds to
`∃ fuel, callFunction tri "tri" #[.int n] fuel = .ok (.int …)`. It is a
statement about the literal AST `tri` under `Semantics.lean`, and it
contains no axioms beyond Lean's standard three.

## Where behaviour is checked

| check | what it compares | command |
|---|---|---|
| differential suite | runner interpreter vs CPython 3.9, per function call | `python3 harness/diff_test.py` |
| proof-interpreter differential | `Semantics.lean` vs CPython 3.9, same rows | `python3 harness/diff_test.py --proof-interpreter` |
| grammar census | one witness program per CPython `ast` production | `python3 harness/refusal_census.py --grammar` |
| script corpus | whole files, stdout, exit status, and exception class | `python3 harness/script_corpus.py` |
| interpreter smoke tests | `#guard`s over the proof interpreter | built with `LeanModels.Python.Tests` |
| non-vacuity | concrete runs next to every theorem | `#py_check` lines in each `spec.lean` |

The oracle is pinned to CPython 3.9: `diff_test.py` re-executes itself under
`python3.9`, and `LEANPY_CPYTHON` overrides that. How to run the suite and
add rows: [howto/run-the-differential-harness.md](howto/run-the-differential-harness.md).
