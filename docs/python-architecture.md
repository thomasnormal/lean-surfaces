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
   also lowers a few constructs the same way CPython's compiler does:
   methods are flattened into `"Class.method"` functions, list
   comprehensions become `list(<genexpr>)`, generator expressions become
   synthesized generator functions, and dict views and `del d[k]` become
   synthetic builtins such as `<dictkeys>`. It also recognises
   `namedtuple` definitions.
3. **Interpretation.** A definitional interpreter gives the `Module`
   meaning. It is fuel-bounded: every run ends in `.ok v`, `.exn e`,
   `.timeout` (out of fuel), or `.unsupported msg` (outside the modelled
   tier). The heap, globals, stdout and a clock trace are threaded through
   a `World` ([memory-model.md](memory-model.md)).

## Two interpreters, one set of shared workers

There are **two** definitions of the interpreter. Contributors need to
know which one a given check exercises.

| | the proof interpreter | the runner's interpreter |
|---|---|---|
| file | `LeanModels/Python/Semantics.lean` | `LeanModels/Python/Monadic/` |
| style | explicit fuel recursion, one big mutual block | do-notation over a state/error monad |
| used by | every theorem (`CallsTo`, `==>`, `CallsIn`, …), `#py_check` | `leanmodels-run`, and so `diff_test.py`, `tools/leanpy`, the coverage page |
| tier | narrower: some newer constructs refuse | the full published tier |

The two interpreters share the pure workers: arithmetic, comparison,
string operations, rendering, and the dict and list primitives. Those live
in `Runtime.lean`, `Semantics.lean`'s helper sections and
`Monadic/Substrate.lean`. Only the control structure is written twice.
New constructs land in the runner's interpreter first. As a result, some
programs run under `tools/leanpy` but cannot yet be the subject of a
theorem. For those, the proof interpreter refuses loudly.

**How the proof interpreter is checked against CPython.**
`python3 harness/diff_test.py --proof-interpreter` runs the same
differential suite through `Semantics.lean`. A refusal there is recorded
rather than failed, because its tier is narrower. A wrong answer, meaning
a value or exception class different from CPython's, fails exactly as it
does for the runner. The first run of this check found 25 rows where the
proof interpreter answered `NameError` for the synthetic dict-view and
`del d[k]` builtins it does not model. The fix is `isLoweredBuiltinName`:
those rows now refuse. Both modes run in CI, and both sets of numbers
are on [python-coverage.md](python-coverage.md).

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
| `ClockErase.lean`, `PayloadBlind.lean`, `VCGen.lean`, … | meta-theorems for stateful and clock-dependent programs (developed for the sunfish proofs, now in the sunfish repository) |

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
| script corpus | whole files, stdout and exit status | `python3 harness/script_corpus.py` |
| interpreter smoke tests | `#guard`s over the proof interpreter | built with `LeanModels.Python.Tests` |
| non-vacuity | concrete runs next to every theorem | `#py_check` lines in each `spec.lean` |

The oracle is pinned to CPython 3.9: `diff_test.py` re-executes itself under
`python3.9`, and `LEANPY_CPYTHON` overrides that. How to run the suite and
add rows: [howto/run-the-differential-harness.md](howto/run-the-differential-harness.md).
