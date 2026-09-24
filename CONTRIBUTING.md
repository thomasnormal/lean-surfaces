# Contributing

Thank you for helping. This repository holds several language tiers:
Python, SystemVerilog, C/C++, Ada, ECMAScript, and circuits. This guide
covers the **Python tier**, which is the one released as 0.1.0. The other
tiers are research in progress, with their own contracts under `docs/`.

Start with the [README quickstart](README.md#quickstart-python-tier) and
the [tutorials](docs/tutorial/index.md). How the pieces fit together is on
[docs/python-architecture.md](docs/python-architecture.md).

## What you can contribute

- **A proved example.** A Python function plus theorems about it, in
  `Examples/python/<name>/`. See "Adding an example" below.
- **A semantics bug report.** The Lean model answers differently from
  CPython 3.9 on some program. This is the most valuable report there is.
  Use the *semantics mismatch* issue template and include the smallest
  program you can find.
- **A refusal you ran into.** The model said `unsupported` for a construct
  you need. Check [docs/python-coverage.md](docs/python-coverage.md) first:
  it lists what is refused on purpose.
- **Tier work.** This means modelling a new construct. Open an issue before
  starting: a new construct touches the interpreter, the proof layer's
  meta-theorems, and the differential suite together.

## Ground rules

These are enforced by review, and several by CI.

1. **No `sorry`, no `admit`.** Not even temporarily in a pull request.
2. **Never answer wrongly; refuse loudly.** If the model cannot decide a
   construct faithfully, it must return `unsupported` with a message that
   names the construct. It must never return a guessed value or a guessed
   exception.
3. **CPython 3.9 is the oracle.** Behaviour is checked against it, not
   against a reading of the docs. Every new behaviour gets rows in
   `harness/cases.json` and must pass `python3 harness/diff_test.py`.
4. **Don't hide mismatches.** An `"expect": "unsupported"` row records a
   known refusal. It is not a way to silence a mismatch. A mismatch is a
   bug, so report it.
5. **Keep theorem statements as they are.** Never weaken, strengthen or
   "simplify" a recorded statement to make a proof go through. If a
   hypothesis turns out to be needed, that is a semantics finding. Take it
   through the differential harness first.
6. **Generated files are generated.** Don't hand-edit the `*.json`
   envelopes, `docs/python-coverage.md`, or
   `Examples/python/sum_to/SumTo.lean`. Edit the source and regenerate.
7. **Don't use `native_decide`/`bv_decide`** unless you have a reason you
   can state in one line at the use site. Include `#print axioms` for that
   theorem.

## Development loop

```console
$ lake build Examples.python.<name>.spec     # build one example (and the tier it needs)
$ lake build leanmodels-run                  # the runner the harnesses use
$ python3 harness/diff_test.py --no-build    # model vs CPython 3.9, every row
$ python3 tools/docs_check.py                # docs quote the tree verbatim
$ python3 harness/coverage_page.py --check   # the coverage page is fresh
```

You need `python3.9` on your `PATH`. `diff_test.py` re-executes itself
under it; set `LEANPY_CPYTHON` to point at a different 3.9 binary. Avoid a
bare `lake build` while iterating, since it builds every tier. CI runs the
full build on every push.

## Adding an example

Each example is a directory `Examples/python/<name>/` with three files:

- `<name>.py`: the program, as ordinary Python.
- `spec.lean`: first `#py_check` runs that show the spec is not vacuous,
  then every theorem statement, each proved `:= by proofs`.
- `proof.lean`: the real proofs, under the same theorem names, in
  `namespace Examples.python.<name>.proof`.

Steps:

1. Write `<name>.py`, then extract it:
   `python3 extractors/python/extract.py Examples/python/<name>/<name>.py`
   writes `<name>.json`, the envelope.
2. Add concrete rows for your function to `harness/cases.json` and run
   `python3 harness/diff_test.py`. It must exit 0.
3. Write `spec.lean`, starting with the `#py_check` lines. Then write
   `proof.lean`. [Examples/python/README.md](Examples/python/README.md)
   lists which existing example to copy for each proof shape. The tactic
   reference is [docs/reference.md](docs/reference.md).
4. Build it with `lake build Examples.python.<name>.spec`.

## Pull requests

Keep one logical change per pull request, and say in its description what
you checked (the loop above). If the change moves coverage, regenerate
`docs/python-coverage.md` in the same pull request. For user-visible
changes, add a line to [CHANGELOG.md](CHANGELOG.md) under
`[Unreleased]`.

## License

See [LICENSE](LICENSE). Contributions are accepted under the same license.
`Examples/python/sunfish/sunfish.py` is a vendored copy of the sunfish
chess engine and keeps its own GPL-3.0 license (see its header).
