# How to run the differential harness

The harness runs each case on CPython *and* on the Lean interpreter (via
`lake exe leanmodels-run`) and compares canonical results. This is mandatory
methodology, not hygiene: every specced function gets differentially tested
**before** proving — it caught the `gcd` sign bug
([spec-surface.md §3](../spec-surface.md)). Format contract:
[DESIGN.md](../DESIGN.md), "Runner + differential harness".

## Run it

From anywhere (the script re-roots itself at the repo root):

```
python3 harness/diff_test.py
```

It runs `lake build` once up front, then prints a table
(`case | cpython | lean | verdict`) and a summary line like:

```
103 cases: 0 failed, 2 whitelisted-unsupported, 101 matched
```

Exit status is non-zero on any non-whitelisted mismatch. Flags: `--no-build`
(skip the up-front build), `--fuel N` (pass to the runner; default 10000),
`--cases FILE`, `--runner CMD`.

The harness is one third of the full check triad —
`lake build && python3 tools/docs_check.py && python3 harness/diff_test.py`
— the standard gate before finishing any change (proofs or docs).

To probe a single call by hand, use the runner directly — one JSON line on
stdout, exit 0 for every *semantic* result (`exn`/`timeout`/`unsupported`
are results, not failures):

```
lake exe leanmodels-run Examples/python/tri.json tri 10
{"status":"ok","value":{"t":"int","v":"55"}}
```

## Add cases

`harness/cases.json` is a JSON array; one row per (file, function), with a
list of argument tuples. Real rows:

```json
[
  {"file": "Examples/gcd/gcd.py", "function": "gcd", "args": [[12, 18], [18, 12], [5, 0], [0, 5], [7, 13], [0, 0], [270, 192], [4, -6], [-4, 6], [-6, -4]], "expect": "match"},
  {"file": "Examples/python/arith.py", "function": "powi", "args": [[2, -1]], "expect": "unsupported"}
]
```

- `file` — repo-relative path to the `.py` source. The harness imports it by
  path and expects the extractor-generated envelope `<file>.json` next to it
  (run `python3 extractors/python/extract.py <file>` first).
- `function` — module-level function name.
- `args` — a list of argument lists (integers only; the runner parses args
  as arbitrary-precision ints). Functions taking non-int arguments (lists,
  strings) therefore have no expressible rows in v0: cover their concrete
  behavior with `#py_check` lines in the source file — the surface command
  takes full terms — and record the gap in the file's non-vacuity block.
  [`Examples/python/ag_head.py`](../../Examples/python/ag_head.py) is the
  pattern.
- `expect` — `"match"` (default): CPython and Lean canonical outcomes must
  be equal, exceptions included (compared by canonical class name —
  [reference, error classes](../reference.md#error-classes)).
  `"unsupported"`: whitelists a documented v0 tier gap — the row passes iff
  the Lean side reports `{"status":"unsupported"}`; CPython's answer is shown
  for information only.

Choose inputs that probe the semantic decisions, not just the happy path:
negative operands for `//`/`%` (sign behavior), zero divisors, empty/edge
indices, both short-circuit outcomes. The `gcd` row above exists precisely
because `gcd(4, -6)` distinguishes `Int.fmod` from `Int.emod`.

## What can go wrong

**Mismatch.** The table shows both sides; the run exits 1. Reproduced with a
scratch case file (`half` is `a / 2` — true division is outside the v0 tier —
run with `"expect": "match"`; `double` is `a * 2`, wrongly whitelisted as
`"expect": "unsupported"`):

```
case       cpython                 lean         verdict
-------------------------------------------------------------------------------
half(4)    ok: <unmappable float>  unsupported  MISMATCH
double(4)  ok: 8                   ok: 8        MISMATCH (expected unsupported)
-------------------------------------------------------------------------------
2 cases: 2 failed, 0 whitelisted-unsupported, 0 matched
```

Three distinct situations hide in there:

- A value mismatch on a supported construct means the Lean semantics
  disagrees with CPython on that input — an interpreter bug, or a semantic
  subtlety you want to know *before* proving. Do not whitelist it.
- `ok: <unmappable float>` — CPython returned a value outside the canonical
  set. It can never `match`; if the Lean side is `unsupported`, whitelist the
  row (`"expect": "unsupported"`) — that is exactly the checked-in
  `powi [[2, -1]]` row, and the fix for `half(4)` above.
- `MISMATCH (expected unsupported)` — your whitelisted row actually
  evaluates (the tier grew, or the row was wrong). Set
  `"expect": "match"`.

**`{"status":"timeout"}`.** Fuel ran out (e.g. `--fuel 3` on `tri 10`).
Raise `--fuel`; if it persists, the function may not terminate on that input.

**Non-integer arguments.**

```
leanmodels-run: arguments must be integers, got 'x'
usage: leanmodels-run <envelope.json> <function> [args...] [--fuel N]
  args are parsed as (arbitrary-precision) integers; default fuel 10000
```

The runner (and therefore the harness `args`) only takes ints in v0. Note a
misspelled function is *not* a runner error — it is a faithful semantic
result: `{"status":"exn","exn":"NameError"}`.

**Relative `--cases` path not found.** The script `chdir`s to the repo root
before reading the case file, so a `--cases` path relative to *your* cwd
fails with `FileNotFoundError`. Pass a repo-root-relative or absolute path.

**Stale envelope.** The harness runs CPython on the `.py` but Lean on the
`.json`; if you edited the source and forgot to re-extract, the two are
different programs. Re-run the extractor.
