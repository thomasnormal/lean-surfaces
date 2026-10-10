# C++ capture literals: resource pricing

Measured **2026-10-10**, against the unchanged capture loader at `752e733`.
This prices the literal-ingestion boundary in [capture provenance](cpp-provenance.md),
not C++ semantics. The original registered TinyXML2 and nlohmann/json
translation-unit/profile bundles are used whole; read-only Mox still has no
published successful receipt. This is not a repository-wide census.

## Inputs and measurement boundary

The archived probes contain **32,723,259 bytes** for XML and **1,835,697,710
bytes** for JSON. Capture and probe digests are checked before and after the
experiments, as are the loader, receipt validator, strict parser, evidence
embedding and raw AST sources. The production loader SHA-256 is
`23a707859b50031a483a32c9b1d1d5ee5cf8dae74e66969f57f791d8b50bfc85`.
Neither input is trimmed, deduplicated, regenerated under a cheaper profile,
or replaced by a small fixture.

Lean is pinned to `leanprover/lean4:v4.33.0-rc1`. Each full-artifact attempt
uses `-j1`, a **180-second wall cap**, and an inherited **8 GiB per-process
address-space limit** with `-M8192`, except the explicitly named 16 GiB JSON
sensitivity control. Limits are applied by `/usr/bin/prlimit`, not a threaded
Python `preexec_fn`. Address space is not resident memory or an aggregate
process-tree budget. Larger caller budgets are experiments, not new defaults
or admission rules.

An external copy of `CaptureLoad.lean` adds monotonic phase markers, splits
`parseDeclarationProbeString` into its exact existing parser/validator
composition, and names the `Lean.toExpr` result before the existing
`addAndCompile`. It keeps every payload check and raw observation. A second
external copy appends and flushes markers to a file: Lean redirects ordinary
elaboration output, and an OOM can lose buffered markers. No instrumentation,
cache, new fast path or altered budget is added to the production loader.

RSS from `wait4` is the completed controller child's measured high-water
mark, including descendants it reaped. Killing the whole process group can
prevent that accounting from incorporating Lean: timeout rows instead name
a separately sampled Lean high-water lower bound. The corrected sampler
unions **all** `/proc/PID/task/TID/children` files. The initial leader-only
sampler saw Lake but missed its worker-spawned Lean process; its sample files
are retained as defective instrumentation, not Lean memory measurements.

## Default and finite-budget outcomes

| Whole XML attempt | Seconds | Measured RSS, KiB | Outcome |
| --- | ---: | ---: | --- |
| Original public loader | 39.510 | 2,808,412 | LCNF 200,000-heartbeat refusal |
| Instrumented, original defaults | 39.112 | 2,808,344 | Same LCNF refusal |
| Instrumented, `Elab.async false` | 40.430 | 2,754,248 | Same LCNF refusal |
| Heartbeats 2,000,000 | 41.519 | 2,811,920 | Recursion-depth refusal |
| Heartbeats 2,000,000, depth 4,096, synchronous checking | 42.324 | 2,755,136 | Recursion-depth refusal |
| `compiler.extract_closed false`, synchronous checking | 39.917 | 2,758,920 | LCNF 200,000-heartbeat refusal |
| Experimental kernel-only registration, synchronous checking | 28.678 | 1,870,576 | Kernel literal and two `rfl` witnesses pass; executable compilation not requested |

The closed-extraction control still reaches the same first compiler error;
downstream fixture elaboration after that error is not validation. Heartbeats
are not seconds, and the command's limit must not be attributed exclusively
to the final compiler phase. The tenfold heartbeat control merely exposes
another limit; it does not establish that unbounded compilation would finish.

The public JSON loader refuses with internal OOM at **27.183 seconds /
3,376,008 KiB**; its buffered instrumented 8 GiB control does likewise at
**24.475 seconds / 3,376,928 KiB**. No full public-loader compilation completes
for either original artifact in these default or finite-budget controls.
Printed `#check` output or a later command's sentinel is explicitly
insufficient: Lean can continue elaborating after the loader reports an
error, and complete process failure remains failure.

## Phase localization and controls

XML completes payload binding, UTF-8 decoding, strict raw parsing, full typed
validation and conversion to a literal expression before its compiler
refusal. In the ordinary asynchronous configuration, an
`add-and-compile-end` marker can appear **before** the eventual error; it
records API return, not completed compilation. The synchronous control has
no such completion marker. Compilation success always requires the entire
Lean process to finish successfully.

The corrected thread-aware XML repeat measures **6.539 seconds** for strict
raw parsing, **0.767 seconds** for typed validation and **0.426 seconds** for
`ToExpr`. Its sampled peak `VmRSS` is **2,817,620 KiB**, whereas its completed
`wait4` receipt records **2,800,400 KiB**; the discrepancy is retained, not
silently reconciled. These unreplicated phase timings identify work to price,
not an allocation breakdown or an optimization speedup.

The flushed JSON trace under 8 GiB reaches `probe-utf8-start` without
`probe-utf8-end`; no raw-parse marker is reached. Under 16 GiB it completes
UTF-8 decoding and enters strict raw parsing, but does not finish that phase
within the wall cap. This localizes two different resource barriers; it does
not blame XML's LCNF compiler for JSON's default failure, infer a fixed
allocation multiplier, or establish that parsed JSON would fit in memory.

| Flushed JSON trace, corrected sampler | Seconds | Sampled Lean high-water, KiB | Outcome |
| --- | ---: | ---: | --- |
| 8 GiB, otherwise original defaults | 23.700 | 3,336,040 | OOM between UTF-8 markers; exit 1 |
| 16 GiB sensitivity | 180.537 | 6,797,424 | Raw-parse wall timeout; exit -9 |

The 16 GiB trace completes UTF-8 decoding in **3.841 seconds**. Its timeout
controller's own `wait4` value, **836,328 KiB**, omits the killed Lean child's
peak and must not replace the sampled figure. Sampling has a nominal
0.1-second interval; the controller's reported elapsed time includes polling
and final process-group termination, not an exactly 180-second completed
parse. Neither trace reaches typed validation or literal compilation.

Import-only controls pass at **17.652 seconds / 1,581,300 KiB** for the public
loader and **17.652 seconds / 1,577,448 KiB** for the durable instrument module.
The actual eight-row module bundle passes the same two guards under both
original and ordinary instrumented loading: **19.263 seconds / 1,635,620
KiB**, and **21.167 seconds / 1,638,860 KiB**, respectively. The durable-marker
control also passes at **17.550 seconds / 1,648,456 KiB**. These controls rule
out an unconditionally failing instrument; their wall-time differences are
not isolated marker overhead or throughput estimates. Runs share a host and
have import, filesystem and scheduling effects.

Kernel-only XML registration uses the identical safe literal expression with
`Lean.addDecl` and `Elab.async false`; receipt schema and AST-root witnesses
close by `rfl`. This demonstrates kernel feasibility for the unchanged XML
literal, **not** success of `load_cpp_capture`'s executable compilation.
It omits LCNF/IR/code generation, does not register postponed compilation,
and does not establish general `#eval` or downstream executable availability.
`enableRealizationsForConst` is not a substitute for generated code. The
experimental alternative therefore remains outside production.

## Representation cost and next decision

A separately bounded streaming lexical/structural pass measures JSON's
original value spans without loading it into Python memory:

| Span, including internal whitespace | Bytes | Share of entire probe |
| --- | ---: | ---: |
| Raw AST value | 1,722,577,981 | 93.83778% |
| Metadata value | 113,119,708 | 6.16222% |
| Of metadata: declaration-array value | 113,119,460 | Included above |
| Remaining metadata | 248 | Included above |
| Outer framing | 21 | Remainder |

The pass uses a 64 KiB buffer and a 128 MiB address-space bound, completing
in **2.503 seconds / 17,408 KiB**. These are byte spans, not semantic node or
declaration counts. Dropping the AST would remove most bytes but violate the
literal-observation contract; it is not an optimization of the same input.

The embedding retains raw metadata and typed declaration rows, including
each `row.raw`. Derived `ToExpr` also emits list/pair scaffolding and typed
fields; it is not a general serializer that preserves heap sharing.
Parser and validator temporaries add costs, but no fixed memory multiplier
or complete allocation breakdown is measured here. Strings use literal
strings rather than an inferred character-list expansion.

**Decision:** keep public loading unchanged. Price general literal
organization/compiler work for XML and bounded decoding/parsing for JSON
separately before implementation. Preserve strict validation, complete raw
observations, same-byte payload binding and future executable availability;
do not use corpus-specific budgets, pruning, kernel-only success or a cached
result to claim completed public ingestion. Input-world/source-form closure,
tooling query eligibility, entity/type/template/linkage, graph consensus,
cross-TU/ODR and ISO admission remain separate barriers. C++ semantic and
runtime admissions stay **zero**.

## Receipts

Full commands, limits, diagnostics, source/input pins, instrument sources,
raw markers, sample archives and review notes are under
`/var/tmp/thomas-ahle/fleet2/state/ls-cpp/capture-pricing-20261010/`, split into
`xml/`, `json/`, `shared/` and `review/`. The prior default census remains
under `capture-ingestion-20261010/census/`; these new resource experiments
do not rewrite its outcomes or promote the observational captures to
semantic evidence.
