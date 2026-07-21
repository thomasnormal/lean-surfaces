# SV corpus coverage census — sv-tests-2 vs the M0 extractor

Axis-1/2 coverage of the M0 tier (`docs/sv-design-m0.md`, envelope schema
`sv-0.1`) measured on real code: every `.sv` file under
`/home/thomas-ahle/mox/sv-conformance/sv-tests-2/tests/chapter-*/`
(the IEEE 1800-2023 conformance corpus, self-checking PASS/FAIL tests), run
through the `extractors/sv/extract.py` pipeline **in-process** by
`extractors/sv/census.py`.

Reproduce (from the repo root):

```
python3.12 extractors/sv/census.py            # full census, ~4 s at 32 jobs
python3.12 extractors/sv/census.py --recheck  # fixed-seed 200-file determinism check
```

Machine-readable results: `harness/sv/conformance/census.json`
(per-file records + this document's aggregates). Census date: 2026-07-21,
pyslang 11.0.0.

## Method

* **Walk**: 21,336 `.sv` files in `tests/chapter-3` … `chapter-40` (445
  additional `.sv` files sit directly under `tests/` outside any chapter and
  are out of scope). Metadata (`:name:`/`:tags:`/`:type:`) parsed from each
  header; 1,366 files have no `:type:` line.
* **Pipeline**: the worker calls the same functions `extract.process_file`
  calls (`SyntaxTree.fromText` → `Compilation` → `convert_design`) without
  writing `.sv.json` files into the corpus. Cross-validated on 40 random
  files against the `extract.py` CLI: identical Unsupported sets.
* **Classes**:
  * `skip_include` — the file has a real `` `include `` directive
    (multi-file test; a single-file compile would classify a partial parse,
    so these are skipped with reason). 29 files, 27 of them in chapter-22.
  * `error` — the pipeline raised, or hit the 90 s per-file alarm.
  * `clean` — envelope has **zero** `Unsupported` nodes.
  * `partial` — envelope has `Unsupported` nodes; the distinct `sv_kind`
    values are recorded per file.
* **Determinism**: `--recheck` re-runs a seed-20260721 sample of 200 files
  and compares (status, kinds, adapter blockers, unlockable) — **200/200
  identical** on this census.
* **Runtime**: full census in **3.9 s** (32 workers, 96-core host) — far
  under the 15 min target; the corpus is many small files and pyslang's
  parser is C++.

## (a) Headline counts

| class | files | share |
|---|---:|---:|
| partial | 21,278 | 99.73% |
| clean | 29 | 0.14% |
| skip_include | 29 | 0.14% |
| **EXTRACT-ERROR** | **0** | 0% |
| total | 21,336 | |

Clean by `:type:` (clean / total of that type):

| :type: | clean / total | note |
|---|---:|---|
| simulation | 5 / 18,001 | all 5 are pragma/`protect` tests; 3 have **zero modules** (vacuously clean), none prints PASS via M0 constructs |
| compile_error | 18 / 1,747 | negative tests: *illegal* SV that happens to parse into M0 vocabulary — see robustness notes |
| shell / compile_warning / (none) | 6 / 1,435 | |

The corpus-wide truth: **no self-checking simulation test is runnable at
M0**, because self-checking requires `initial` + `$display`, both outside
the tier — exactly the Adapter phase's motivation.

## (b) Construct-frequency table — THE IMPLEMENTATION PRIORITY QUEUE

Number of `partial` files whose envelope contains each `sv_kind`
(a file counts once per distinct kind), top 60, sorted descending. **This
table is the implementation priority queue for growing the tier**: each row
is "how many corpus files stop being blocked-by-this if the construct is
implemented".

> Caveat: the extractor collapses whole out-of-tier *processes* into a
> single `Unsupported` node, so `ProceduralBlockSymbol:Initial` (row 1)
> hides everything inside `initial` bodies. Section (e) re-measures the
> queue with the adapter tier treated as supported — that residual table is
> the true post-Adapter queue.

| sv_kind | files blocked |
|---|---:|
| `ProceduralBlockSymbol:Initial` | 20569 |
| `VariableSymbol:2state` | 6911 |
| `InstanceSymbol:Instance` | 3658 |
| `ConversionExpression:width` | 3231 |
| `TimedStatement:DelayControl` | 2673 |
| `SubroutineSymbol:Subroutine` | 1414 |
| `ClassType` | 1289 |
| `ProceduralBlockSymbol:NoEventControl` | 1274 |
| `PrimitiveInstanceSymbol:PrimitiveInstance` | 1016 |
| `VariableSymbol:signed` | 839 |
| `TypeAliasType:TypeAlias` | 799 |
| `PackageSymbol` | 735 |
| `VariableSymbol:type` | 709 |
| `CovergroupType:CovergroupType` | 652 |
| `CheckerSymbol` | 563 |
| `ClockingBlockSymbol:ClockingBlock` | 549 |
| `CheckerInstanceSymbol:CheckerInstance` | 534 |
| `ParameterSymbol:Parameter` | 518 |
| `ClassType:ClassType` | 503 |
| `PropertySymbol:Property` | 464 |
| `WildcardImportSymbol:WildcardImport` | 371 |
| `PrimitiveSymbol` | 371 |
| `ConfigBlockSymbol` | 271 |
| `SequenceSymbol:Sequence` | 261 |
| `GenerateBlockArraySymbol:GenerateBlockArray` | 258 |
| `GenerateBlockSymbol:GenerateBlock` | 250 |
| `TransparentMemberSymbol:TransparentMember` | 239 |
| `TypeAliasType` | 205 |
| `GenvarSymbol:Genvar` | 195 |
| `InstanceArraySymbol:InstanceArray` | 182 |
| `AssignmentExpression:target` | 180 |
| `SignalEventControl:None_` | 149 |
| `GenericClassDefSymbol` | 137 |
| `SubroutineSymbol` | 119 |
| `ExplicitImportSymbol:ExplicitImport` | 104 |
| `VariableSymbol:range` | 92 |
| `ExpressionStatement:UnaryExpression` | 90 |
| `ProceduralBlockSymbol:Final` | 83 |
| `VariableSymbol` | 76 |
| `NetSymbol:Tri` | 66 |
| `RangeSelectExpression` | 63 |
| `CallExpression` | 56 |
| `NetSymbol:Supply1` | 56 |
| `NetSymbol:WAnd` | 53 |
| `SignalEventControl:clock` | 53 |
| `NetSymbol:TriReg` | 53 |
| `NetSymbol:WOr` | 50 |
| `TransparentMemberSymbol` | 50 |
| `TimedStatement:ImplicitEventControl` | 49 |
| `SpecifyBlockSymbol:SpecifyBlock` | 49 |
| `EmptyMemberSymbol:EmptyMember` | 48 |
| `CaseStatement` | 48 |
| `NetSymbol:Supply0` | 47 |
| `PortSymbol:2state` | 42 |
| `GenericClassDefSymbol:GenericClassDef` | 39 |
| `NetSymbol:UserDefined` | 38 |
| `DefParamSymbol:DefParam` | 37 |
| `NetType` | 34 |
| `TimedStatement:EventListControl` | 33 |
| `LetDeclSymbol:LetDecl` | 33 |

## (c) Per-chapter coverage

| chapter | total | clean | partial | skip | clean % |
|---|---:|---:|---:|---:|---:|
| chapter-3 | 232 | 1 | 230 | 1 | 0.4% |
| chapter-4 | 424 | 0 | 424 | 0 | 0.0% |
| chapter-5 | 613 | 0 | 613 | 0 | 0.0% |
| chapter-6 | 1155 | 0 | 1155 | 0 | 0.0% |
| chapter-7 | 771 | 0 | 771 | 0 | 0.0% |
| chapter-8 | 805 | 0 | 805 | 0 | 0.0% |
| chapter-9 | 563 | 0 | 563 | 0 | 0.0% |
| chapter-10 | 629 | 3 | 626 | 0 | 0.5% |
| chapter-11 | 1014 | 0 | 1014 | 0 | 0.0% |
| chapter-12 | 596 | 0 | 596 | 0 | 0.0% |
| chapter-13 | 597 | 0 | 597 | 0 | 0.0% |
| chapter-14 | 464 | 0 | 464 | 0 | 0.0% |
| chapter-15 | 523 | 0 | 523 | 0 | 0.0% |
| chapter-16 | 1511 | 0 | 1511 | 0 | 0.0% |
| chapter-17 | 510 | 0 | 510 | 0 | 0.0% |
| chapter-18 | 816 | 0 | 816 | 0 | 0.0% |
| chapter-19 | 695 | 0 | 695 | 0 | 0.0% |
| chapter-20 | 782 | 0 | 782 | 0 | 0.0% |
| chapter-21 | 857 | 0 | 857 | 0 | 0.0% |
| chapter-22 | 567 | 4 | 536 | 27 | 0.7% |
| chapter-23 | 814 | 3 | 811 | 0 | 0.4% |
| chapter-24 | 347 | 4 | 343 | 0 | 1.2% |
| chapter-25 | 473 | 1 | 472 | 0 | 0.2% |
| chapter-26 | 562 | 0 | 562 | 0 | 0.0% |
| chapter-27 | 350 | 0 | 350 | 0 | 0.0% |
| chapter-28 | 721 | 0 | 721 | 0 | 0.0% |
| chapter-29 | 352 | 0 | 352 | 0 | 0.0% |
| chapter-30 | 427 | 0 | 427 | 0 | 0.0% |
| chapter-31 | 501 | 0 | 501 | 0 | 0.0% |
| chapter-32 | 286 | 0 | 286 | 0 | 0.0% |
| chapter-33 | 267 | 1 | 266 | 0 | 0.4% |
| chapter-34 | 228 | 12 | 215 | 1 | 5.3% |
| chapter-35 | 256 | 0 | 256 | 0 | 0.0% |
| chapter-36 | 720 | 0 | 720 | 0 | 0.0% |
| chapter-37 | 417 | 0 | 417 | 0 | 0.0% |
| chapter-38 | 340 | 0 | 340 | 0 | 0.0% |
| chapter-39 | 64 | 0 | 64 | 0 | 0.0% |
| chapter-40 | 87 | 0 | 87 | 0 | 0.0% |
| **total** | **21336** | **29** | **21278** | **29** | **0.14%** |

(Chapter-34 leads only because `pragma protect` envelopes elaborate to
empty/trivial designs; chapter-24's cleans are illegal-`program` negative
tests. No clean row represents a runnable self-checking test.)

## (d) M0-relevant deep-dive: chapters 4, 6, 11 — the unlockable set

**Definition (precise).** The Adapter phase's self-check tier extends M0
with exactly: `initial` blocks, `$display`/`$finish` calls, string
literals, and local variable declarations (M0-typed: unsigned 4-state
scalar or `[W-1:0]`, with M0/string initializers). A test is **unlockable**
iff it is `partial`, has ≥ 1 module, and re-walking its *elaborated AST*
with those four constructs treated as supported leaves zero blockers —
i.e. `initial` bodies are descended into (the envelope collapses them into
one `Unsupported` node, so envelope tags alone cannot decide this) and
everything inside must be M0 vocabulary (`begin/end`, `=`, `<=`, `if/else`,
M0 expressions) or the four constructs; `$display`/`$finish` arguments may
be string literals or M0 expressions; `$display` is likewise accepted
inside `always` bodies. Counts below are over `:type: simulation` tests.

| chapter | sim tests | clean | partial | **unlockable** | blocked by more |
|---|---:|---:|---:|---:|---:|
| chapter-4 | 420 | 0 | 420 | **0** | 420 |
| chapter-6 | 1011 | 0 | 1011 | **3** | 1008 |
| chapter-11 | 974 | 0 | 974 | **8** | 966 |

The 11 files are listed in `harness/sv/conformance/unlockable.txt`
(corpus-relative paths). Corpus-wide the same definition unlocks **265**
simulation tests (421 files counting non-simulation types).

**The four-construct tier is necessary but nowhere near sufficient for
these chapters.** What still blocks the rest (top residual blockers among
non-unlockable simulation tests, per chapter):

| chapter-4 | files | chapter-6 | files | chapter-11 | files |
|---|---:|---|---:|---|---:|
| `TimedStatement:DelayControl` | 346 | `AssignmentExpression:target` | 543 | `AssignmentExpression:target` | 549 |
| `ConversionExpression:width` | 202 | `VariableSymbol:2state` | 449 | `BinaryExpression:CaseEquality` | 383 |
| `VariableSymbol:2state` | 155 | `NamedValueExpression:2state` | 420 | `NamedValueExpression:2state` | 305 |
| `BinaryExpression:CaseEquality` | 143 | `BinaryExpression:LogicalAnd` | 314 | `VariableDeclStatement:2state` | 273 |
| `AssignmentExpression:target` | 140 | `VariableDeclStatement:2state` | 224 | `BinaryExpression:LogicalAnd` | 209 |
| `NamedValueExpression:2state` | 132 | `TypeAliasType:TypeAlias` | 216 | `BinaryExpression:CaseInequality` | 203 |
| `BinaryExpression:LogicalAnd` | 121 | `BinaryExpression:CaseEquality` | 215 | `VariableSymbol:2state` | 166 |
| `BinaryExpression:CaseInequality` | 69 | `CallExpression` | 198 | `ConversionExpression:width` | 119 |
| `InstanceSymbol:Instance` | 51 | `BinaryExpression:CaseInequality` | 187 | `NamedValueExpression:signed` | 101 |
| `TimedStatement:SignalEventControl` | 37 | `TimedStatement:DelayControl` | 169 | `VariableDeclStatement:signed` | 84 |

Chapter 4 (scheduling) is structurally about `#delay`/event control — its
unlockable set is empty because nearly every test *is about* timing.
Chapters 6/11 are dominated by 2-state types (`int`/`bit` locals and
module vars), `===`/`!==`, `&&`/`||`, and bit/part-select assignment
targets (`AssignmentExpression:target`).

Greedy increments — each row adds one construct to the adapter tier and
shows the cumulative unlockable count over ch. 4/6/11 simulation tests
(base 11):

| + construct | cumulative unlockable (ch 4/6/11) |
|---|---:|
| `BinaryExpression:CaseEquality` (`===`) | 71 |
| `BinaryExpression:CaseInequality` (`!==`) | 126 |
| `TimedStatement:DelayControl` (`#d`) | 167 |
| `ConversionExpression:width` (implicit resize) | 227 |
| `InstanceSymbol:Instance` (hierarchy) | 300 |
| `BinaryExpression:LogicalAnd` (`&&`) | 359 |
| `RangeSelectExpression` (`[a:b]`) | 378 |
| `ConversionExpression:StreamingConcat` | 397 |
| `BinaryExpression:LogicalOr` (`\|\|`) | 415 |
| `PrimitiveInstanceSymbol:PrimitiveInstance` | 431 |

`===`/`!==` is the single cheapest high-yield add (the Lean value core
`LeanModels/Sv/Basic.lean` already has the case-equality ops — this is
extractor-vocabulary + envelope work only).

## (e) The post-Adapter priority queue (corpus-wide, simulation tests)

Residual blocker frequency over all non-unlockable `partial` simulation
tests with the adapter tier treated as supported — the *true* queue once
initial bodies are visible (top 30; `Call:<name>` = a call other than
`$display`/`$finish`):

| adapter-residual blocker | sim files blocked |
|---|---:|
| `AssignmentExpression:target` | 7498 |
| `TimedStatement:DelayControl` | 7343 |
| `NamedValueExpression:2state` | 6357 |
| `VariableSymbol:2state` | 6158 |
| `ConversionExpression:width` | 4746 |
| `BinaryExpression:LogicalAnd` | 4688 |
| `VariableDeclStatement:2state` | 3792 |
| `InstanceSymbol:Instance` | 3219 |
| `BinaryExpression:CaseEquality` | 3215 |
| `BinaryExpression:CaseInequality` | 2325 |
| `CallExpression` | 2235 |
| `RepeatLoopStatement` | 1214 |
| `SubroutineSymbol:Subroutine` | 1175 |
| `ClassType` | 1086 |
| `ProceduralBlockSymbol:NoEventControl` | 1068 |
| `TimedStatement:SignalEventControl` | 1031 |
| `PrimitiveInstanceSymbol:PrimitiveInstance` | 921 |
| `NewClassExpression` | 857 |
| `MemberAccessExpression` | 830 |
| `InvalidStatement` | 797 |
| `VariableSymbol:signed` | 763 |
| `ElementSelectExpression` | 747 |
| `HierarchicalValueExpression` | 745 |
| `TypeAliasType:TypeAlias` | 696 |
| `NamedValueExpression:signed` | 640 |
| `VariableSymbol:type` | 634 |
| `PackageSymbol` | 597 |
| `CovergroupType:CovergroupType` | 558 |
| `ClockingBlockSymbol:ClockingBlock` | 450 |
| `BinaryExpression:LogicalOr` | 443 |

The corpus-wide greedy sequence (simulation, base 265):
`InvalidStatement`→578, `+InstanceSymbol:Instance`→887,
`+TimedStatement:DelayControl`→1014, `+BinaryExpression:CaseEquality`→1378,
`+ConversionExpression:width`→1909, `+BinaryExpression:CaseInequality`→2399,
`+PrimitiveInstance`→2842, `+PrimitiveSymbol`→3119. Headline: the
four-construct adapter tier + {`===`, `!==`, `#delay`, width-changing
implicit conversions, bit/part-select targets, 2-state locals} is the
shortest path to a four-digit conformance suite.

## Extractor robustness notes (observed, not fixed)

1. **Zero crashes.** 21,307 single-file compiles (including 1,747
   deliberately-illegal `compile_error` tests): 0 pipeline exceptions,
   0 `ExtractorInternal:*` nodes, 0 per-file timeouts. The "never fails on
   valid SV" guarantee empirically extends to invalid SV.
2. **`clean` does not imply valid SV.** `extract.py` never consults
   compilation diagnostics, so 18 of the 29 clean files are
   `:type: compile_error` negative tests (e.g.
   `chapter-10/10.3.2--variable-only-one-continuous-assignment-driver.sv`:
   two continuous assigns to one variable — illegal, but every node is M0
   vocabulary). Any conformance harness built on envelopes must gate on
   `:type:` (or on slang diagnostics) before trusting a clean envelope.
3. **Signedness gap at the expression level** (tier-boundary bug worth a
   decision): `type_width` rejects *declared* signed types, but signed
   **expressions** pass through — `if (-1 < 0)` extracts with no
   `Unsupported` marker (`-1` is a signed 32-bit `IntegerLiteral`, `<`
   compares signed in SV), yet `LeanModels/Sv/Basic.lean` comparisons are
   unsigned, so the M0 evaluator would compute `-1 < 0` = false. The
   envelope's `Literal`/`Binary` nodes carry no signedness. None of the 11
   ch-4/6/11 unlockable files hits this (verified by inspection: their
   comparisons are unsigned or non-negative), but the Adapter phase should
   either mark signed-operand comparisons `Unsupported` in the extractor or
   add signedness to the envelope before scaling to the corpus.
4. **`InvalidStatement` clusters on unknown system calls**: 797 simulation
   files carry it, 313 of them as their *only* adapter-residual blocker —
   overwhelmingly slang marking statements bad around system functions it
   doesn't accept in that form (`$abs(-5)`, `$test$plusargs(vector)`, …).
   These are slang-frontend conformance gaps, not extractor bugs; they cap
   the reachable suite regardless of Lean-side work.
5. **Multi-file tests**: 29 files use real `` `include `` directives (27 in
   chapter-22). `extract.py` compiles single files with no include path, so
   the census skips them with reason rather than misclassifying a partial
   parse. Supporting them needs an include-dir argument in `extract.py`
   (one-line `SyntaxTree.fromText` change) — deferred.

## Artifacts

* `extractors/sv/census.py` — the census tool (python3.12; `--recheck`,
  `--limit`, `--jobs`, `--corpus`).
* `harness/sv/conformance/census.json` — 21,336 per-file records
  (path, chapter, metadata, status, envelope kinds, adapter blockers,
  unlockable flag) + the summary block backing every table above.
* `harness/sv/conformance/unlockable.txt` — the 11 ch-4/6/11 unlockable
  simulation tests, one corpus-relative path per line.
