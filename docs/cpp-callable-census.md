# C++ callable admission census

`extractors/cpp/census_callable.lean` queries the existing LP64 callable
admission boundary on a **complete** canonical probe. It does not execute a
function, compile an original artifact into a Lean literal, authenticate a
capture or prove a source program correct.

```console
lake env lean --run extractors/cpp/census_callable.lean probe.json --sources original.cpp
```

Select additional files explicitly after `--sources` to include corpus
headers. The tool resolves file identities using the filesystem in the
launch environment; run from the capture working directory when the compiler
reports relative filenames. The external receipt must pin that environment, selected
source hashes, full probe hash, frontend/plugin identities, command, time and
memory budgets. Run every Lean process under the lane's 16 GiB address-space
cap and one-worker limit. The tool itself rejects files over **128 MiB**
before reading or decoding them. A larger probe is a resource rejection,
not a semantic refusal or an execution result.

The report retains every root/`inner` occurrence of an ordinary function,
method, constructor, destructor or conversion function with a direct
`CompoundStmt` or `CXXTryStmt` child. It does not deduplicate repeated handles,
template instantiations, overloads or source sites. Prototypes and bodies
absent from the dump are outside that denominator. Implicit bodies are
reported separately from the explicit source-body totals.

## Source classification

The optional probe field `source_origin_api` names
`SourceManager expansion/spelling file locations v1`. For every
`clang::FunctionDecl`, including method subclasses, `source_origin` retains
the declared name's physical expansion and spelling filenames and byte
offsets, or explicit null for an unavailable file location. These are
`SourceManager.getExpansionLoc`, `getSpellingLoc`, `getFilename` and
`getFileOffset` observations. They do not use presumed locations, `#line`
filenames, JSON's elided location fields or sticky-file reconstruction.
The actual Clang JSON AST stays unchanged.

A body is `target-source` only when **both** physical files resolve to
explicitly selected files; `dependency` when both resolve elsewhere;
`mixed-macro` when only one is selected; and `unknown-origin` when either
location cannot be resolved. This defines declared-name origin, not ownership
of every token in the body. Cross-file macros remain visible. Missing,
malformed or conflicting origin metadata refuses the census rather than
guessing ownership from the AST. This supplementary tooling gate does not
change callable admission or require old captures to gain new semantic data.

## Admission and refusals

The complete probe passes the existing declaration parser, type-evidence,
binary-expression and expression-type validators before any body query.
Each occurrence is then passed to
`admitCallableFunctionWithExpressionTypes` with the same validated rows and
LP64 profile, including dependencies and methods that the boundary refuses.
Automatic-local variable evidence is validated by that admission function
when its body requires it.

Expression validation builds occurrence indexes once. Binary evidence keeps
its all-object traversal and **first** matching AST object; a later complete
node cannot repair an earlier stub. Expression types still join only through
root/`inner`, check every repeated AST kind, and require repeated evidence
rows to agree. Hash indexing changes lookup cost, not the acceptance rule.

The JSON report distinguishes whole-probe gates from per-body admission.
`COMPLETE` means the census finished, including its refused bodies; it does
not mean all bodies were admitted. Exit 2 and `REFUSE` name the failed stage.
External timeout, signal, memory failure and frontend failure require their
own receipt and must not be counted as semantic rejection.

`target_first_refusals` counts the existing admission function's **first**
error for each explicit target body. The full per-body `body_kinds` inventory
is raw telemetry, not a complete set of semantic blockers. Neither histogram
alone prices a new language tier. Completed reports explicitly say execution
and literal compilation were not attempted; refusal reports name their stage
and say execution was not attempted.

The focused controls are in `test_census_callable.py` (opt in with
`LEANCPP_TEST_LEAN=1` and matching `LEANCPP_CLANG` /
`LEANCPP_PROBE_LIBRARY`). They cover actual admitted and refused bodies,
dependency and macro origins, template occurrences, selected-header and
symlink handling, whole-probe validation, missing origin metadata and the
pre-read byte bound. `test_canonical_probe.py` separately checks physical
offsets and a misleading `#line` filename against the compiler's inputs.

## 2026-10-20 corpus receipt

Fresh strict C++23 captures use Clang/LLVM **21.1.8** and the current probe.
The source selection below is the XML implementation file alone, retaining
its header and standard-library bodies as dependencies.

| Input | Capture/runtime outcome | Explicit selected-source bodies admitted / refused |
| --- | --- | ---: |
| TinyXML-2 `321ea883b7190d4e85cae5512a12e5eaa8f8731f` | Complete 37,799,178-byte probe; runtime census completes | **0 / 202** |
| nlohmann/json `9cca280a4d0ccf0c08f47a99aa71d1b0e52f8d03` | Frontend exits 0 and emits 1,975,718,707 bytes; runtime parsing is outside the 128 MiB budget | **not measured** |
| Systems header | Frontend exits 1 on four anonymous-structure extension errors under `-pedantic-errors`; no probe | **not measured** |

The XML probe has SHA-256
`ddf9e49a33567a267a7bb6dcf21616eb7ba1270d406d6ecb5cf1a6b92bc0e990`.
Its **2,015** type rows, **756** binary rows and **9,677** expression-type
rows validate. The census retains **520** body occurrences: **202** selected
source bodies and **318** dependency bodies, including eleven implicit
dependency constructors. No body in either group is admitted. An independent
root/`inner` walk agrees on every path, handle, kind and selected-source
classification.

The selected source bodies are 186 methods, seven constructors, seven
destructors and two ordinary functions. Their first admission refusals are:

| First refusal | Bodies |
| --- | ---: |
| Requires ordinary `FunctionDecl` | 200 |
| Missing structured function type evidence | 1 |
| Non-integral parameter type | 1 |

These are declaration/signature gates; raw `CallExpr` presence in the two
ordinary bodies does not establish that adding calls would admit them.
The report retains each body's full raw-kind counts for further pricing.

The indexed census completes in **51.025 seconds**, with **1,784,228 KiB**
maximum child RSS, under a 300-second timeout, the 16 GiB address-space cap
and one worker. This includes Lake startup and parsing, not just validation.
The complete **353,192-byte** report is byte-identical to the completed
pre-indexing run on the same input. Exact validator snapshots also agree on
**124** small captured-probe mutation controls, including refusals.

The retained older XML probe (SHA-256
`e8db863c3f2fc3d8aaa44028d243064b7cef0d35ffe1061c9a96efd4f6185d6d`)
still refuses its eight unwitnessed binary occurrences. Fresh captures move
these observations to the refusal ledger; indexing does not repair the old
artifact. The compressed JSON capture is retained in full, but its schema
and bodies are not runtime-admitted by this measurement. The systems frontend
refusal is likewise separate from a body-admission result. No input executes
in this census, and it does not complete a C++ rung or a three-corpus semantic
census. Local launch logs, complete reports and compressed captures remain
under the worktree's `scratch/cpp-callable-census/` directory.

## Static-method follow-up

The [static integral callable extension](cpp-static-callables.md) freshly
captures the same pinned XML source with relative filenames and the static
method getter. Explicitly selecting **both** `tinyxml2.cpp` and `tinyxml2.h`
admits **one of 472 explicit source bodies**, the unchanged header helper
`XMLUtil::IsUTF8Continuation`. The original implementation-only denominator
still admits zero of 202. There are 520 retained bodies overall; the selected
header moves bodies out of the dependency group, so its 472-body denominator
must not be compared directly with the earlier 202-body implementation count.
The generated helper executes against original native calls and has a total
kernel theorem over all signed 8-bit inputs; the census itself still executes
no body and proves no program. Other inputs' previously recorded resource and
strict-frontend outcomes remain separate.
