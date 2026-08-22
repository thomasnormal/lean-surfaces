# The WebAssembly tier: FOUNDING CHARTER

**Status: the workstream's founding document, and the family's CALIBRATION
MEMBER.** Thomas's family directive asks for versioned, spec-mirrored
language surfaces. Every tier so far has had to bridge a gap between a
prose standard and a formal surface, and has had to *invent* the
correspondence: `docs/c-tier-charter.md` censuses a C *corpus* because there
is nothing to census on ISO 9899's side except English.

WebAssembly is the tier where that gap is smallest. Its core specification
contains genuine small-step reduction rules and a typing judgment, written
as inference rules, and since Wasm 3.0 the working group maintains them in a
machine-readable DSL — SpecTec — **one directory per version, inside the
spec repository itself**. So this charter's job is not only to plan a tier.
It is to say precisely **how the family's laws apply when the spec is
ALREADY formal**, because that is the measurement every other tier's
correspondence should be calibrated against.

**It recommends a target version and a rung 0. It recommends no endgame.**
§7 lists what Thomas still has to answer.

**Census first, per §L25.** Every number below was measured today by an
instrument that lands with this charter, on a pinned revision. Nothing is
quoted from memory. Machine-readable rows in `docs/wasm-spec-census.json`
and `docs/wasm-suite-census.json`.

**No semantics were built this pass.** No Lean.

---

## 0 THE TWO INSTRUMENTS, AND WHY THERE ARE TWO

| instrument | subject | sibling |
| --- | --- | --- |
| `harness/wasm_spec_census.py` | the **specification's own formal rules** | **none — see below** |
| `harness/wasm_suite_census.py` | the official `test/core` conformance suite | `harness/c_suite_census.py` |

The second has a sibling; the first does not, and its absence from the C
tier is the calibration lesson in one line. `harness/c_construct_census.py`
censuses `sunfish.c` — a *program*. There is no instrument in this
repository that censuses the C *standard*, because ISO 9899 is prose and
prose does not have a rule count. **WebAssembly's does**, so the spec is a
censusable artifact and drift in it is a diff rather than a reading.

Both obey the house laws. Output is sorted and **a double run is
byte-identical (verified, both instruments)**. Both carry `--compare` so
cross-repo staleness is mechanically detectable — the corpus lives in
another repository and moves on its own schedule, which is exactly the
condition that made the C tier's census stale by one engine release
(§L35). Both are deliberately **NOT wired into `tools/ci.sh`**, for the
reason `harness/c_suite_census.py` is not: the tree is not in this
repository and not on a stock runner, so a gate would be a permanent SKIP
pretending to be a check.

**Six refusal paths were RUN, not admired.** A missing tree; a tree with no
`specification/`; a version directory with zero `.spectec` files; a
`test/core` with zero `.wast` files; a `.wast` whose parentheses do not
balance; a `.wast` with an unterminated string literal. All six exit 2 with
a message naming the fault. An empty census is an instrument fault, never a
finding.

The `.wast` scanner blanks `;;` line comments, nestable `(; … ;)` block
comments and **the contents of string literals while preserving byte
offsets**. The last is not fastidiousness: `.wast` string literals routinely
contain parentheses and semicolons, so a scanner that read them as syntax
would mis-nest and silently produce a plausible wrong table — the same
failure class as the C census's partial-AST defect (§L35).

**Pinned revision for every number in this document:** `WebAssembly/spec`
at `fc209c5ed8afc4dfeb9252024d217da3376c7a6f`, which `git describe` renders
`wg-3.0-313-gfc209c5e`.

---

## 1 THE SPEC MAP

### 1.1 What "version" means for Wasm — four different things, measured

The word is overloaded and the tier has to be precise about which sense it
pins. Measured in the repository:

| sense | artifact | what the census sees |
| --- | --- | --- |
| **the W3C document version** | git tags `wg-1.0` (2024-04-17), `wg-2.0` (2025-08-28), `wg-3.0` (2025-09-26) | three suites, three rule sets |
| **the formal-rule version** | `specification/wasm-{1.0,2.0,3.0,latest}/` | four directories, all present at ONE checkout |
| **the binary format version** | the module header's `version` word | **1** in every module measured, at every language version |
| **a feature proposal** | `test/core/<name>/` subdirectories | 0 at 1.0, 1 at 2.0, 7 at 3.0 |

Two facts that matter more than they look:

**(a) The binary format version word has been `1` throughout.** Measured on
the rung-0 artifact (§5): magic `\x00asm`, version `1`. Language versioning
is *not* carried in the binary header — it is carried by which instructions
and types an implementation accepts. So a version-pinned Lean surface pins
a *vocabulary*, not a magic number, and cannot detect its own version
mismatch from the header. That is a refusal-design constraint, not a
detail.

**(b) `specification/` exists only from `wg-3.0` onward.** Measured: the
`wg-1.0` and `wg-2.0` *tags* contain no SpecTec sources at all; today's
HEAD contains `wasm-1.0/`, `wasm-2.0/`, `wasm-3.0/` and `wasm-latest/`
together. The older versions' formal rules were **back-ported into the
DSL**, and `wasm-3.0/` and `wasm-latest/` are **byte-identical** (`diff -rq`
clean). So one modern checkout is the whole versioned family, and a lane
targeting 2.0 reads today's HEAD rather than a 2025 tag. The spec repo has
already done the family's versioning work, in the family's own shape.

**The spec is machine-CHECKED per version**, not merely stored:
`specification/Makefile` carries `check-1.0`, `check-2.0`, `check-3.0` and
`check-latest` targets that run the SpecTec elaborator over each directory.

### 1.2 The rules, counted

`harness/wasm_spec_census.py` classifies each relation by the **shape of
its judgment**, never by its name — `~>` is reduction, `context |- x : t`
is validation, the rest is auxiliary. The judgment form is written down in
the spec; a name-based classification would be a guess.

| version | files | lines | relations | **rules** | validation | reduction | aux | syntax | defs | grammar |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| wasm-1.0 | 10 | 2309 | 35 | **133** | 72 | 58 | 3 | 88 | 131 | 61 |
| **wasm-2.0** | 10 | 4121 | 40 | **259** | 125 | **128** | 6 | 143 | 213 | 71 |
| wasm-3.0 | 37 | 9351 | 125 | **568** | 306 | 224 | 38 | 208 | 464 | 232 |
| wasm-latest | 37 | 9351 | 125 | 568 | 306 | 224 | 38 | 208 | 464 | 232 |

**The whole of Wasm 2.0's execution semantics is 128 named reduction
rules**, and they factor, in the spec's own structure, into four relations:

```
Step       : config ~> config             22 rules
Step_pure  : admininstr* ~> admininstr*   56 rules
Step_read  : config ~> admininstr*        47 rules
Steps      : config ~>* config             2 rules
Eval_expr  : state; expr ~>* state; val*   1 rule
```

That factoring is a gift and the tier should mirror it rather than flatten
it: **56 of 128 rules — 44% — are `Step_pure` and mention no state at
all.** A Lean surface can define, gate and reason about them with no world,
no store and no frame. The C tier has no comparable stratum; every C
statement can touch memory.

**One reconciliation, and it validates the instrument.** An independent
survey (§8) counted 3.0's reduction rules as **221**; this census says
**224**. The difference is exactly one relation: `NotationReduct` (3 rules,
form `~> instr*`), which lives in `X.3-notation.execution.spectec` and is a
*notational* device rather than a semantic relation. The shape-based
classifier catches it because its form contains `~>`; a hand count drops
it. **Both numbers are right about different things** — 221 semantic
reduction rules, 224 rules whose judgment is a reduction — and the totals
agree exactly at **568**, which is the agreement that matters. A surface
mirroring the semantics owes 221; the coverage gate should exclude
`NotationReduct` by name rather than by taste.

### 1.3 The version deltas, in the spec's own units

Because every rule has a name, "what does upgrading cost" is a set diff
rather than an estimate:

| step | added | dropped | kept |
| --- | ---: | ---: | ---: |
| wasm-1.0 → wasm-2.0 | **+128** | **−2** | 131 |
| wasm-2.0 → wasm-3.0 | **+345** | **−36** | 223 |
| wasm-3.0 → wasm-latest | 0 | 0 | 568 |

**1.0 → 2.0 drops exactly two rule names**: `Instr_ok/select` and
`Step/ctxt-instrs`. Both are refinements, not removals — `select` gains its
typed form and splits, and the contextual-step rule is restructured. So
2.0 is very nearly a *superset* of 1.0: 131 of 133 names survive verbatim.
**2.0 → 3.0 more than doubles the surface** (+345) and drops 36, most of
them trap rules absorbed into a uniform treatment (`Step/store-num-trap`,
`Step_read/load-num-trap`, `Step_read/table.get-trap`, … all gone as
separate names).

This is the number that decides §6's target: **an upgrade is enumerable,
and the 1.0→2.0 one is nearly free.**

### 1.4 How spec-mirroring works when the spec IS formal — and the correspondence is MACHINE-CHECKED

The family's other tiers must decide, editorially, what "mirrors the spec"
means. Wasm hands the answer over, and this charter's central methodological
finding is that **the spec document itself already uses the correspondence
we want**.

`document/core/**/*.rst` — the published specification — no longer writes
its rules out. It **splices** them from SpecTec, by name:

```
$${rule: Instr_ok/br_table}
$${rule-prose: Elemmode_ok/passive Elemmode_ok/declare}
```

Measured: **410 distinct splice patterns** across the document, reaching
**488 of the 568 rules (85%)**. So the rule names this instrument extracts
are exactly the names the published specification cites.

**THE CORRESPONDENCE CONVENTION, stated normatively:**

> **One Lean definition per spec rule, named after that rule, cited by that
> name.** `Step_pure/br_if-true` becomes a constructor `br_if_true` of an
> inductive `Wasm.V2.Step_pure`, carrying the spec rule's name in a
> docstring. Coverage is then a SET EQUALITY between the surface's
> constructor names and the census's rule names — a `#guard`, not a
> judgement call.

That gate does not exist yet, but its **prototype has been run and lands
inside the instrument**: `splice_check` resolves every splice pattern in
`document/core` against the censused rule set and **refuses if any pattern
resolves to nothing**, because a pattern with no rule means the census
missed a rule. Measured today: **410 patterns, 0 dead.** The census's
namespace and the published spec's namespace are the same namespace, and
that is now checked rather than assumed.

Recovering the pattern grammar was itself a finding: a bare relation name
covers all its rules, `*` globs, and **a bare case name is a group
prefix** — `Step_pure/select` covers `Step_pure/select-true` and
`Step_pure/select-false`. The first version of the check reported 54 dead
patterns; all 54 were this rule, not spec defects. An instrument that had
reported them as findings would have published 54 wrong facts.

**80 rules are never spliced**, and they are not an oversight: 47
validation, 21 auxiliary, 14 reduction, concentrated in `Instr_ok2` (8),
`Instrs_ok2` (4), `ImmutReachable` (5) and `Val_ok` (3). These are the
*algorithmic* and *runtime-typing* re-statements that exist for the
soundness appendix rather than for the normative body. A surface may
legitimately not carry them at v0, and the census now says exactly which
they are.

### 1.5 SpecTec — what it is, and what it does NOT have

`spectec/` is the DSL and toolchain. Measured backends in `spectec/src/`:
`backend-latex`, `backend-prose`, `backend-splice`, `backend-interpreter`,
`backend-ast`, plus the `frontend`/`el`/`il`/`il2al`/`middlend` pipeline.

**`spectec/README.md` names "the _Coq_ and _Isabelle_ definitions for
mechanisation" as a goal — and there is no Coq, Isabelle or Lean backend
directory in the tree.** That is a measured absence and it is the single
most important fact about where a Lean surface sits: the DSL was designed
with proof-assistant backends in mind and does not yet have one.

There **is** an interpreter backend, and it runs the official suite per
version: `spectec/test-interpreter/spec-test-1` (73 `.wast` files —
matching the `wg-1.0` tag's 73 exactly), `spec-test-2` (147), and
`spec-test-3`, which is a **symlink to `../../test/core`**. So "execute the
spec's own rules against the spec's own tests" is an existing, wired loop.
A Lean surface can be scored on the same loop, against the same corpora,
and that is the cheapest possible definition of success.

*This charter did not build the SpecTec toolchain or run its test targets;
the pass rates it achieves are NOT measured here and no number for them
appears in this document.*

### 1.6 Positioning against prior mechanizations

**§8 answers this, and the answer is load-bearing enough that it belongs in
the reader's head before §2:** there are **two live Lean 4 Wasm efforts**,
both committed to within the last 72 hours — a SpecTec→Lean backend inside
the WG's own tooling, and a funded startup's 113 k-line interpreter scoring
**99.4%** on the suite of §4. **This tier is not first.** §8.4 takes the
position that follows — *complement*: build the proof layer, where the gap
is real, and mirror the generated definitions rather than compete with
them.

---

## 2 THE BEHAVIOR TAXONOMY

### 2.1 There is no undefined behavior, and the spec says so

`document/core/appendix/properties.rst:14`, in the spec's own words:

> There is no undefined behavior,

**Measured: that is the only occurrence of the phrase "undefined behav" in
the entire `document/core` tree.** The C tier arms **eleven UB classes**
whose refusals *never retire* because refusing them is the product
(`docs/c23-goal.md` §3.1 cause 2). **The Wasm tier arms zero.** The whole
of that cause disappears from the verdict system.

That is the calibration lesson's first half, and it is worth being precise
about what replaces UB: **traps**. A trap is not undefined — it is a
*specified terminal outcome* with its own reduction rules. Where C says
"anything may happen and the model must decline to invent a meaning", Wasm
says "the configuration steps to `TRAP`", and the model must **produce that
value**. Refusal and totality swap places.

### 2.2 The nondeterminism, ENUMERATED — and the spec enumerates it for us

Wasm is deterministic *modulo* a small, named set. The set is not inferred:
`appendix/profiles.rst` defines a **deterministic profile (DET)** whose
definition is a list of what it removes, and what it admits it cannot.
Measured against the prose, five sources, and they are not the same kind:

| # | source | spec site | DET collapses it? | shape |
| --- | --- | --- | --- | --- |
| 1 | **NaN sign and payload** | `exec/numerics.rst:1044-1063` | **yes** | set-valued function |
| 2 | **relaxed SIMD** | `exec/numerics.rst:2323, 2473, 2496, 2572` | **yes** | implementation choice |
| 3 | **`memory.grow` / `table.grow`** | `exec/instructions.rst:501, 622` | **NO** | resource exhaustion |
| 4 | **host functions** | `exec/runtime.rst:277`, `exec/instructions.rst:393-418` | **NO** | embedder's, not Wasm's |
| 5 | **`br_table`'s result type** | `valid/instructions.rst:204` | n/a | *validation*, not execution |

Threads and relaxed memory are **not in scope**: they are a separate
proposal, absent from the 3.0 core spec, and this charter does not price
them.

### 2.3 The J.1 exemplar: NaN payloads, and the ONE rule pair that carries everything

Thomas's J.1 ruling — *correct = correct under any resolution* — has an
exemplar here so exact that the spec writes it in the same shape. Measured
in `specification/wasm-2.0/8-reduction.spectec:183-189`:

```
rule Step_pure/binop-val:
  (CONST nt c_1) (CONST nt c_2) (BINOP nt binop)  ~>  (CONST nt c)
  -- if c <- $binop_(nt, binop, c_1, c_2)

rule Step_pure/binop-trap:
  (CONST nt c_1) (CONST nt c_2) (BINOP nt binop)  ~>  TRAP
  -- if $binop_(nt, binop, c_1, c_2) = eps
```

`$binop_` returns a **SET**. The premise `c <- $binop_(…)` is *membership*,
so the reduction relation picks an element — and `= eps`, the empty set, is
a trap. **One rule pair covers three regimes at once:**

* a singleton set — the deterministic case, the overwhelming majority;
* a multi-element set — the nondeterministic case (NaN), where **every
  element is a correct answer** and a model is correct iff it is correct
  under *any* of them;
* the empty set — the trap.

And the NaN set is defined, in `exec/numerics.rst:1056-1063`, as exactly
that: an auxiliary function *"producing a set of allowed outputs from a set
of inputs"*, with the DET profile's clause being the singleton
`{ +NAN(canon_N) }` and the other two clauses marked
`\exprofiles{\PROFDET}` — *excluded under DET*.

**So the ∀-resolution taxonomy maps onto Wasm with no adaptation:**

| family verdict | Wasm meaning |
| --- | --- |
| **MATCH** | the model's outcome is IN the spec's set of allowed outcomes |
| **DIVERGE** | the model produced an outcome OUTSIDE the set. Zero, always |
| **REFUSE** | the model declined, loudly. **One cause only** (§2.5) |
| **TIMEOUT** | fuel exhausted; never conflated with REFUSE |

`assert_return` compares against a *pattern*, not a value, precisely
because the answer is a set (§4.3). The suite was built for ∀-resolution
before this family had a name for it.

### 2.4 The versioning datum: the suite's own vocabulary for nondeterminism CHANGED

This is both a nondeterminism finding and a versioning finding, and it is
the sharpest evidence that the family's "versioned surfaces" instinct is
right. Measured across the three tags:

| | wg-1.0 | wg-2.0 | wg-3.0 |
| --- | ---: | ---: | ---: |
| `assert_return_canonical_nan` | **933** | 0 | 0 |
| `assert_return_arithmetic_nan` | **961** | 0 | 0 |
| `nan:canonical` (a result *pattern*) | 0 | **3293** | 3325 |
| `nan:arithmetic` (a result *pattern*) | 0 | **3409** | 3409 |
| `(either …)` | 0 | 0 | **32** |

**Wasm 1.0 expressed NaN nondeterminism as two dedicated ASSERTION FORMS.
Wasm 2.0 abolished both and folded them into `assert_return` as result
PATTERNS.** The obligation did not change; its *encoding* did, completely.
A Lean surface pinned to 1.0 that grew a verdict system around
`assert_return_canonical_nan` would have to throw that machinery away at
2.0 — not extend it, throw it away. Two of the family's laws are paying off
at once: pin a version, and let the version's own vocabulary drive the
verdict system rather than a vocabulary invented for it.

**`(either …)` is 3.0-only, 32 sites across 6 files, ALL of them
`relaxed-simd/`** (measured — `relaxed_min_max`, `i8x16_relaxed_swizzle`,
`relaxed_laneselect`, `i16x8_relaxed_q15mulr_s`, `relaxed_dot_product`,
`relaxed_madd_nmadd`). It is a *third* encoding of specified
nondeterminism, added when relaxed SIMD landed, and it is the only one
whose alternatives are enumerated literally rather than by a named pattern.

In the DSL the same thing is a single boolean: `def $ND : bool
hint(builtin)` (`wasm-latest/1.0-syntax.profiles.spectec:5`), used at
exactly two sites (`3.0-numerics.relaxed.spectec:11,14`) to gate
`$relaxed2` and `$relaxed4`. **Nondeterminism in Wasm 3.0 is a
one-bit parameter of the semantics**, which means a Lean surface can carry
`(nd : Bool)` and get the DET profile for free rather than as a separate
model.

### 2.5 The refusal surface collapses from three causes to one

`docs/c23-goal.md` §3.1 insists the C tier's REFUSE has three causes that
must never be pooled, because they retire on different schedules. Measured
against Wasm, only one survives:

| C tier cause | Wasm tier |
| --- | --- |
| out-of-tier construct | **survives** — retires by climbing a version/proposal rung |
| **UB, refused loudly — never retires** | **GONE.** There is no UB (§2.1) |
| unmodeled libc | **GONE.** Wasm has no standard library; imports are the *host's*, and a missing import is `assert_unlinkable`, a specified outcome |

**So the Wasm tier's REFUSE has exactly one cause, and it fully retires.**
That is a qualitatively different scoreboard from the C tier's, where the
dominant refusal class is permanent by design. A Wasm scoreboard that ever
shows a second refusal cause has found a bug in this analysis.

The Python lane's non-verdict carries over unchanged and is load-bearing
here too: **a run that executed nothing must never score as agreement.**

---

## 3 WHAT THE FAMILY GAINS — and the honest scale statement

Stated plainly because §7 asks Thomas to spend sessions on it:

* **The correspondence becomes mechanical.** §1.4's convention is a set
  equality against a census, not a reading. No other tier in the family can
  say that today.
* **The refusal surface collapses to one retiring cause** (§2.5). The
  scoreboard means something simpler than the C tier's.
* **The nondeterminism is enumerated by the spec** (§2.2) rather than
  discovered by the lane, and is a one-bit parameter in 3.0 (§2.4).
* **The suite is written by the spec's own authors, free, permissively
  licensed and self-describing** (§4) — the family's first such. It is
  **not** normative, and §4.1 states that correction rather than burying
  it.

And what it does not gain: **Wasm is not sunfish.** The Python and C tiers
model one program in two languages, which is what makes `docs/DESIGN.md`'s
square a cross-check. §5 recommends a rung 0 that keeps a thread to that
program, but the thread is thin and this charter does not pretend
otherwise.

---

## 4 THE CONFORMANCE CORPUS

### 4.1 It is the WG's own — and it is explicitly NON-NORMATIVE

`docs/c23-goal.md` opens by conceding *"There is no official ISO
conformance suite"* and then scores against five *proxies* — three compiler
projects' regression histories and one vendor's suite — with the standing
caveat that a high score means *"agrees with what these projects test"*,
not conformance.

**WebAssembly's `test/core` is the working group's own suite, shipped in
the spec repository, beside the spec it tests.** That is a real improvement
on five third-party proxies, and it is where an earlier draft of this
charter stopped. **It was an overclaim, and the correction matters enough
to state loudly:**

* The **W3C WG charter in force** (2026-08-20 → 2028-08-27) lists a *"Test
  suite and implementation report for the specification"* under **"Other
  Deliverables"**, in a section headed *"Other **non-normative** documents
  may be created such as:"*.
* Corroborating it mechanically: a case-insensitive grep of the entire
  normative spec source (`document/core/**/*.rst`) for `test suite`,
  `testsuite` or `conformance` returns **zero hits**. **The specification
  never refers to the suite at all.**
* The `.wast` *script format* is not specified in any normative document.
  `interpreter/README.md` calls it *"additional functionality purely
  intended as testing infrastructure."*

So the honest statement is narrower than "official conformance suite" and
should be used in exactly this form: **`test/core` is the de-facto suite,
maintained by the specification's own authors, and a hard gate in the
Community Group's phase process** — Phase 3 entry requires the suite to
cover a feature, Phase 4 requires two or more Web VMs to pass it — **but it
is not normative, and the specification does not cite it.** A high score
means "agrees with the tests the spec's authors wrote", which is a genuine
degree closer than any C corpus and still not conformance.

This is a *better* footing than the C tier's, not a qualitatively different
one, and §3's claim that this is "the family's first official free suite"
is corrected to: **the family's first suite written by the spec's own
authors.**

**And the correction settles a family-level question rather than merely
retracting one.** `docs/backlog.md` §L63 — the Ada tier's founding charter —
claims ACATS as *"the only OFFICIAL suite in the family"*. Had this
charter's first draft landed, the two would have collided head-on.
**§L63 is right and this lane was wrong**: ACATS keeps the title, and the
family's record is now consistent because a claim was checked rather than
asserted.

### 4.2 The corpus, measured at HEAD

| | files | lines | commands | assertions | modules | keywords |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `test/core/*.wast` (core) | **97** | 58 668 | 21 235 | **20 029** | 1 118 | 318 |
| `test/core/*/` (7 proposals) | 161 | 120 004 | 44 061 | 42 569 | 1 137 | 453 |
| **total** | **258** | **178 672** | **65 296** | **62 598** | **2 255** | **638** |

Per version, same instrument:

| tag | files | lines | commands | assertions | modules | keywords |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| wg-1.0 | 73 | 49 115 | 19 272 | 18 438 | 779 | 252 |
| **wg-2.0** | 148 | 149 385 | 54 008 | 52 230 | 1 598 | 540 |
| wg-3.0 | 258 | 178 048 | 65 201 | 62 542 | 2 228 | 638 |

The 3.0 proposal subdirectories are `bulk-memory`, `exceptions`, `gc`,
`memory64`, `multi-memory`, `relaxed-simd`, `simd`. At 2.0 there is exactly
**one** (`simd`); at 1.0, none.

**Module forms, at HEAD: 2160 text, 88 binary, 7 quoted.** The suite is
overwhelmingly a *text*-format corpus, which decides §6's frontend question
against the naive reading.

### 4.3 The oracle: the tests describe themselves

No external interpreter is needed as an oracle. Each `.wast` carries its
own expectation. Measured at HEAD:

| assertion | count | the obligation |
| --- | ---: | --- |
| `assert_return` | **52 718** | run it; the result must MATCH THE PATTERN |
| `assert_trap` (action) | 4 930 | the action must reduce to `TRAP` |
| `assert_invalid` | 2 723 | **validation must REJECT** |
| `assert_malformed` | 1 940 | **decoding must REJECT** |
| `assert_unlinkable` | 200 | instantiation must fail at link time |
| `assert_trap` (module) | **54** | *instantiation* traps — see below |
| `assert_exception` | 18 | the action throws (3.0 only) |
| `assert_exhaustion` | 15 | resource exhaustion |
| `invoke` (bare action) | 357 | must run without trapping |

**A finding that a verdict system keyed on the keyword would get wrong:
`assert_trap` is OVERLOADED.** `interpreter/text/parser.mly` has two
productions for it — with a *module* argument (line 1465) it builds
`AssertUninstantiable`; with an *action* argument (line 1470) it builds
`AssertTrap`. **There is no `assert_uninstantiable` keyword in the lexer at
all** (measured: the lexer has exactly 9 assert keywords and that is not
one of them). So one surface keyword denotes two distinct semantic
obligations — "instantiation traps", which exercises the start function and
active segment initialisation, versus "this call traps". The census splits
them by argument shape; the split is **4930 / 54** at HEAD and **458 / 2**
at 1.0.

**Three of the top four assertion classes are NEGATIVE.** `assert_invalid`
+ `assert_malformed` + `assert_unlinkable` = **4863 assertions that demand
a REJECTION**, against `assert_return`'s 52 718 that demand a value. That
maps onto the house rule that *a negative suite is as much of a battery as
a positive one* (`docs/c-tier-charter.md` §2.5) — and here the negative
battery arrives pre-built and pre-classified into the three phases that
reject: decoding, validation, and linking. A tier that builds only an
interpreter can score none of it.

Mapping onto the verdict system:

| assert form | MATCH when | DIVERGE when |
| --- | --- | --- |
| `assert_return` | the outcome is **in the pattern's set** (§2.3) | outside it |
| `assert_trap` / `assert_exhaustion` | the model reaches `TRAP` | it returns a value |
| `assert_invalid` | validation **rejects** | validation accepts |
| `assert_malformed` | decoding **rejects** | decoding accepts |
| `assert_unlinkable` | instantiation fails at link | it links |

### 4.4 The licence — CHECKED PER FILE, and the c-testsuite trap does NOT fire

`docs/c23-goal.md` §2 records a trap worth re-running rather than
inheriting: c-testsuite's top-level MIT covered *"all testing software, but
not for individual test cases"*, and reading 219 `.otag` files split the
corpus 150 ISC / 69 **LGPL-2.1**. A lane that read only the top-level
notice would have redistributed copyleft code under a wrong one.

**Re-run here. It does not fire.** `WebAssembly/spec`'s top-level `LICENSE`
is not a licence at all — it is a *map*, and it delegates per directory:

| directory | licence |
| --- | --- |
| `document/` | W3C Software and Document Notice and License |
| `spectec/`, `interpreter/`, **`test/`** | **Apache-2.0** |
| `proposals/` | CC0 |
| `papers/` | CC BY 4.0 |

`test/LICENSE` is the Apache-2.0 text in full. And the per-file check —
the instrument scans the first 40 lines of every `.wast` for a copyright,
SPDX or licence line — reports **0 of 258 files** carrying any per-file
notice. There is no `.otag`-equivalent and no third-party provenance layer.
**The suite is uniformly Apache-2.0.**

**Recommendation: FETCH, DON'T VENDOR, pinned by revision — unchanged.**
The licence would *permit* vendoring with a notice, which is a real
difference from the C tier's situation and should be recorded as such. It
is still the wrong choice: 178 672 lines is not a thing to carry, the
policy is the one the lane already follows (`Examples/c/sunfish/` holds an
envelope and no `.c`), and a uniform policy across tiers is worth more than
a local optimisation. **This is Thomas's to overrule** (§7).

---

## 5 THE DRIVER ARTIFACT — rung 0 proposed

### 5.1 What is on the box, measured

| tool | present? | note |
| --- | --- | --- |
| `wasm32-clang` / `wasm32-wasi-clang` / `wasm-ld` | **yes** | clang 23.0.0git, target `wasm32-unknown-wasi` |
| `node` | **yes** | v25.6.1 — V8's engine, `WebAssembly.validate` confirmed working |
| `ocaml` | **yes** | the spec's reference interpreter is OCaml |
| **a wasi sysroot** | **NO** | measured: no `wasi-sysroot` anywhere under `/opt/homebrew` |
| `wabt` (`wat2wasm`, `wasm-objdump`) | **NO** | — |
| `wasmtime` / `wasmer` / `wasm-tools` | **NO** | — |

### 5.2 The obvious candidate, and why it FAILED

The family's flagship program has a C twin: `tools/ctwin/sunfish.c`, on
sunfish master, sha256
`7d5e0ff8782f804844f383d6f72314dbf948f8e3a26f4033794d6357140b77d7` — **the
exact file `docs/c-tier-charter.md` §1.2 censuses**, verified today by
recomputing the hash. Compiling it to wasm would give the family a *third*
vertex on one program.

**Measured: it does not compile here.** `wasm32-wasi-clang --target=wasm32-wasip1
-std=c23 -O2` fails at `sunfish.c:29:10: fatal error: 'stdio.h' file not
found` — no wasi sysroot on this box. And a second obstacle sits behind the
first: the C census records **`setjmp` 2 / `longjmp` 2**, which on
wasm32-wasi needs explicit SjLj support and an exception-capable runtime.
Neither was reached, so **the second obstacle is stated as a risk, not as a
measurement.**

Recorded as a real option, correctly priced rather than assumed away.

### 5.3 RUNG 0, RECOMMENDED: `pyfloordiv`, compiled

Take the C tier's **own M1 round-trip function** — `pyfloordiv`,
`sunfish.c` L160-164, the function `docs/c-tier-charter.md` §4.7 chose and
`§L57` gated — and compile it to wasm.

```c
int pyfloordiv(int a, int b) {
    int q = a / b, r = a % b;
    if (r != 0 && ((r < 0) != (b < 0))) q--;
    return q;
}
```

Measured, freestanding (`--target=wasm32 -nostdlib -Wl,--no-entry
-Wl,--export=pyfloordiv -Wl,--strip-all`):

| level | module | code section |
| --- | ---: | ---: |
| `-O0` | **185 bytes** | 122 bytes |
| `-O1` / `-O2` / `-Os` / `-Oz` | **99 bytes** | 36 bytes |

The `-O2` module is 6 sections (type 7, function 2, memory 3, global 8,
export 23, code 36) and its body is **11 distinct opcodes**:

```
local.get 0 · local.get 1 · i32.div_s · local.tee 2 · local.get 0 ·
local.get 2 · local.get 1 · i32.mul · i32.sub · local.tee 0 ·
i32.const 0 · i32.ne · local.get 0 · local.get 1 · i32.xor ·
i32.const 0 · i32.lt_s · i32.and · i32.sub · end
```

**Verified under node at every optimisation level**: agrees with
`Math.floor(a/b)` on all **574** points of the grid `a ∈ [−20,20] ×
b ∈ [−7,7]\{0}`, and **both** trap classes fire (`divide by zero`,
`divide result unrepresentable`).

**Why this is the right rung 0 — and it is the calibration lesson in one
function.** `docs/c-tier-charter.md` §4.7 chose `pyfloordiv` because it
carries **two of the C tier's eleven armed UB classes in three
statements**: division at `b == 0` and at `INT_MIN / -1`. Compiled to wasm,
those same two inputs become **specified, deterministic traps** — and the
spec says so in the DSL, measured at
`specification/wasm-2.0/3-numerics.spectec:145-149`:

```
def $idiv_(N, U, i_1, 0)   = eps
def $idiv_(N, S, i_1, 0)   = eps
def $idiv_(N, S, i_1, i_2) = eps  -- if $($signed_(N,i_1) / $signed_(N,i_2)) = $rat$(2^(N-1))
```

`$idiv_` is typed `iN(N)?` — an *option* — and `$binop_` lifts it into the
set that `Step_pure/binop-val` draws from and `Step_pure/binop-trap`
observes empty. **The two `eps` clauses ARE the two C UB classes**, and
nothing else in `$idiv_` is partial.

So one function, three tiers, three treatments of the same two inputs:

| tier | `a / 0` and `INT_MIN / -1` |
| --- | --- |
| Python | raises `ZeroDivisionError`; no `INT_MIN` case at all (unbounded ints) |
| **C** | **undefined — the model must REFUSE** |
| **Wasm** | **`eps` → `TRAP` — the model must PRODUCE A VALUE** |

That is what "the surface-to-spec distance is minimal" buys, made concrete:
the C tier's hardest obligation at this function is the Wasm tier's
easiest, and both are correct.

**One honest caveat, and it is a real limit on the analogy.** At `-O1` and
above the compiler eliminated `i32.rem_s` entirely, computing `a % b` as
`a - (a/b)*b`, and made the `q--` branchless. **The wasm module is not a
transcription of the C — it is a compiled artifact**, so its relationship
to `sunfish.c` is the *compiler's* correctness, not a fidelity contract like
ctwin's. The Wasm tier's rung 0 therefore does **not** extend the square;
it is a well-understood 99-byte module that happens to have a documented
provenance. `-O0` (185 bytes, `i32.rem_s` retained) is the more faithful
shape and is the better default for a first ingestion.

### 5.4 The alternative, and why it is not the recommendation

Using spec-suite modules directly as rung 0 is viable and costs nothing to
add later — `test/core/fac.wast` and `test/core/i32.wast` are the obvious
first ones. It is not the *first* rung because a suite module arrives with
a `.wast` script wrapper around it, so it couples rung 0 to the script
frontend; §6 wants those separable. **Both should exist by M1's end**; the
compiled artifact is simply the one that isolates the binary decoder.

---

## 6 THE FIRST MILESTONE — planned

### 6.1 The version recommendation: **target Wasm 2.0 first**

| | 1.0 | **2.0** | 3.0 |
| --- | ---: | ---: | ---: |
| rules to mirror | 133 | **259** | 568 |
| reduction rules | 58 | **128** | 224 |
| suite files | 73 | **148** | 258 |
| proposal subdirs | 0 | **1** | 7 |
| NaN oracle | **two obsolete assert forms** | result patterns | result patterns |
| `(either …)` | — | — | 32 sites |
| SpecTec source | back-ported | back-ported | native |

**Recommend 2.0**, for three measured reasons and against the obvious
objection:

1. **1.0's oracle vocabulary is obsolete.** Its 1894 NaN assertions use two
   assertion forms that no longer exist (§2.4). Building a verdict system
   for them is building something 2.0 deletes.
2. **3.0 is 2.2× the rules** (568 vs 259) and 7× the proposal surface, and
   adds a third nondeterminism encoding (`either`) plus GC and exceptions —
   whole new value domains.
3. **The 1.0→2.0 upgrade is nearly free and the 2.0→3.0 one is
   enumerable** (§1.3): 131 of 133 names survive into 2.0, so targeting 2.0
   forfeits almost nothing of 1.0, while 2.0→3.0 is a known +345/−36 that
   can be priced when it is wanted rather than guessed now.

The objection — *3.0 is where the spec is native and where the DET profile
lives* — is real and is why **the surface should carry `(nd : Bool)` from
line one** (§2.4) even at 2.0, where it is always `true`. That costs one
parameter and makes the 3.0 profile a fill-in rather than a refit.

**Independently corroborated after the fact.** §8.1 finds that the one
active Lean soundness effort in the field — `zilinc/spectec`'s
`test-lean/typing_lemmas.lean` — **imports the generated `wasm2.0`
model**, not 1.0 and not 3.0. That recommendation was reached here from the
census alone and then found to match where the only other Lean proof lane
actually chose to stand. It is the strongest evidence available that 2.0 is
the right rung for *proof* work, whatever 3.0 is right for.

### 6.2 The frontend: ingest the **BINARY** format, and the census says why

The naive reading of §4.2 — 2160 text modules against 88 binary — argues
for text. **Recommend binary anyway**, and the reasons are the census's:

* **The text format is the larger specification — measured, in the DSL at
  3.0.** `6.*-text.*.spectec` carries **258 grammar productions over 1815
  lines**; `5.*-binary.*.spectec` carries **170 over 1204**. Text is 1.5×
  binary and adds folded expressions, identifiers, abbreviations,
  annotations and inline module fields. Binary is a byte grammar with no
  sugar.
* **Every text module has a binary form and the toolchain emits it.** The
  reference interpreter and the compiler both do. Text→binary is an
  *envelope-generation* step outside Lean, exactly as `docs/c-tier-architecture.md`
  §4 puts translation phases 1-6 outside Lean in clang. **A decision taken
  for another tier for other reasons pays off again here.**
* **Rung 0 is already binary** (§5.3), 99 or 185 bytes, and its section
  structure was parsed in this charter with ~30 lines of Python.
* **`assert_malformed`'s 1940 assertions are about DECODING**, and most are
  written against binary modules. A text-first frontend can score none of
  them.

Two frontend hazards the census found, both of which a text-first ingester
would have to solve and a binary one does not:

* **Inline modules.** `test/core/inline-module.wast` is, in its entirety,
  `(func) (memory 0) (func (export "f"))` — a whole file of module *fields*
  whose `(module …)` wrapper is elided. The scanner surfaced this as three
  unknown top-level commands before it was taught the abbreviation.
* **Annotations.** `(@id …)` is a **lexical** construct
  (`interpreter/text/lexer.mll:823-829`), recorded out of band and legal
  anywhere a token is — including where a command goes.
  `test/core/annotations.wast` tests exactly that, and a plain
  s-expression reader sees them as commands.

### 6.3 M1 — the inches

**M1: one module is INGESTED. `pyfloordiv.wasm` round-trips binary →
envelope → Lean AST literal → `#guard`.** No semantics, no store, no
reduction. Mirrors the C tier's M1 exactly (`§L50`), because that shape
worked.

1. **The two censuses and this charter.** LANDED with this document.
2. **The version pin + envelope schema** — `docs/wasm-envelope-schema.md`,
   schema `wasm-0.1`, mirroring `docs/c-envelope-schema.md` and
   `docs/sv-envelope-schema.md`. **Every vocabulary table DERIVED from
   `docs/wasm-spec-census.json`** rather than chosen, as the C schema was
   derived from its construct census. Carries `wasm_version` as a
   first-class field for the reason `c-0.1` carries `profile_id`: it is an
   *input* to what the bytes mean, and the ingester must refuse a mismatch
   loudly.
3. **`extractors/wasm/extract.py`** — a binary decoder under the standing
   never-fail contract: never fails on a valid module; anything outside the
   pinned vocabulary becomes an `Unsupported` leaf naming the opcode;
   double-run byte-identical; hard errors exit non-zero and say why. Cheap
   — the binary format is a byte grammar, and §5.3's section walk is
   already most of the section layer.
4. **`LeanModels/Wasm/Ast.lean` + `Json.lean`** — the deep-embedded AST and
   the elaboration-time ingester. A **sibling** of `LeanModels/Python/` and
   `LeanModels/C/`, never a client, on `docs/c-tier-charter.md` §2.1's
   ruling. Wasm's values are fixed-width like C's and unlike Python's; its
   memory is a byte array with no provenance at all, unlike *both*.
5. **`Examples/wasm/pyfloordiv/`** — the module, the envelope, and the
   `#guard`s, non-vacuity checked by flipping each.
6. **The correspondence gate, PROTOTYPED** — `docs/wasm-spec-census.json`'s
   rule-name set for `wasm-2.0`, committed, plus a check that the surface's
   declared coverage is a *subset* of it. At M1 the subset is empty and the
   gate is trivially true; it exists so that M2's first constructor is
   checked against the spec on the day it lands, not retrofitted.

**What M1 deliberately does not decide:** whether `Run` moves to
`LeanModels/Core/` (`§L35` priced it at 149 lines / 24 files / 1251 sites
and it stays deferred until a second consumer exists — the ingester tier
does not mention `Run` in any lane); the value model; the memory model; and
the endgame.

### 6.4 THE CALIBRATION QUESTION: can M2 state a SOUNDNESS theorem early?

The dispatch asks the tier to price this, because it is the lesson that
transfers. **Answer: yes, earlier than any other tier in the family — and
for a reason that is structural, not lucky.**

Three things are true here that are true nowhere else:

1. **The theorem is already stated, in the spec.**
   `document/core/appendix/properties.rst` carries the soundness statement,
   and `specification/wasm-latest/` carries `7.0-soundness.contexts.spectec`
   and `7.1-soundness.configurations.spectec` — **the soundness section is
   in the DSL too.** The tier does not have to invent a target. Contrast
   `docs/c-tier-charter.md` §3.2, where the twin-bridge theorem's whole
   difficulty is that the observable has to be *strengthened on both sides*
   before it means anything.
2. **The statement is small and standard.** Progress and preservation over
   a typing judgment and a reduction relation — the shape every semantics
   course states. The C tier's endgame (b) is a bespoke cross-language node
   identity that no textbook has a template for.
3. **44% of the reduction rules need no state** (§1.2). `Step_pure`'s 56
   rules can carry a preservation argument with no store, no frame and no
   world.

**But the price is honest and it is not small.** Progress and preservation
are theorems about the *whole* relation, so they need all 259 rules of 2.0
present, not a fragment — the census's own numbers are the estimate here.
The realistic shape:

* **M2 states the theorem and proves it for a FRAGMENT** — `Step_pure` over
  the numeric instructions, against `Instr_ok`. That is reachable, it is a
  real theorem rather than a battery, and it is the first thing in this
  family's history where **the theorem statement can be transcribed from
  the spec rather than designed.**
* **A full 2.0 soundness proof is a program, not a milestone.** Two
  mechanisations already exist in other assistants and the effort they
  represent is the honest anchor — which §8 supplies. This charter does not
  price it and explicitly declines to.

**THE CALIBRATION LESSON, for the family:** when the spec is formal, the
gain is *not* mainly that the semantics is easier to write — it is that
**the target stops being a design decision.** The C tier spent §3.2 of its
charter arguing about what its endgame theorem should even say, and
concluded the Python arc's frozen statement would have to change before the
theorem meant anything. The Wasm tier's endgame statement is transcribed
in an afternoon. **The cost moves from specifying to proving**, and only
the second half is irreducible. Every other tier in the family should
budget for the first half; this one should not.

---

## 7 STILL OWED BY THOMAS

1. **The target version.** §6.1 recommends **2.0**, measured. The
   alternatives are 1.0 (smaller — 133 rules — but an obsolete oracle
   vocabulary) and 3.0 (native SpecTec and the DET profile, at 2.2× the
   rules).
2. **The frontend format.** §6.2 recommends **binary**, against the naive
   reading of the corpus. Text-first is defensible if scoring the 2160 text
   modules early matters more than the 1940 `assert_malformed` ones.
3. **Vendored versus fetched suite.** §4.4 recommends **fetch, pinned by
   revision**, uniformly with the other tiers. Unlike the C tier's corpora
   this one is **uniformly Apache-2.0 and could legally be vendored with a
   notice** — so this is a genuine choice here where it was not there.
4. **The endgame — and §8 re-frames it sharply.** A **conformance** endgame
   (score `test/core`, zero DIVERGE, the `docs/c23-goal.md` pattern) now
   means **competing with a 99.4% incumbent** (§8.1b). A **soundness**
   endgame (§6.4) targets ground **no one in Lean has taken, on a version
   no assistant has a citable proof for** (§8.2). Those are no longer
   symmetric options, and the charter says so rather than leaving the
   symmetry implied. §6.3's M1 remains neutral between them by
   construction.
   **A standing check follows from §8.4's risk (i):** before M2 starts,
   re-check whether `zilinc/spectec`'s Lean lane has closed its 13
   `sorry`s. If it has, the soundness contribution is redundant and this
   tier should re-choose rather than proceed on a stale plan — the same
   cross-repo staleness law that `--compare` exists for (§L35), applied to
   a competitor instead of a corpus.
5. **Whether `LeanModels/Wasm/` gets a directory and an exe target** — the
   same fenced-file question the C tier asked at `§L35` and which turned
   out **half unnecessary** (`§L50`: `Examples.+`'s glob pulled the lane
   into CI with no edit to either fenced file). Sequenced past M1 so it can
   be answered concretely rather than speculatively.

---

## 8 PRIOR MECHANIZATIONS, AND THIS TIER'S POSITION

**The headline, and it is the charter's most consequential finding: this
tier would NOT be founding the first Lean 4 mechanization of WebAssembly.
There are two live efforts, both with commits inside the last 72 hours, and
one of them scores 99.4% on the suite §4 recommends scoring against.**

A charter that had planned M1 without knowing this would have been planning
against a field that already exists. §8.4 states the position that follows.

### 8.1 The two live Lean 4 efforts

**(a) `zilinc/spectec` branch `lean-backend` — a SpecTec→Lean backend,
inside the WG's own tooling.** A fork of `Wasm-DSL/spectec` carrying
`spectec/src/backend-lean/` (~227 KB of OCaml) behind a real CLI flag
`--lean`. Author Yong Zheng Yew, hosted on the fork of Zilin Chen (NTU),
who also owns SpecTec's Isabelle backend. **Last commit 2026-08-20, ≥100
commits since June, near-daily.** Its generated output, counted: `wasm1.0.lean`
3051 lines, `wasm2.0.lean` 7179, **`wasm3.0.lean` 11 289 lines / 544
`inductive`s** — all with **0 `sorry`, 0 `axiom`**. Its proof lane,
`test-lean/typing_lemmas.lean`, is **1865 lines, 26 theorems, 13 `sorry`**,
and its contents are unmistakably type-soundness scaffolding
(`instr_typing_inversion`, `valtype_sub_refl/trans`,
`ainstrs_ok_context_store_wf`). It imports the **2.0** model — which is
independent corroboration of §6.1's version recommendation.

**(b) Talos (`cajal-technologies/talos`) — a funded startup's Lean 4 Wasm
interpreter.** Cajal (YC W26). **113 263 lines of Lean, ~2270 theorem/lemma
declarations, zero `sorry`**, targeting Wasm **3.0**. AGPL-3.0. Last commit
2026-08-21. **It scores 64 751 / 65 142 assertions = 99.40% on the official
suite, across 257 `.wast` files** — computed from its own committed
`testsuite_report.txt`. It proves per-program correctness via a
weakest-precondition calculus (migrating to iris-lean), plus
`step_deterministic` and soundness/completeness of a checked step function
against the relational `Step`. **It does NOT prove type soundness**; no
progress or preservation theorem exists in it.

**The two are complementary and say so publicly.** Talos's top committer,
on Hacker News: *"There is an ongoing effort (not by us) about creating a
formal WASM spec in lean, generated from SpecTec, when that lands our plan
is to prove that our interpreter follow the specification."* A co-founder:
*"…later full verification against the SpecTec-generated Lean semantics so
that we can drop our interpreter from the trusted base."*

**(c) The stalled predecessor, and its blockers are Lean's.**
`Wasm-DSL/spectec` PR #192 (`lean4-wip`, Joachim Breitner) is an open draft
whose body says *"not meant for merging"*; last commit 2026-02-19. It
generated a 10 790-line Wasm 3.0 model with CI that literally runs `lean
Wasm.lean`. **The two blockers it documented are Lean issues, not Wasm
ones**: `lean4#2329` (`deriving DecidableEq` for nested inductives) and
`lean4#1964` (nested inductive predicates with indices in parameters —
Breitner: *"this is a kernel issue"*). A partial workaround exists
(Xiaojia Rao's `Extended-derive-deceq`) and is vendored into the live
`lean-backend` branch. **A lane that deep-embeds Wasm's mutually recursive
types in Lean will meet both**, and that is a design input for M1's AST,
not a footnote.

Eight further Lean repos were surveyed and none is a live effort: the most
substantial, `linobit-corp/wasm-lean` (a WasmCert-Coq port claiming
14 342/14 342 on Wasm 1.0), stopped in April 2026.

### 8.2 The established mechanizations, and the gap they leave

| | assistant | version | proves | suite | status |
| --- | --- | --- | --- | --- | --- |
| WasmCert-Isabelle | Isabelle/HOL | 2.0 | **progress + preservation** | not published (no CI) | dormant (0 commits/6mo) |
| WasmCert-Coq | Rocq | 2.0 + subtyping | type safety, checker soundness **and completeness**, instantiation | **54 004/54 004 = 100%** (on a submodule ~15 months stale) | maintenance (4 commits/6mo) |
| Iris-Wasm | Rocq + Iris | **1.0** | WP + adequacy, logical relation, **robust safety** | — | dormant since 2025-01 |
| Iris-WasmFX | Rocq + Iris | stack switching | type safety | — | live (PLDI 2026) |

Papers, verified: Watt, CPP 2018; Watt/Rao/Pichon-Pharabod/Bodin/Gardner,
**FM 2021** (not ITP); Rao et al., PLDI 2023; Rao et al., POPL 2025;
SpecTec itself, Youn et al., **PLDI 2024**.

**The gap, stated precisely and it is the important paragraph:**

> **No mechanized soundness proof of Wasm 2.0 or 3.0 exists that the
> specification is willing to cite** — the appendix's footnotes scope its
> proofs to **1.0**. In Lean specifically, **no proof of type soundness
> exists at all**: the generated definitions are there (11 289 lines for
> 3.0), and the proof is 26 theorems and 13 `sorry`s deep.

And the spec's soundness appendix is **theorem statements without proofs**:
11 named results with full formal statements (Preservation, Progress,
Soundness, Principal Types, Type Lattice, …) and the entire justification
is one sentence — *"Given the definition of valid configurations, the
standard soundness theorems hold."* Measured in its 1578-line source:
`Theorem` ×10, `Corollary` ×2, **`Lemma` ×0, `sketch` ×0**, and the sole
occurrence of "Proof" is inside the string *"Certified Programs and Proofs
(CPP 2018)"*.

**This sharpens §6.4's calibration lesson rather than softening it.** The
target is transcribable *because someone already wrote the statement down*.
That the proof is unwritten in every assistant for 2.0 and 3.0 is the
measure of how much the second half costs — and it is the honest anchor
§6.4 said it would need.

### 8.3 W3C process — the facts, and one trap worth naming

* **Wasm 1.0 — W3C Recommendation, 5 December 2019.**
* **Wasm 2.0 — never a Recommendation.** Candidate Recommendation Snapshot,
  2024-12-17.
* **Wasm 3.0 — there is no `wasm-core-3` shortname.** 3.0 ships **under
  `wasm-core-2`**; the current document is a **Candidate Recommendation
  Draft dated 12 August 2026** whose abstract reads *"This document
  describes release 3.0 of the core WebAssembly standard."*
* **The current W3C Recommendation, as of today, is Wasm 1.0 (2019).**

**The trap: "current Recommendation" ≠ "current standard".** The WG has
moved to an *evergreen* model and states its intent to keep the document in
Candidate Recommendation *"without ever technically moving it to the final
Recommendation state."* So anyone citing "the W3C Recommendation" in 2026
is citing a 2019 document predating SIMD, GC, tail calls, exceptions and
memory64. **This charter therefore never says "the Recommendation"; it says
a version number**, and §6.1's recommendation of 2.0 is a recommendation
about a *rule set*, not about a W3C maturity level.

### 8.4 THE POSITION: complement — build the PROOF layer, consume the definitions

Three options, and the charter takes one.

**COMPETE — rejected.** Re-deriving Wasm definitions in Lean by hand would
reproduce, worse, 11 289 lines that a maintained generator already emits
with 0 `sorry`, and would re-fight two known Lean kernel-adjacent blockers
for nothing. Talos's 113 k lines and 99.4% suite score are not a target
this lane could approach, and would not be worth approaching if it could.

**CONSUME WHOLESALE — rejected as a plan, kept as a dependency.** Taking
the generated `wasm2.0.lean` as the surface is attractive and is the right
*source* of definitions. It cannot be the whole plan: it is on a personal
fork's branch, is not on `main`, has no release, and this repository's
standing rule is that a lane *"depends on no package"* — the same rule that
made `docs/c-tier-charter.md` §3.2 restate `Report` rather than import it.

**COMPLEMENT — TAKEN.** The seam is where §8.2's gap is:

> **Definitions are generated and abundant; the PROOF is absent in Lean.
> This tier's contribution is the proof layer and the verdict system around
> it — mirroring the generated definitions rather than competing with them,
> and vendoring a pinned SNAPSHOT rather than depending on a branch.**

Concretely, and it changes three things in the plan above:

1. **§6.3's M1 is unchanged and is now also a hedge.** Ingesting a *binary
   module* into a Lean AST is orthogonal to the generated semantics — the
   generator emits the spec's rules, not a decoder — so M1 competes with
   nothing and is needed under every option.
2. **§1.4's correspondence gate becomes more valuable, not less.** With a
   generator in the field, "does this Lean surface cover the spec's rules"
   is a question about *two* artifacts, and a census-backed set equality
   answers it for both. This lane's instrument can check the generated
   model too — it is the same rule-name namespace.
3. **§6.4's fragment soundness proof is the actual contribution**, and it
   should aim at the *same* statement the `lean-backend` lane is 13
   `sorry`s from, on the *same* version (2.0). That is either a useful
   second opinion or a direct contribution upstream, and both are better
   outcomes than a private re-derivation.

**Two honest risks, recorded.** (i) The `lean-backend` lane could close its
13 `sorry`s and land upstream, at which point this tier's proof
contribution is redundant — that is a *good* outcome for the world and
should be checked for before M2 starts, not after. (ii) AGPL-3.0 on Talos
means its code cannot be borrowed into this repository at all; it is
useful as a *comparison oracle* and nothing else.

**§7's endgame question is re-framed by this section**, and Thomas should
read §7.4 with it: a *conformance* endgame now means competing with a 99.4%
incumbent, while a *soundness* endgame targets ground no one in Lean has
taken.

### 8.5 What this section did NOT verify

Stated because the rest of the charter is measured and this section is
surveyed. Not verified: that the `lean-backend` branch's generated Lean
**compiles today** (the `sorry`/`axiom` counts are textual, from downloaded
files, not from a build); whether that lane is funded or a side effort;
`linobit-corp/wasm-lean`'s 14 342/14 342 claim (read from its README, not
reproduced); WasmCert-Isabelle's suite pass rate (no CI, no harness, no
number published anywhere); and whether SpecTec's Rocq soundness proof has
advanced past Wasm 1.0 since March 2025. **No pass-rate number in this
charter was produced by this lane**, and each is attributed to the artifact
it was read from.

---

## 9 WHAT LANDED WITH THIS CHARTER

* `harness/wasm_spec_census.py` — the spec-rule instrument, with
  `--compare`, `--rules`, and the `splice_check` correspondence prototype.
  **No sibling in any other tier**, which is the calibration lesson.
* `harness/wasm_suite_census.py` — the suite instrument, with `--compare`.
* `docs/wasm-spec-census.json` — 4 versions, 125 relations, 568 rules,
  enumerated by name.
* `docs/wasm-suite-census.json` — 258 files, 62 598 assertions, per-file
  rows and per-file licence evidence.
* `docs/wasm-charter.md` — this document.
* `docs/backlog.md` §L59 — the record.

**No Lean, and no change to any existing file.** "It cannot break anything"
is an argument rather than a measurement, so the triad was run anyway; the
numbers are in §L59.
