# The ECMAScript tier: FOUNDING CHARTER

**Status: the workstream's founding document.** Chartered under Thomas's
family directive — versioned, spec-mirrored surfaces, one lane per
language. ECMAScript is the family's largest spec-having member and it is
Python's scientific twin: the same dynamic-language shape, and the
opposite authority. Python's authority is a reference INTERPRETER you can
ask; ECMAScript's is a DOCUMENT you must read. Everything interesting
about this lane follows from that one difference, and §4 is where it is
paid.

This charter does five things and no more: it CENSUSES the spec and the
suite with an instrument that lands beside it, it fixes the
correspondence convention between a spec clause and a Lean definition, it
recommends a pinned edition, it defines a core slice by measurement
rather than by hope, and it plans the first milestone. **No semantics are
built. No Lean is written.**

Every COUNT below is a RUN of `harness/es_census.py`, with
machine-readable rows in `docs/es262-census.json`; the licenses, the
corpus sizes and the paraphrased normative text were read from the
pinned artifacts themselves and are attributed where used. Nothing is
quoted from memory, and the one place a first version of the instrument
reported a plausible zero is recorded in §1.1 as the defect it was.

**Pinned sources**, fetched and not vendored (§3.4):

| artifact | revision | date |
| --- | --- | --- |
| `tc39/ecma262` `spec.html` | `ed463bc10dbeaad0410ce67e541a77ea8e9900a5` | 2026-08-20 |
| `tc39/test262` | `3655e7464de3d52643ecddd4b5f9f4f3e7f62398` | 2026-08-10 |
| `engine262/engine262` | `c7939eaf0bcfa292b4a8872e78f4c221bc2477a2` | 2026-08-09 |

---

## 0 THE FAMILY ROW, RATIFIED

`docs/family-architecture.md` landed while this census ran (its
`docs/backlog.md` §L59 to this charter's §L66), and it already carries an
ECMAScript row with its
edition tokens marked **PROPOSED** — the founding lane's to measure and
ratify. This section ratifies it, and answers the two rulings that name
this tier.

| registry field | value |
| --- | --- |
| `<Lang>` | **`Es`** — as proposed |
| authority | **SPEC-MIRROR (ECMA-262) + OFFICIAL-SUITE (test262)** — as proposed, and §3.2 measures why the second half is earned |
| **edition token** | **`ES2026`** — ratified here, and **PINNED** (§0.2) |
| pinned artifact | the **`es2026-errata`** git tag (§1.4.1), sha256 `032ecc74…` |
| oracle | an engine for behaviour; **test262's expectation for the verdict** (§4.3) |
| corpus | test262, fetched not vendored (§3.4) |
| state | founding — **SoftFloat block DOWNGRADED (§0.3); edition PINNED, M1 inch 2 landed (§0.2)** |

### 0.1 The edition token, against the four laws

`ES2026` is a valid Lean identifier beginning with a letter (law 1, which
`es2026-errata` is not); it is self-identifying out of context — a reader
seeing `LeanModels/Es/ES2026/Value.lean` in a stack trace knows the
edition (law 2); it names a published document a reader can hold, the
17th edition, rather than a point release or a build (law 3); and it will
not rename, because the edition it names is ratified and frozen (law 4).

**The token and the pinned artifact are deliberately different strings,
and the distinction is load-bearing.** `ES2026` is the EDITION; the
`es2026-errata` tag is the REVISION of that edition's text this tier
extracts from. §1.4.1 measures the errata to be structurally identical to
`es2026` — 764 bytes, zero structural deltas — so pinning the errata
costs nothing and gains the corrections. Layout follows §1.1:
`LeanModels/Es/` for what every claimed edition shares,
`LeanModels/Es/ES2026/` for what this one decides.

Per §1.5 the envelope carries `"language_version": "ES2026"` as a
first-class top-level field beside `language`, the ingester REFUSES a
mismatch, and `frontend.version` keeps its separate job as the FRONTEND's
family (`acorn-8`, not a point release). This charter's earlier drafts
called that field `edition_id` by analogy with `c-0.1`'s `profile_id`;
the family's name wins, and the schema version (`es-0.2`) stays
orthogonal.

### 0.2 The pin is LANDED, and it refuses

Thomas's standing latest-spec-priority ruling and this charter's priced
recommendation agree, so the edition is pinned rather than proposed:
**`ES2026`, at the `es2026-errata` revision.**

`docs/es-edition.json` is the artifact — written by the census
(`--write-edition`), read by it (`--edition`), and the single place the
extractor and the envelope will read the token from, so path, envelope
and citation cannot drift. It mirrors `docs/c-profile.json`'s role
exactly: an identity a downstream tool verifies rather than assumes.

**It refuses, and all four paths were RUN rather than designed:**

* the pinned spec against the pin — **passes**, and stamps
  `language_version: ES2026`;
* the **draft** against the pin — REFUSES, naming both sha256s;
* **`es2026` (non-errata)** against the errata pin — REFUSES. The two
  editions differ by 764 bytes and zero structural counts (§1.4.1), and
  the pin still separates them. An identity check that tolerated a
  764-byte difference would not be one;
* the token `es2026-errata` as an EDITION TOKEN — REFUSES, because it is
  not a valid Lean identifier (`family-architecture.md` §1.1 law 1). This
  is the mechanical reason the token and the revision are two strings.

**And pinning has a second measured cost, beyond §1.4.1's 249 steps.**
Re-running the whole census against `ES2026` instead of the draft moves
exactly two joins, and both moves are the suite and the engine being
ahead of the edition rather than anything being wrong:

| | draft | **ES2026** | delta |
| --- | ---: | ---: | ---: |
| test262 `esid` rows resolving to the pinned spec | 21,874 | **21,572** | **−302** |
| …correspondingly, `clause-id-absent` | 6,776 | **7,078** | +302 |
| engine262 `#sec-` anchors resolving | 1,152 | **1,141** | −11 |
| everything measured on the SUITE and the FRONTEND | — | — | **0** |

**302 suite citations and 11 engine anchors name clauses that exist only
in the draft** — the §3.3 Stage-4 mechanism, now quantified against the
pinned edition instead of asserted. The frontend's 97.8% and the 66-type
vocabulary do not move at all, because they are edition-independent, and
that they did not move is the check that the re-pin changed what it
should and nothing else.

### 0.3 The SoftFloat row — the block is a DEPENDENCY, and Layer 1 is satisfied

`docs/family-architecture.md` §3.5.3 lists this tier as **BLOCKING** on
SoftFloat, on the correct grounds that *"a float-free JS core slice is
very nearly empty"* and that this lane *"must state SoftFloat as a
DEPENDENCY, not defer floats the way the Python lane could."*

**Stated, and answered in the same document's terms.** §3.5.1 splits the
component into Layer 1 (executable bit-level operations) and Layer 2 (the
spec algebra), and finds Layer 1 **already supplied by core Lean on the
pinned toolchain**. This lane measured the same thing independently
before reading it — `harness/es/float_probe.lean`, §4.2(a) — which is
worth keeping precisely because it is an independent replication of a
premise three tier documents had recorded the other way.

So the row resolves in three parts:

1. **Layer 1 is a DEPENDENCY and it is SATISFIED.** The ES tier depends
   on core `Float`'s binary64 model deliberately: pinned interface,
   `#guard`s on the reduction behaviour, no `native_decide`. Not deferred,
   not re-implemented.
2. **Layer 2 is a DEPENDENCY of this tier's PROOF layer**, which M1 does
   not reach and this charter does not price. It is the commissioned
   build lane's step 1 (§3.5.5), and this tier is a consumer, not a
   builder, of it.
3. **M1 is not blocked at all.** Its rung 0 is the PARSE verdict (§5.2) —
   18,114 tests scored on accept/reject, evaluating nothing. That is not
   a dodge of the number question; it is the ingestion tier every lane in
   the family builds first.

One mapping adopted wholesale from §3.5.4: ECMAScript's
**implementation-approximated** surface — 47 mentions, 35 of them `Math`
precision (§2.2) — routes to **REFUSE(`environment`)**, never to an
invented answer. That is the family's ruling and this tier does not need
its own.

---

## 1 THE SPEC MAP

### 1.1 The instrument, and why it lands

`harness/es_census.py`, landed with this charter, run as

```
python3 harness/es_census.py --spec <ecma262>/spec.html \
                             --tests <test262> \
                             --engine <engine262> \
                             --acorn <dir>/node_modules/acorn/dist/acorn.mjs \
                             -o docs/es262-census.json
python3 harness/es_census.py --spec … --tests … --compare docs/es262-census.json
```

ECMA-262's source is **ecmarkup**, an HTML dialect in which the normative
content is machine-tagged: `<emu-clause type="abstract operation">` marks
an abstract operation, `<emu-alg>` marks a numbered-step algorithm,
`<emu-grammar>` marks a grammar production. So *"how many definitions
would a one-Lean-definition-per-abstract-operation tier owe?"* is a
COUNT, not an estimate. The instrument takes it, and takes it again for
test262's YAML frontmatter and for engine262's spec back-references.

Output is sorted; a double run is byte-identical (verified). It carries a
`--compare` mode for the same reason the C lane's does: **all three
corpora live in other repositories and move on their own schedules**, so
staleness has to be mechanically detectable rather than merely possible.
Here that is not a hypothetical — the spec's `main` branch is a LIVING
document (§1.4) and moved twice in the fortnight around this census.

**All three refusal paths were RUN, not admired** (`--self-test`), and
the third caught a real defect. A missing file refuses; a source that
attributes ZERO clauses or ZERO tests refuses (an empty census is an
instrument fault, never a finding); and frontmatter the restricted YAML
reader cannot parse refuses BY FILE NAME rather than being skipped.

Two things the instrument found about itself, both recorded because both
were silent-wrong-answer shaped:

1. **The first step counter reported 0 steps in 2,301 algorithms.** It
   counted `<li>` elements; `<emu-alg>` bodies are markdown ordered lists
   (`1. Let _x_ be …`), so every algorithm looked empty and the headline
   "the spec is a definitional interpreter" had no number under it. A
   zero where a count belongs is now a REFUSAL, not a row.
2. **The restricted frontmatter reader refused one real file** —
   `language/statements/function/13.2-30-s.js`, whose whole frontmatter
   mapping is indented by one space. That is legal YAML (block-mapping
   indentation is relative), so the reader de-indents by the common
   prefix and COUNTS the normalization: exactly 1 of 53,578 tests. The
   alternative — widening the parser until nothing refuses — is how a
   census silently mis-buckets a corpus.

It is deliberately **NOT wired into `tools/ci.sh`**, for the reason that
keeps `harness/c_construct_census.py` un-wired: the corpora are not in
this repository and not on a stock runner, so a gate would be a permanent
SKIP pretending to be a check. `--compare` is the re-run, and it is a
deliberate act.

**One half of it COULD be gated, and is noted rather than taken:**
`--self-test` needs no corpus at all — it builds its own fixtures in a
temp directory and asserts the three refusals plus the corpus's real
frontmatter shapes. It is a candidate `step` for `tools/ci.sh` the day
this lane touches that file, which this charter does not.

**Reproducing the corpora**, since nothing is vendored (§3.4) — shallow
clones of `tc39/ecma262`, `tc39/test262` and `engine262/engine262`, plus
`npm install acorn` in a scratch directory for the frontend probe. The
three clones and the census together take a few minutes; the `test/` tree
alone is 226 MB, which is the concrete reason it stays out of the
repository.

### 1.2 What is there — measured

`tc39/ecma262` at the pinned revision. Titled *ECMAScript® 2027 Language
Specification*, `status: draft` — which is itself the finding of §1.4.

| dimension | measured |
| --- | ---: |
| source | **3,082,799 bytes**, 55,131 lines of ecmarkup |
| clauses / annexes / intro, all id-bearing | 2,266 + 73 + 1 = **2,340 ids** |
| **numbered-step algorithms** (`emu-alg`) | **2,301** |
| **numbered steps inside them** | **14,470** |
| grammar blocks (`emu-grammar`) | 1,545 |
| tables / notes | 100 / 710 |
| `Assert:` steps | 621 |

The 1,417 clauses the spec TYPES, which is the vocabulary a
one-definition-per-operation tier is counting:

| clause type | count |
| --- | ---: |
| built-in function | 548 |
| **abstract operation** | **500** |
| syntax-directed operation (`sdo`) | 206 |
| internal method | 59 |
| concrete method | 48 |
| numeric method | 36 |
| **host-defined abstract operation** | **16** |
| **implementation-defined abstract operation** | **4** |

Per top-level clause, the shape is uneven in a way that decides the slice
(full table in the JSON; the language's thirteen clauses):

| clause | clauses | algorithms | steps | grammar |
| --- | ---: | ---: | ---: | ---: |
| 5 Notational Conventions | 30 | 23 | 50 | 34 |
| 6 Data Types and Values | 95 | 67 | 417 | 0 |
| 7 Abstract Operations | 114 | 113 | 725 | 12 |
| 8 Syntax-Directed Operations | 37 | 406 | 727 | 413 |
| 9 Executable Code and Execution Contexts | 104 | 75 | 332 | 0 |
| 10 Ordinary and Exotic Objects Behaviours | 131 | 124 | 1,150 | 8 |
| 11 Source Text | 13 | 7 | 39 | 1 |
| 12 Lexical Grammar | 38 | 15 | 20 | 193 |
| 13 Expressions | 135 | 177 | 914 | 231 |
| 14 Statements and Declarations | 84 | 95 | 531 | 133 |
| 15 Functions and Classes | 71 | 184 | 707 | 226 |
| 16 Scripts and Modules | 70 | 120 | 763 | 97 |
| 17 Error Handling | 2 | 0 | 0 | 0 |
| **the language, total** | **924** | **1,406** | **6,375** | **1,348** |

Annex B — the web-legacy annex — is **52 clauses, 39 algorithms, 171
steps**, which is small enough to be worth naming as excluded rather than
worth fighting.

### 1.3 The style, and THE CORRESPONDENCE CONVENTION

ECMA-262 is not a prose specification with algorithms in it. It is a
definitional interpreter with prose around it, and the measurement says
so three ways: 2,301 algorithms over 14,470 numbered steps; 621 of those
steps are `Assert:`; and the abrupt-completion plumbing is written as an
operator, not as prose — **`? Foo(x)` appears at 2,405 sites and
`! Foo(x)` at 567**, while `ReturnIfAbrupt`, the ES5-era spelling those
two abbreviate, appears **0 times**.

**And this is not our reading of the document — TC39 mechanizes it in its
own CI, and the mechanism was read rather than recalled.** The
`tc39/ecma262` repository runs ESMeta — a toolchain that mechanically
EXTRACTS an executable interpreter from `spec.html` — in **two workflows,
both on every pull request**:

* `esmeta-typecheck.yml` runs `esmeta tycheck` over the extracted
  definitions, with an explicit ignore list,
  `-tycheck:ignore=esmeta-ignore.json`. That file has **twelve entries**,
  by name, out of 2,301 algorithms.
* `esmeta-yetcheck.yml` runs `esmeta yet-check` between the PR's base and
  head, flagging **newly-introduced "yet" phrases** — ESMeta's term for
  specification prose its extractor cannot yet interpret.

**A specification whose CI reviews every change for whether its automatic
interpreter-extractor can still read it is, in substance, code.** That is
a far stronger claim than "the spec is algorithmic", and it is the single
best argument for this lane: the extraction target already exists and is
maintained; what does not exist is an extraction into a language where the
result can be a THEOREM rather than a test pass.

That is the whole reason this lane is worth founding, and it fixes the
convention without further argument:

> **ONE Lean definition per typed clause, named after the operation, cited
> by `(edition, clause-id, step)`.** An abstract operation becomes a
> `def`; a syntax-directed operation becomes a `def` matching on the
> production; an internal method becomes a field of the object record; a
> `Assert:` step becomes a hypothesis or a `#guard`, never a silent
> assumption. The citation is a TRIPLE and not a clause id alone, because
> clause ids are not stable — §1.4 measures how unstable.

The convention has a mechanical check available on day one, and it is the
reason `--engine` is a mode of the census rather than a curiosity.
**engine262 — a JavaScript implementation of ECMA-262 written to mirror
the spec's structure — writes 1,782 distinct `#sec-…` anchors in JSDoc
comments over 1,868 sites, across 68,429 lines and 364 files** whose very
directory names are the spec's own (`abstract-ops` 54 files,
`runtime-semantics` 109, `static-semantics` 48, `intrinsics` 102,
`execution-context` 8, `host-defined` 12). **1,152 of those anchors
resolve to a clause the pinned spec still defines.** So the convention
this charter adopts is not invented here: it is the convention a working
implementation of this spec independently arrived at, and its coverage is
measurable.

### 1.4 Versioning — and the recommendation

ECMA-262 is published as **annual editions**, and it is simultaneously
maintained as a **living document**. Both facts are measured, not
recalled:

* The pinned `main` calls itself *ECMAScript® 2027 Language
  Specification* with `status: draft`. **The tip of the repository is
  never a published edition.** It is the next one, plus every Stage-4
  proposal that has landed since the last snapshot.
* Editions are git TAGS, and they exist: `es2024`, `es2025`, `es2026`,
  plus candidate tags and **`es2026-errata`**. ES2026 is the 17th
  edition, and the pinned draft's own introduction describes it in the
  past tense.

**THE MEASUREMENT THAT SETTLES IT.** Clause ids are not stable across
editorial restructuring, and the suite proves it against the tip:
**6,776 test262 rows, over 239 distinct ids, carry an `esid` naming a
`sec-…` clause the pinned spec does not define.** The largest single one
is `sec-for-in-and-for-of-statements-runtime-semantics-labelledevaluation`
at 1,819 rows — a clause consolidated into
`sec-runtime-semantics-labelledevaluation` when the syntax-directed
operations were gathered into clause 8. The SEMANTICS did not move; the
CITATION rotted. A tier whose Lean definitions cite clause ids against a
moving `main` would rot the same way, continuously, and would discover it
only when a proof stopped matching a section that no longer exists.

> **RECOMMENDATION: pin `es2026-errata` — the 17th edition plus its
> errata, measured in §1.4.1 to be structurally identical to `es2026`.**
> Pin test262 separately by revision and filter it by `features:` (§3.5).
> Track the draft as a DIFF, never as the source.

Four reasons, in order of weight. (i) A ratified edition makes
"conformance" mean something that is not a moving target — the same
reason the C lane pinned `-std=c23` rather than "clang's current C". (ii)
A tag is a `--compare`-checkable pin, exactly like the C lane's corpus
sha256. (iii) Pinning `main` makes every re-clone a different
specification: the C lane's staleness lesson, but continuous instead of
occasional. (iv) Against pinning an OLDER edition: test262's tree is
ahead of `es2024`/`es2025` by more, so the feature filter must work
harder for no gain, and engine262 — the only cross-check with per-clause
structure — tracks the tip.

**The honest cost of the recommendation, stated:** test262 has no
per-edition branch. It tracks the living spec. So a pinned edition and a
pinned suite will always disagree about the newest material, and §5.2
measures that disagreement exactly — **106 of 18,114 core-slice tests**,
every one of them feature-tagged, every one filterable. That is the price
and it is small.

#### 1.4.1 The recommendation is PRICED, not merely made

The `es2026` and `es2026-errata` tags were fetched and censused with the
same instrument, so the delta is measured rather than assumed. It is
re-derivable in three commands and needs no second artifact — the
instrument takes any `spec.html`:

```
git -C <ecma262> fetch --depth 1 origin tag es2026 tag es2026-errata
git -C <ecma262> show es2026:spec.html > /tmp/es2026-spec.html
python3 harness/es_census.py --spec /tmp/es2026-spec.html
```

| | draft (tip) | **es2026** | delta |
| --- | ---: | ---: | ---: |
| bytes | 3,082,799 | 2,978,793 | −3.4% |
| clauses + annexes | 2,266 + 73 | 2,189 + 73 | −77 |
| algorithms | 2,301 | 2,239 | −62 |
| **numbered steps** | 14,470 | 14,221 | −249 (−1.7%) |
| grammar blocks | 1,545 | 1,507 | −38 |
| abstract operations | 500 | 489 | −11 |
| built-in functions | 548 | 527 | −21 |
| syntax-directed operations | 206 | 202 | −4 |
| **internal methods** | 59 | **59** | **0** |
| **concrete methods** | 48 | **48** | **0** |
| **numeric methods** | 36 | **36** | **0** |
| **host-defined AOs** | 16 | **16** | **0** |
| **implementation-defined AOs** | 4 | **4** | **0** |
| implementation-approximated mentions | 47 | **47** | **0** |
| "undefined behaviour" occurrences | 1 | **1** | **0** |
| core slice: clauses / algs / steps | 924 / 1,406 / 6,375 | 907 / 1,365 / 6,216 | −17 / −41 / −159 |

**THE HEADLINE, and it is the C lane's §1.4 result arriving
independently: between a ratified edition and the tip, the spec GREW and
the TAXONOMY did not move at all.** Not one internal method, not one
concrete or numeric method, not one host hook, not one
implementation-defined operation, and not one word of the
implementation-approximated surface. Every delta is a COUNT of new
material. **So the entirety of §2 — the taxonomy this charter builds a
refusal system around — is edition-invariant across the one boundary that
was available to test it.** Pinning `es2026` costs the tier 249 steps of
newer built-in material and nothing structural.

**And `es2026-errata` is free.** Censused: it differs from `es2026` by
**764 bytes** and by **zero** in every structural count — clauses,
annexes, algorithms, steps, grammar blocks, and all eight clause types.
The caveat this charter raised ("re-check the errata before adopting")
is discharged by measurement rather than left as diligence: **adopt
`es2026-errata`.**

**One trap found while doing it, worth a sentence because it would have
been silent.** The `es2026` tag's own ecmarkup metadata still reads
`status: draft` — the field is not flipped at tag time. A lane that
identified an edition by reading `status:` out of the document would
conclude no edition exists. **The tag is the edition marker; the metadata
block is not.**

### 1.5 SCALE, stated honestly — and THE CORE SLICE

The spec is 3.08 MB, 2,340 clauses and 14,470 steps. A tier that
proposed to model all of it would be proposing something nobody has done
in any language, for any specification, and this charter does not propose
it. It proposes a slice, and the slice is measured rather than hoped:

> **ES-core-v0 = ECMA-262 clauses 5-17, minus four things, each excluded
> with its number.**

| removed | what it is | spec cost | suite cost |
| --- | --- | ---: | ---: |
| **Annex B** | web-legacy, explicitly conditional in the spec | 52 clauses / 39 algs / 171 steps | 1,086 tests |
| **ECMA-402 (Intl)** | **not in ECMA-262 at all** — a different standard | 0 (measured) | 3,357 tests |
| **the module system** | clause 16's linking half; `HostLoadImportedModule` is a host hook | — | 731 tests + 843 `module`-flagged |
| **jobs / the event loop** | `HostEnqueuePromiseJob` and friends; clause 27 | — | 5,624 `async`-flagged |

The second row is worth its own sentence, because "without the full Intl"
was the dispatch's phrasing and the measurement is stronger than that:
**Intl is not a part of ECMA-262 that this charter declines to model. It
is a separate standard (ECMA-402) that is not in the document at all.**
The suite keeps its tests in a separate `intl402/` tree, and 7,760 of the
unresolved `esid` rows point outside ECMA-262 entirely (Intl and Temporal
together). Excluding it costs the tier nothing it had.

**What REMAINS, measured on both sides:**

* **924 spec clauses, 1,406 algorithms, 6,375 numbered steps, 1,348
  grammar blocks** — 50% of the document's bytes and 44% of its steps.
* **18,114 test262 tests**, of which **16,702 need no harness file at
  all** beyond the two every test gets.

That is a real slice, and it is still large. §5 is about not trying to
eat it in one bite.

---

## 2 TAXONOMY MAPPING

The family's taxonomy — undefined / unspecified / implementation-defined
/ locale-specific — was built for C, and mapping it onto ECMAScript
produces a result so lopsided that the lopsidedness is the finding.

### 2.1 There is no undefined behavior, and the spec says so in as many words

**The phrase "undefined behaviour" occurs exactly ONCE in all 3.08 MB of
ECMA-262, and the sentence containing it asserts that there is none.** It
is in clause 29, the Memory Model, and it reads — paraphrasing its own
words — that the memory model defines both the conditions under which a
program is sequentially consistent and the possible values readable from
data races, *to wit, there is no undefined behaviour*.

The word "unspecified" occurs once, about the means by which agents in a
cluster share memory. None of `in either order`, `order is not
specified`, `unspecified order`, `any order`, or `evaluated in an
implementation-defined order` occurs anywhere in the document. Zero
occurrences, all five, measured.

This is a structural consequence of the completion record, not editorial
tidiness. Every evaluation in ECMAScript produces a Completion Record:
normal, or `throw`, or a `break`/`continue`/`return` carrying a target.
The instrument counts **422 mentions of "normal completion", 318 of
"throw completion", 122 of "abrupt completion"** and the 2,405 `?` /
567 `!` shorthand sites that propagate them. There is no third outcome to
leave undefined. A C program that indexes out of bounds has no meaning; a
JS program that does gets `undefined`, and the step that produces it is
numbered.

**The escape hatches are constrained too, which is the part that
surprised this census.** The spec's Annex D lists host hooks, and it
imposes a requirement ON the hook: a host hook **must return either a
normal completion or a throw completion**. Even the place where the
specification hands definition to somebody else, it does not hand over
the OUTCOME TYPE. There is no ECMAScript analogue of "and then anything
may happen."

### 2.2 What latitude does exist, enumerated

The spec has its own four-way taxonomy of deferrals, and it is more
precise than ours, so the tier should adopt it verbatim rather than
translate it:

| the spec's term | what it means, paraphrased | mentions | where they are |
| --- | --- | ---: | --- |
| **implementation-defined** | deferred to an external source with no further qualification, and no recommendation | 57 | 13 in Numbers and Dates; **16 in the whole language core** |
| **implementation-approximated** | deferred, but with an IDEAL behaviour recommended; implementations are encouraged to approximate it | 47 | **35 in Numbers and Dates** — this is `Math` precision |
| **host-defined** | deferred to a host, and listed in the Host Layering Points annex | 52 | 15 in Executable Code and Execution Contexts |
| **host hook** | an abstract operation defined in whole or part externally; must return a normal or throw completion | 16 clauses | enumerated below |

Both enumerable sets fit in a paragraph, which is the point:

* **The four implementation-defined abstract operations are all time
  zones**: `GetNamedTimeZoneEpochNanoseconds`,
  `GetNamedTimeZoneOffsetNanoseconds`, `AvailableNamedTimeZoneIdentifiers`,
  `SystemTimeZoneIdentifier`.
* **The sixteen host hooks**: `HostEnsureCanAddPrivateElement`,
  `HostMakeJobCallback`, `HostCallJobCallback`, `HostEnqueueGenericJob`,
  `HostEnqueuePromiseJob`, `HostEnqueueTimeoutJob`,
  `HostEnqueueFinalizationRegistryCleanupJob`,
  `HostGetImportMetaProperties`, `HostFinalizeImportMeta`,
  `HostLoadImportedModule`, `HostGetSupportedImportAttributes`,
  `HostEnsureCanCompileStrings`, `HostHasSourceTextAvailable`,
  `HostResizeArrayBuffer`, `HostGrowSharedArrayBuffer`,
  `HostPromiseRejectionTracker`.

**The core slice barely touches any of it.** Of 57
implementation-defined mentions, 16 fall in clauses 5-17; of 47
implementation-approximated mentions, 2 do. `Math` precision and `Date`
are clause 21, which the slice does not contain. Where the C lane needed
a `docs/c-profile.md` and a 13-fact `_Static_assert` battery before its
extractor could be written, the ES core slice's implementation-defined
budget is small enough to enumerate in the envelope schema and refuse on.

### 2.3 THE HORIZONTAL DATUM: ∀-order has nothing to range over

Thomas's ∀-order ruling — that a claim about a program whose evaluation
order the standard leaves open must quantify over the orders — is the C
lane's load-bearing design constraint. The C charter's M2 design honours
it at **C's 181 short-circuit sites** and leaves **20 full expressions
for a may-alias check**.

**In ECMAScript it has nothing to range over, and the census is what says
so.** Evaluation order is not a property the standard declines to fix; it
IS the numbered steps. `EvaluateStringOrNumericBinaryExpression` — the
operation every `a + b` goes through — is five steps, quoted verbatim
from the pinned source:

```
1. Let _leftRef_ be ? Evaluation of _leftOperand_.
1. Let _leftValue_ be ? GetValue(_leftRef_).
1. Let _rightRef_ be ? Evaluation of _rightOperand_.
1. Let _rightValue_ be ? GetValue(_rightRef_).
1. Return ? ApplyStringOrNumericBinaryOperator(_leftValue_, _opText_, _rightValue_).
```

That is C's whole sequencing problem, answered by ordinal position. There
is no license to reorder, because there is no prose granting one —
measured at zero occurrences of all five phrasings. (Every line begins
`1.` because ecmarkup auto-numbers markdown ordered lists — the rendered
spec shows 1 through 5. That is why the instrument counts leading
`<digits>.` per line rather than looking for a running count.)

The exception is exactly one clause, and it is the same one the C charter
fenced off. **Clause 29, the Memory Model — 28 clauses, 10 algorithms, 69
steps — replaces the state function with a relational constraint system
over memory events**, which is precisely what the C charter said of its
rung R6: *"the one rung that is not a widening — it replaces a state
function with a memory-ORDER relation, which would change the
interpreter's TYPE."* Two languages, two censuses, independently, and the
concurrency clause is the same shape of obstacle in both.

### 2.4 The row `docs/family-architecture.md` §4.3 leaves for this lane

That table asks every spec-mirror tier to map its spec's behaviour
classes onto the refusal taxonomy before it writes semantics. C's row is
filled; this is ECMAScript's, and it is short because §2.1 is true.

| the spec's classes | mapping |
| --- | --- |
| **undefined behaviour** | **THE ROW IS EMPTY.** One occurrence in 3.08 MB, in a sentence asserting there is none. No UB class is armed and none will be — the whole difference from C's row, which arms eleven that never retire. |
| **unspecified** | one occurrence, about how agents in a cluster share memory. Reaches the core slice nowhere. |
| **unspecified evaluation ORDER** | **also empty**, at zero occurrences of all five phrasings (§2.3). C's canonical-left-to-right-plus-census treatment has nothing to apply to: the numbered steps ARE the order. |
| **implementation-defined** | 57 mentions, 16 in the language core, only 4 TYPED operations — all time zones. Pinned by the envelope; refused where a program's observable depends on one. |
| **implementation-approximated** | 47 mentions, 35 of them `Math` precision. → **REFUSE(`environment`)** per §3.5.4's family ruling; never an invented answer. |
| **host-defined / host hooks** | 16 named hooks (§2.2). → **REFUSE(`environment`)**; the module and job-queue hooks are what put the module system and the event loop outside the core slice. |
| **early errors** | not a latitude class but a static-semantics OBLIGATION, and the one the frontend census sizes at **285 tests** (§5.2). REFUSE until built, then a rung. |
| **the memory model** | clause 29 — the one relational rather than algorithmic clause, out of slice, and the same obstacle C's R6 names. |

So the datum, stated for the family:

> **Whether ∀-order quantification is needed is a property of the
> SPECIFICATION'S STYLE, not of the language's dynamism.** A prose
> standard that grants latitude needs it everywhere latitude is granted.
> An algorithmic standard that fixes every step needs it in exactly the
> clause where it stops being algorithmic. C and ECMAScript are both
> imperative, both mutable, both real; the difference in how much order
> quantification they cost is entirely a difference in how the two
> documents are written.

That is a finding about how to read a spec, and it is the reason this
lane's charter is worth writing before its semantics.

---

## 3 THE CONFORMANCE CORPUS: test262

### 3.1 What it is, measured

The official ECMAScript conformance suite, maintained by TC39 alongside the
spec. Its README is worth paraphrasing on three points, because each one
binds this lane. It is the **implementation conformance** suite for *the
latest drafts or the most recent published edition* — so it tracks the living
document by design (§1.4). It covers **three** Ecma standards, ECMA-262,
ECMA-402 and ECMA-404, not one — which is the same fact §1.5 uses to exclude
Intl. And TC39 states plainly that coverage is **not** complete and that
omissions and errors are possible: **the arbiter is fallible and says so**,
which is why §4.3's doctrine makes a disagreement a question rather than a
verdict. At the pinned revision:

| dimension | measured |
| --- | ---: |
| `.js` files under `test/` | **53,872** |
| `_FIXTURE` files (never standalone tests) | 294 |
| **tests** | **53,578** |
| tests with no YAML frontmatter | **0** |

By area — and this is the language-versus-built-ins split the charter
must price:

| area | tests | what it is |
| --- | ---: | --- |
| `language/` | 24,007 | the language core |
| `built-ins/` | 23,815 | the standard library |
| `intl402/` | 3,357 | ECMA-402, a different standard |
| `staging/` | 1,491 | not yet promoted into the structured tree |
| `annexB/` | 1,086 | web legacy |
| `harness/` | 116 | tests OF the harness |

**The split is 24,007 language to 23,815 built-ins — almost exactly
even.** So "the built-ins are half the suite" is literally true, and it
is the same relationship the C lane found between the language and libc:
`docs/c23-goal.md` measured that the libc obligation was not "libc" but
`printf`, and that 149 of 220 c-testsuite tests called no libc at all.
The ES analogue is measured in §3.3 and it is just as favourable.

### 3.2 The harness protocol, and why it is cheap

test262's `INTERPRETING.md` is normative. Paraphrasing the parts that
bind a model:

* Each test runs in a fresh realm. `harness/assert.js` and
  `harness/sta.js` are evaluated first unless the test carries the `raw`
  flag — 32 tests do.
* **A test PASSES by not throwing.** Failure is signalled by an uncaught
  exception; `assert.js` throws a `Test262Error`. There is no expected
  output file anywhere in the suite.
* `includes: [...]` names further files from `harness/` to evaluate
  first, in order.
* Unless flagged `onlyStrict`, `noStrict`, `module` or `raw`, each test
  runs TWICE — once as written, once with `"use strict";\n` prepended.
* The host must supply `print` and a `$262` object (`createRealm`,
  `detachArrayBuffer`, `evalScript`, `gc`, `global`, `agent`, …).

**The pass criterion is the finding.** The C lane's best result in
`docs/c23-goal.md` was that its largest reachable corpus — GCC's torture
tests — is scoreable on EXIT STATUS with **zero output modeling**,
because the idiom is `abort()` on failure. **test262 is that shape
everywhere.** MATCH is "the model ran the program and nothing was
thrown", or, for a negative test, "the model threw the named error at the
named phase". The Python lane compares stdout because CPython programs
print; the ES core slice never has to.

**The one qualification, and it is precise rather than a hedge:** the
`async` flag makes `print` the completion SIGNAL — the runner waits for
`Test262:AsyncTestComplete` or a `Test262:AsyncTestFailure:` prefix. That
is still not formatted output (two fixed strings, one prefix match), and
it is 5,624 tests all of which the core slice excludes with the event
loop. No test anywhere in the suite compares byte-exact program output.

The harness itself is small and is ordinary JS the model must run: **38
distinct include files, 8,826 lines total**, and the distribution is
lopsided —

| include | tests using it |
| --- | ---: |
| `propertyHelper.js` | 5,241 |
| `temporalHelpers.js` | 2,809 |
| `testTypedArray.js` | 2,084 |
| `compareArray.js` | 1,715 |
| `isConstructor.js` | 644 |
| `regExpUtils.js` | 586 |

`temporalHelpers.js` and `testTypedArray.js` are outside the core slice
by construction. `propertyHelper.js` is the one that matters, and it is
the property-attribute checker — which is to say the core slice's harness
obligation is `assert.js` + `sta.js` + `propertyHelper.js` and very
little else.

### 3.3 The metadata format, and the verdict mapping

Frontmatter is YAML between `/*---` and `---*/`. Measured key frequencies
over 53,578 tests: `description` 53,577, `esid` 42,599, `info` 36,674,
`features` 34,929, `flags` 20,606, `includes` 13,621, `es5id` 8,260,
`negative` 4,732, `es6id` 3,031, `author` 1,645, `locale` 340.

`flags`, in full: `generated` 17,003, `async` 5,624, `noStrict` 2,687,
`module` 843, `onlyStrict` 678, `raw` 32, `CanBlockIsTrue` 7,
`CanBlockIsFalse` 2.

`negative` — **4,732 tests, and they are overwhelmingly one thing**:

| phase | tests | | type | tests |
| --- | ---: | --- | --- | ---: |
| `parse` | **4,658** | | `SyntaxError` | 4,696 |
| `runtime` | 40 | | `ReferenceError` | 14 |
| `resolution` | 34 | | `Test262Error` | 14 |
| | | | `TypeError` | 4 |
| | | | `EvalError` / `RangeError` | 3 / 1 |

`features` names 198 distinct feature tags, which is how the suite gates
material newer than a given implementation — the mechanism §1.4's
recommendation depends on.

**The verdict mapping**, the Python lane's shape with one adaptation and
the invariant unchanged:

| verdict | meaning against test262 |
| --- | --- |
| **MATCH** | a positive test ran to completion with nothing thrown; or a negative test threw the named error class at the named phase |
| **REFUSE** | the model declined, loudly and fuel-independently. Three disjoint causes, never pooled (§3.6) |
| **DIVERGE** | the model produced an observable and it disagrees with the suite's expectation. **The invariant violation. Zero, always** |
| **TIMEOUT** | fuel exhausted. Never conflated with REFUSE |

Two adaptations forced by the corpus, both stated rather than assumed:

* **The strict/non-strict double run is part of the verdict, not a
  detail.** A test without `onlyStrict`/`noStrict`/`module`/`raw` is TWO
  runs, and MATCH means both. Counting it once would silently halve a
  denominator; the scoreboard reports runs and tests separately.
* **A run that executed nothing must never score as agreement.** The
  Python harness carries `"live"`; the C scoreboard carries a statement
  count. Here the hazard is sharper, because *a test passes by NOT
  throwing* — so a model that ran zero statements and threw nothing would
  score MATCH on 13,842 positive tests. **The ES scoreboard's liveness
  field is load-bearing in a way neither sibling's is**, and it is
  recorded here so it is designed in rather than discovered.

### 3.4 Licenses — and the recommendation is FETCH, DON'T VENDOR

| artifact | license | vendorable? |
| --- | --- | --- |
| **test262** | **BSD 3-clause**, Copyright (C) 2012 Ecma International | yes, with notice |
| `tc39/ecma262` (spec source) | TC39 IP policy: prose under Ecma's alternative copyright notice; **source code** under Ecma's MIT-style software policy | prose: **NO** |
| **engine262** | **MIT** | yes, with notice |
| acorn (the frontend probe's parser) | MIT | fetched, never vendored |

**The test262 license is genuinely BSD, and this was verified rather than
assumed** — the C lane's c-testsuite trap (a top-level MIT that covers
"all testing software, but not for individual test cases", over 69
LGPL-2.1 cases) is exactly the failure this check exists to avoid.
test262's `LICENSE` is a single BSD 3-clause grant from Ecma
International covering the Software, with a patent-rights disclaimer
pointing at Ecma's IPR policy. There is no per-case `.otag` layer and no
third-party copyleft island. **So test262 COULD be vendored.**

**It should not be.** The recommendation is unchanged from
`docs/c23-goal.md` §2 and for the same reasons plus one new one: it keeps
a 53,872-file, **226 MB** `test/` tree out of the repository; the lane's flagship
corpora are already cross-repo (`Examples/c/sunfish/` holds an envelope
and no `.c`); and — the new reason — **the spec's PROSE is not
MIT-licensed.** Ecma's alternative copyright notice governs the normative
text, so this lane will be quoting and paraphrasing a document it may not
redistribute wholesale. A charter that vendored the suite while
paraphrasing the spec would be applying two different standards to two
artifacts from the same committee. Fetch both, pin both by revision,
cite-and-paraphrase both.

### 3.5 The core slice, on the suite side — measured

Applying §1.5's slice to the suite: exclude `annexB/`, `intl402/`,
`staging/` and `harness/`; exclude `language/{module-code,import,export}`;
exclude tests flagged `module`, `async`, `CanBlockIsTrue` or
`CanBlockIsFalse`; and count `built-ins/` SEPARATELY rather than folding
it in, because it is the libc-analogue and pooling would hide the split
the charter has to price.

| slice | tests | needing no `includes` |
| --- | ---: | ---: |
| **language core** | **18,114** | **16,702** |
| built-ins | 23,109 | 14,511 |
| module system | 731 | — |

Inside the language core:

| | tests |
| --- | ---: |
| positive | 13,842 |
| **negative, `phase: parse`** | **4,248** |
| negative, `phase: runtime` | 24 |
| distinct `features` tags | 82 |

The core slice's largest subtrees are `language/expressions` (8,857) and
`language/statements` (6,827); the rest is `language/literals` 534,
`language/eval-code` 295, `language/identifiers` 268,
`language/arguments-object` 203, and twenty smaller ones.

**The built-ins are a libc-analogue and a refusal cause, not a debt.**
23,109 tests is a lot of tests and none of them is the language. The C
lane settled the equivalent question by measuring that its libc
obligation was one function; here the same reasoning applies with a
different shape — a built-in the model has not modeled is an
**unmodeled-intrinsic REFUSE**, which retires by widening the intrinsic
slice and never by weakening a claim. The one thing the charter must not
do is let 23,109 unbuilt built-ins read as a language-tier gap.

### 3.6 REFUSE has three causes and they must not be pooled

They retire on completely different schedules, so pooling them makes the
scoreboard unreadable — the Python lane's `docs/completeness.md` §3
lesson, and the C lane's §3.1:

1. **Out-of-tier construct** — the program uses syntax the vocabulary
   does not cover. Retires by climbing a rung. The Python lane's
   `.unsupported`, exactly.
2. **Unmodeled intrinsic** — the program touches a built-in outside the
   modeled slice. Retires by widening the slice; §3.5 says how large it
   is.
3. **Host-defined or implementation-defined behaviour** — the program's
   observable depends on one of the 4 implementation-defined operations,
   the 16 host hooks, or a `Math` precision the spec only approximates.
   **This one never retires**, and it is the ES analogue of the C lane's
   "UB-refused is the product" — except that here it is a far smaller
   set, and §2.2 enumerates all of it.

**There is no fourth cause, and its absence is the taxonomy result.** The
C lane arms eleven UB classes that never retire. This lane arms none,
because the spec defines every outcome. What the C lane spends on
detecting meaninglessness, this lane spends on volume.

---

## 4 THE PYTHON COMPARISON, EXPLICIT

The dispatch's framing is right and worth stating as the lane's thesis:
**ECMAScript is Python's scientific twin.** Both are dynamically typed,
mutably objected, closure-carrying, exception-throwing, garbage-collected
languages of the same era and the same shape. The single controlled
variable between them is where the authority lives. That is what makes
the comparison a horizontal experiment rather than a second project.

### 4.1 What transfers, and it is most of the machine

Everything in `docs/c-tier-charter.md` §2.5 transfers unchanged — the
`#guard`/non-vacuity gate, zero `sorry`, zero `native_decide`, the
gate-per-rule composition discipline, envelope discipline (schema
version, `source_sha256`, frontend FAMILY in the cache key, `Unsupported`
leaves, deterministic double-run), the batch protocol (one runner process,
one row per job in job order, a `runner-error` row rather than a missing
row), the exit-code convention with **3 and 4 never counting as
agreement**, the prohibition on whitelist rows that silence a mismatch,
and effects-as-world-data with inputs-as-traces.

The Python lane's specific engineering transfers too, and more of it than
transferred to C:

* **The extractor → envelope → `load_program` → AST-literal → `#guard`
  pipeline**, verbatim in shape. §5 is that pipeline.
* **The free-scrutinee dispatch discipline.** The Python tier's H3
  finding — that referent dispatch must fork on a PURE plan
  (`attrReadPlan`/`attrCallPlan`), because a match nested under the
  receiver's binder is invisible to `cases`/`rw` — is going to be
  load-bearing here immediately, because property access in ECMAScript is
  a prototype WALK and not a lookup.
* **The frozen-recursion-point technique** (`callIn`/`execWhile`/
  `execFor`, unfolded one step by `.eq_n`) and `termination_by structural
  fuel` on every mutual member — the mergeSort trap. The spec's
  algorithms are mutually recursive on a scale that makes this
  non-optional.
* **`Run σ α` verbatim.** And here ECMAScript does something C did not:
  it makes the spec's own vocabulary and the tier's coincide. **The
  Completion Record IS `Run`.** `normal` is `.ok`, `throw` is `.exn`,
  `.timeout` is fuel exhaustion, `.unsupported` is the tier gap. The
  covenant the C charter described as "the four constructors are the
  COVENANT, not Python" turns out to be, in ECMAScript, *the
  specification's own type*.

```lean
-- LeanModels/Python/Runtime.lean (excerpt)
inductive Run (σ : Type) (α : Type) where
  | ok          (state : σ) (value : α)
  | exn         (state : σ) (error : PyErr)
  | timeout
  | unsupported (message : String)
```

**And this lane is the second consumer that forces the deferred
decision.** The C charter named `Run.exn`'s `PyErr` payload as "the one
wart", priced the move of `Run` into `LeanModels/Core/` at 149 lines
across 24 files and 1,251 `Run.` sites, and deferred both because no
second consumer existed. ECMAScript is a sharper forcing function than C
was: **a thrown JS value is an arbitrary ECMAScript language value**, not
a closed enum and not even necessarily an Error object — throwing a
primitive is legal, and `language/statements/throw/S12.13_A2_T2.js` is
one of the tests that says so. So `Run σ ε α` — or an ES-side payload
carried in `α` — is a decision this lane meets on its first evaluation
rule, not at inch 4. **Recorded as owed, and recorded as this lane's
contribution to a question the C lane opened.**

### 4.2 What cannot transfer — four, each measured or named

**(a) The value model, because Number is a float and Python's `RVal.int`
is unbounded.** `1 + 1` in ECMAScript is IEEE-754 double arithmetic.
There is no integer type in the language core besides BigInt, which is a
different type with its own operators and its own `TypeError` on mixing.
So where the Python lane could defer floats — and did, for nine rungs —
this lane meets them on line one of any evaluation semantics.

**The Python lane's recorded reason for deferring does not hold on the
pinned toolchain, and this was MEASURED rather than inherited — and then,
on rebase, found to have been measured independently by the family
architecture the same day (`docs/family-architecture.md` §3.5, which
lands first and is the citable ruling).** Two lanes reaching the same
refutation of a three-times-recorded premise, from different directions
and without coordination, is the strongest form this project's evidence
takes, so the probe stays as an independent replication rather than being
deleted in favour of the citation:
`docs/completeness.md` §6 names `float` as that lane's largest gap by
value AND price simultaneously and calls it a DECISION rather than a work
item, on the grounds that *"Lean's `Float` is not kernel-reducible, so
`#py_check` and every captured `rfl` run would break — the mergeSort
trap's family."* Run against `leanprover/lean4:v4.33.0-rc1` with no
imports at all — `harness/es/float_probe.lean`, which lands with this
charter so the claim is re-derivable rather than reported, needs no build,
and is non-vacuous (flipping one expected string fails with the
expression printed):

* `(1.5 : Float) + 2.5 = 4.0` closes **by `rfl`**;
* so does `(0.1 : Float) + 0.2 = 0.30000000000000004` — genuine binary64
  rounding, decided in the KERNEL;
* `#guard` fires on Float `==`, on `1.0 / 0.0`, on `NaN != NaN`, on
  `1.0 + 1e16 == 1e16`, and on `Float.toString`.

**`Float` is kernel-reducible on the pin.** Structurally: `Float` is a
structure over `Float.Model`, which is a `UInt64` of bits plus a proof of
`Float.Model.Format.binary64.Valid` — a bit-level IEEE-754 model, with
`DecidableEq`, shipped in core as a **27-file, 2,918-line** tree under
`Init/Data/Float`, carrying `round`, `roundToNearestEven`,
`roundedMantissa`, `roundToInt` and `roundWithAccuracy`.

**So the blocker is not where the record says, and it is much smaller.
It splits in two, and only the second half is missing:**

* **Layer 1, EVALUATION — already provided by core.** Number arithmetic
  runs in the kernel, so captured `rfl` runs and `#py_check`-style gates
  survive contact with floats. **The tier can RUN and SCORE Number
  semantics against test262 with no number decision taken at all.**
* **Layer 2, REASONING — the real gap, and it is scoped.** Those 2,918
  lines carry **3 theorems**. The definitions of the round-of-exact
  algebra exist and reduce; the algebra ABOUT them does not. Anything the
  tier wants to PROVE about float arithmetic — rather than run — starts
  near zero.

**This is the §L39 pattern again and it is worth naming as such**: a
deferral that outlived its cause, recorded in one place, never re-checked,
and found by running the thing rather than by re-reading the record.
`docs/completeness.md` is stale on this point. It is **recorded here and
not edited**, because the Python campaign owns that file — the same
courtesy §L39 extended to `AGENTS.md`.

**What this changes for the plan.** The Number question drops out of
M1 entirely and stops being a blocking owner-gated decision:

1. **§5's rung 0, the PARSE verdict, needs no arithmetic at all** —
   18,114 tests, unaffected either way.
2. **The first evaluation rungs need Layer 1 only, which exists.** Use
   core `Float`; the spec's Number operations are defined on binary64 and
   so is core's model.
3. **Layer 2 binds only at the first THEOREM about float arithmetic**,
   which is a proof-layer milestone this charter does not reach and does
   not need to price.

A bit-level model with three theorems is still a real cost, and calling
it small would be the overclaim this document exists to avoid — but it is
a cost at a milestone the lane has not planned yet, not a gate on its
first one.

**(b) Prototype chains, because Python's object model is a flattened
table and ECMAScript's is a walk.** The Python tier flattens methods into
`Module.functions` under `"<class>.<method>"` qualified names — methods
ARE functions, dispatched by name. ECMAScript has no such table:
`o.foo` walks `[[Prototype]]` links, and every step of the walk is a
`[[Get]]` internal method that an exotic object may override.
The spec's clause 10 is **131 clauses / 124 algorithms / 1,150 steps** of
exactly this — the largest step count in the language core — and it types
**59 internal methods** and **48 concrete methods**. The Python lane's
`attrReadPlan` TECHNIQUE transfers; its flattening does not, and neither
does the dunder guard that makes it sound.

**(c) Completion records as VALUES, because Python models flow with
statement arms.** The Python interpreter has a `Run` outcome and
dedicated arms for `break`/`continue`/`return`. ECMAScript's
`break`/`continue`/`return` are Completion Records with a `[[Target]]`
label, threaded through every evaluation step and combined by
`UpdateEmpty`. The shapes look similar and are not: in Python the flow is
in the interpreter, in ECMAScript it is in the value the semantics
computes. Transplanting the Python arms would be the kind of near-miss
that produces a model that is right on 90% of a corpus and silently wrong
on labelled `continue`.

**(d) The event loop, deferred and named.** `docs/completeness.md` puts
`async` last with "four productions, near-zero verification value" — true
of Python. Here **5,624 tests are `async`-flagged**, Promises are clause
27 (213 clauses / 107 algorithms / 1,316 steps), and the job queue is
reached through four of the sixteen host hooks. It is out of the core
slice, it is not near-zero value, and it must not be described as if the
Python lane's ruling covered it.

### 4.3 THE ORACLE INVERSION — the horizontality lesson

This is the comparison's whole point, and it changes a doctrine rather
than a number.

The Python lane's oracle is CPython, pinned at 3.9, and the pinning is
load-bearing enough that `docs/backlog.md` records both ends being pinned
separately — the frontend that parses and the interpreter that answers.
Under that arrangement **DIVERGE means the model is wrong**, definitionally,
because CPython IS the specification of Python. The zero-DIVERGE invariant
is a statement about the model.

**ECMAScript has no reference implementation.** The authority is the
document. So any engine the tier compares against — V8 through node,
JavaScriptCore, SpiderMonkey, or engine262 — is itself only a claimant,
and a disagreement between the model and an engine has THREE possible
causes, not one:

1. the model is wrong;
2. **the engine is wrong** — which is not hypothetical; test262 describes
   itself as the *implementation conformance* suite, which is a role that
   exists only because independent implementations disagree;
3. the spec under-determines the observable — the 57 + 47 + 52 sites of
   §2.2, plus anything the memory model leaves to a race.

**Consequence, and it is a doctrine change this lane must adopt from the
start: the scoreboard is scored against TEST262'S EXPECTATION, never
against an engine's behaviour.** An engine may be run as a cross-check —
and engine262 is the right one, because it is structured per clause and
MIT-licensed — but a model-versus-engine disagreement is a QUESTION,
resolved by reading the cited clause, and it is never automatically a
model bug. The Python lane never has to do this: it can always just ask.

**This is `docs/family-architecture.md` §4.2's precedence rule, and this
tier adopts it verbatim rather than restating it**: the SPEC is the
target, the IMPLEMENTATION is the oracle for behaviour, the SUITE OWNER
is the authority for the expected VERDICT, and a divergence between any
two is a FINDING recorded with both citations. That three-way split is
sharper than the two-way one this section reached on its own, and it is
exactly what an authority-less language needs.

**One refinement this lane owes back.** §4.2 writes that *"Wasm,
ECMAScript and Ada all have reference implementations."* For ECMAScript
that is true only in the loose sense: engine262 self-describes as *"an
implementation of ECMA-262 in JavaScript"* with 100% spec compliance as a
GOAL, and it is neither normative nor privileged by TC39. **There is no
reference implementation of ECMAScript in the sense CPython is one for
Python** — which is the whole content of this section, and the reason the
suite rather than any engine holds the verdict.

That is the horizontality lesson the family directive is for. **The same
census method, the same refusal classes, the same ladder, applied to two
languages of nearly identical shape, produce different DOCTRINES because
the authority is differently located.** A lane that copied the Python
lane's DIVERGE rule wholesale would have quietly promoted V8 to the
status of a standard.

### 4.4 The driver artifact — there is no ctwin-analogue, and it is a decision

The C lane had extraordinary luck: `tools/ctwin/sunfish.c` already
existed, node-identical to `sunfish.py`, with its own differential
fidelity gate. That is what made "the square" — A ≡ C ≡ B ≡ D — a real
target rather than a slogan.

**No such artifact exists here, and this was checked rather than assumed:
the sunfish repository contains zero `.js`, `.mjs` or `.ts` files.**
Three candidates, priced, with a recommendation:

**(1) A test262 slice as rung 0 — RECOMMENDED.** 18,114 core-slice tests,
already pinned, no new artifact to write or maintain, and the parse-verdict
rung (§5) is scoreable immediately. This is precisely the C lane's own
resolution: `docs/c23-goal.md` made the GCC torture corpus rung 1 because
it was "the cheapest first scoreboard in the whole program and it needs no
output modeling." The ES equivalent is cheaper still, because the *whole
suite* has that shape.

**(2) `sunfish.js`, a hand-written JS twin — the endgame candidate, NOT
proposed.** It would recreate the square with a THIRD vertex and make the
family's central claim — that one program, modelled in three languages
against three different authorities, must agree — into something
testable. The cost is honest: writing a node-identical twin, and then
maintaining it against an engine that moves, plus a JS arm on the ctwin
fidelity gate. The C charter priced the twin-bridge theorem at 150+
sessions and called it "a program, not a milestone"; a third vertex is
not cheaper. **Recorded as available, recommended against for now, and
Thomas's to overrule.**

**(3) A real JS program Thomas names.** The census cannot propose one
because none is in reach. If there is a JS artifact Thomas cares about,
naming it changes the slice — the way ctwin's accidental 45-kind
vocabulary turned out to clear 83% of the C suites.

---

## 5 THE FIRST MILESTONE — planned, and partly measured already

**M1: the frontend census. Which parser emits a usable AST envelope, what
vocabulary does the core slice actually use, and does the parser's verdict
agree with the suite's own?** No semantics and no evaluation — M1 is the
ingestion tier, the same shape the C lane's M1 had, and it is chosen for
the ordinary reason that nothing can be evaluated before it is ingested.
(It is NOT chosen to dodge the Number question: §4.2(a) measured that
question out of the way, so M1 owes the sequencing no apology.) The
measurements below were taken WITH this charter, because a milestone
whose feasibility is asserted is not planned.

### 5.1 The frontend candidates, and the one measured

* **The ESTree ecosystem.** ESTree is the de facto AST interchange format
  for JavaScript tooling, with several independent producers — acorn,
  espree, meriyah, `@babel/parser`. A format with
  multiple independent implementations is exactly what the envelope
  discipline wants: the frontend is replaceable and the envelope is the
  contract.
* **engine262's own parser** — 15 files, 11,543 lines, producing a
  spec-shaped tree with the spec's own nonterminal names rather than
  ESTree's. Structurally closer to clause 12-15; ecosystically isolated.
* **The precedent worth naming: engine262 IS the "implement the spec in a
  language" experiment already run once.** 68,429 lines of JavaScript,
  1,782 spec anchors, directory names taken from the spec's clause names.
  A Lean-implements-the-spec tier is the same experiment in a language
  where the result can be a theorem instead of a test pass. That is the
  lane's one-sentence justification and it is measured, not rhetorical.

**Measured, with acorn, over the whole 18,114-test core slice, one node
process for the batch, exactly one row per job, 0 runner errors:**

| | tests |
| --- | ---: |
| parsed | 14,045 |
| rejected | 4,069 |
| **distinct ESTree node types across the entire slice** | **66** |

Sixty-six. The C lane's rung-0 vocabulary was 45 AST node kinds and that
number turned out to clear 83% of five C test suites. **The ES core
slice's whole syntactic vocabulary is 66 ESTree node types**, enumerated
in the census JSON — from `ArrayExpression` to `YieldExpression`. A
`LeanModels/Es/Ast.lean` is a bounded object, and the census says how
bounded before anyone writes it.

### 5.2 The round-trip guard, measured in advance

The envelope discipline demands a guard that the frontend is not silently
mis-reading the corpus. test262 supplies one for free: 4,248 core-slice
tests declare `negative: {phase: parse}`, which is a claim about the
PARSER that a parser can be scored against directly.

| acorn's verdict vs the suite's | tests |
| --- | ---: |
| agree — accepted, and not a parse-negative test | 13,760 |
| agree — rejected, and a parse-negative test | 3,963 |
| **over-reject** — rejected a positive test | **106** |
| **under-reject** — accepted a parse-negative test | **285** |

**17,723 of 18,114 agree: 97.8%**, before anything is built. And both
disagreement classes decompose cleanly, which is what makes them work
items rather than mysteries:

* **All 106 over-rejects are feature-gated proposals**, not parser bugs:
  `dynamic-import` 84 (import-defer and source-phase-import variants),
  `decorators` 22, `class` 22. These are test262 tests for material ahead
  of any ratified edition — **§1.4's living-spec-versus-edition question,
  landing in the frontend and costing exactly 106 tests, all filterable
  by `features:`.** And it is a MECHANISM rather than an accident: the
  TC39 process makes tests a Stage 4 *entrance* requirement, so a
  proposal's tests necessarily land in test262 BEFORE the edition that
  will contain it. A suite ahead of every edition is the process working,
  and `features:` is the filter the process supplies with it.
* **The 285 under-rejects are EARLY ERRORS** — static semantics the
  parser does not carry, which is a real obligation and a nameable one.
  By feature: 181 untagged (the ES5/ES2015-era rules),
  `destructuring-binding` 53, `async-iteration` 17,
  `destructuring-assignment` 16, `generators` 10. By directory:
  `language/statements/variable` 31, `language/expressions/assignment`
  26, `language/expressions/compound-assignment` 23,
  `language/statements/for-in` 22, `language/expressions/arrow-function`
  16, `language/statements/for-of` 16. **Early errors are a
  static-semantics tier, they are enumerated, and they are 285 tests
  wide.**

### 5.3 The inches

Each separately green, separately landable, the triad green at every one,
and none touching `lakefile.toml`, `LeanModels.lean` or `lean-toolchain`.

1. **The census instrument and this charter. LANDED** —
   `harness/es_census.py`, `harness/es/acorn_probe.mjs`,
   `docs/es262-census.json`, `docs/es-charter.md`, `docs/backlog.md` §.
2. **Pin the edition. The DELTA IS ALREADY TAKEN (§1.4.1) and the token
   is RATIFIED (§0)** — the core slice's shape does NOT move between a
   ratified edition and the tip, only its counts. What remains is
   mechanical: make `ES2026` a constant the census, the envelope and the
   module path all read, so a future re-census cannot silently compare
   across editions. Confirmation-only from §6's first item.
3. **`docs/es-envelope-schema.md`**, schema `es-0.2`, mirroring
   `docs/envelope-schema.md`, `docs/sv-envelope-schema.md` and
   `docs/c-envelope-schema.md`. **Every vocabulary table DERIVED from
   `docs/es262-census.json`** — the 66 node types — rather than chosen, so
   "what the ingester accepts" and "what the corpus contains" cannot
   drift. Carries **`language_version: "ES2026"`** as a first-class
   top-level field per `docs/family-architecture.md` §1.5 — the same
   string that names the directory, so path, envelope and citation cannot
   drift, and the ingester REFUSES a mismatch exactly as `load_c_program`
   refuses a `profile_id` mismatch. `frontend.version` separately carries
   the FRONTEND's family (`acorn-8`), never a point release.
4. **`extractors/es/extract.py`** under the never-fail contract: never
   fails on valid ECMAScript; anything outside the pinned vocabulary
   becomes an `Unsupported` leaf carrying the node type and ≤200
   characters of source; deterministic double-run; hard errors exit
   non-zero and say why. Anchors: the Python extractor is **1,955** lines,
   SV's 2,495, C's 531 (clang does the work there). ESTree is a JSON tree
   already, so this lane is nearer the C end.
5. **`LeanModels/Es/Ast.lean` + `Json.lean`** — the deep-embedded AST for
   the 66 node types and the elaboration-time ingester, mirroring
   `load_program`. No semantics; the inch produces a Lean TERM and nothing
   evaluates it. Placed per `docs/family-architecture.md` §1.1: the AST
   and ingester are version-NEUTRAL and sit in `LeanModels/Es/`;
   `LeanModels/Es/ES2026/` is created only when this edition first decides
   something for itself, which on the §1.4.1 delta the syntax layer does
   not.
6. **One program round-tripped with its `#guard`s**, structural facts the
   census independently knows. Candidate fixture: one of the 3,963
   agree-reject tests paired with one positive test from
   `language/statements/if`, so **the tier's first word about ECMAScript
   includes something it must REJECT** — the reasoning that chose
   `pyfloordiv` for the C lane.

### 5.4 What M1 deliberately does NOT decide

Whether `Run` gains an error-type parameter or moves to
`LeanModels/Core/` (§4.1); whether the tier ever gets a JS driver twin
(§4.4); and the endgame. **The Number representation is no longer on this
list**: §4.2(a) measured it out of M1's way. M1 is
endgame-neutral by construction: every road needs the corpus ingested and
nothing in `LeanModels/Es/` presupposes a choice.

---

## 6 STILL OWED BY THOMAS

1. **THE PINNED EDITION.** The recommendation is **`es2026-errata`** —
   the 17th edition plus errata, which §1.4.1 measures to be
   structurally identical to `es2026` (764 bytes, zero structural
   deltas) — with test262 pinned separately by revision and filtered by
   `features:`. The alternative is tracking `main`, the ES2027 draft,
   which moves continuously. **§1.4.1 prices the choice: the taxonomy is
   edition-invariant, so the cost of pinning is 249 numbered steps of
   newer built-in material and nothing structural.** This blocks inch 2
   and therefore 3-6, and it is the one item on M1's critical path.
2. **THE NUMBER QUESTION — RESOLVED DOWNWARD by measurement, and no
   longer a decision this charter asks for (§4.2(a)).** Core `Float` on
   the pinned toolchain is a kernel-reducible bit-level binary64 model,
   verified by `rfl` on `0.1 + 0.2 = 0.30000000000000004`, so the
   evaluation layer is already provided and the tier should simply use
   it. What remains is the REASONING layer — 2,918 lines of core
   definitions carrying 3 theorems — and it binds at the first theorem
   ABOUT float arithmetic, a proof-layer milestone this charter does not
   reach. **Listed here only to record that the Python lane's
   `docs/completeness.md` §6 is stale on the kernel-reducibility point.**
   Not blocking anything.
3. **THE DRIVER ARTIFACT** (§4.4). Recommendation: a test262 slice as
   rung 0, with `sunfish.js` recorded as an endgame candidate and NOT
   proposed. If Thomas wants the square to have a third vertex, that is a
   different and much larger charter.
4. **`Run σ ε α`** (§4.1). ECMAScript is the second consumer the C
   charter said would make this decision cheap, and its throw payload is
   an arbitrary language value. Owed at the first evaluation rule, not
   before.

Standing, and not a question: the census must be re-run with `--compare`
before any number in this document is cited again. Three moving upstream
repositories is one more than the C lane had, and that lane's record
carried a stale "still owed" for five days across a single repository
boundary.

---

## 7 WHAT LANDED WITH THIS CHARTER

* `harness/es_census.py` — the instrument: spec, suite, engine and
  frontend modes, `--compare`, `--self-test` exercising all three refusal
  paths.
* `harness/es/acorn_probe.mjs` — the frontend half, one process per
  batch, one row per job, a loud exit-3 refusal when acorn is absent
  rather than an empty vocabulary.
* `harness/es/float_probe.lean` — nine kernel claims, import-free, that
  re-measure the Python lane's recorded float deferral (§4.2(a)). It
  needs no build, so it cannot break one.
* `docs/es262-census.json` — every number above, machine-readable,
  including the 66-type ESTree vocabulary and the 16 host hooks by name.
* `docs/es-charter.md` — this document.
* `docs/backlog.md` § — the record.

Also taken, and re-derivable rather than stored (§1.4.1): the census of
the `es2026` and `es2026-errata` edition tags, which prices the pinning
recommendation instead of merely asserting it, and which produced the
lane's second cross-language result — **the taxonomy is
edition-invariant**, the C lane's "the surface did not move" arriving in
a second language against a different kind of boundary.

**No change to any existing file**, and the only Lean is an import-free
probe under `harness/` that nothing imports and no build target names.

**The triad is PARTIAL and the gap is recorded, not papered over.**
`docs_check` is green at 74/74 marked blocks; `es_census.py --self-test`
is green on all three refusal paths; `--compare` is byte-identical on a
double run; and `float_probe.lean` passes all nine kernel claims under
the pinned `lean`, non-vacuously. `lake build`, `diff_test` and
`script_corpus` were NOT run: the machine-wide build lock was held
continuously by a sibling lane and two queued triads died at exit 144
while spinning on it — externally killed, as it turned out, by another
lane's orphan cleanup matching on a shared session-directory path prefix
rather than on parentage, not by the load this first recorded. **"It cannot break anything" is an argument
rather than a measurement** — the argument is strong here (no built Lean
changed at all) but it is still an argument, so the build third is
recorded as OWED and the next lane to hold the lock should run it on this
commit. Writing numbers for a build nobody watched would have failed this
document's own covenant in its last paragraph.
