# The Ada tier: FOUNDING CHARTER

**Status: the workstream's founding document**, written to Thomas's family
directive (versioned, spec-mirrored surfaces). It does four things and no
more: it MAPS the spec with an instrument that lands beside it, it CENSUSES
the conformance suite with a second one, it prices the scale honestly, and it
plans the first milestone. **No semantics are built here and none is
designed.** §6 lists what Thomas still has to answer.

It follows [docs/c-tier-charter.md](c-tier-charter.md) and
[docs/c23-goal.md](c23-goal.md) as templates, and cites them wherever a
decision is already taken rather than re-deriving it. Where Ada forces a
DIFFERENT answer, the charter says so and says what measured it.

**It is written to [docs/family-architecture.md](family-architecture.md)**,
which landed while this census was running and which carries an Ada registry
row (§1.2) and an Ada mapping row (§4.3), both marked **PROPOSED** and both
this lane's to fill. §0.1 below ratifies the registry row; §1.5 fills the
mapping table; §5 follows the §8 founding checklist in its order. The family
charter says of Ada that it is *"the finest taxonomy in the family and the
best fit for REFUSE-with-a-cause"* and asks a question directly:

> *"Ada is the stress test of whether four causes are enough; if a fifth is
> needed, Ada is where it will show."*

**§1.5.1 answers it, and the answer is no — a fifth REFUSE cause is not what
is missing.** What is missing is a VERDICT, because at Ada's bounded-error
sites the DIVERGE test is set membership rather than equality.

---

## 0 THE ONE THING THAT IS DIFFERENT ABOUT ADA

Every other tier in the family scores against a PROXY. The Python lane scores
against CPython's observed behavior; the C tier scores, by
[docs/c23-goal.md](c23-goal.md)'s own words, against *"three compiler
projects' regression histories plus one vendor's suite"*, and that document
is blunt that a high score there would mean *"agrees with what these projects
test"*, **not** *"conforms to ISO 9899:2024"*. It records the reason: **there
is no official ISO conformance suite for C.** ISO publishes the standard, not
a corpus.

Ada is the exception, and it is the reason this tier exists.

> **ISO/IEC 18009** — *Ada: Conformity assessment of a language processor* —
> is a standard for TESTING Ada implementations, and the ACATS is the corpus
> that instantiates it. The ACATS is maintained by the Ada Conformity
> Assessment Authority, distributed to the general public, and every one of
> its 4945 Ada source files carries an explicit grant of unlimited rights
> (§2.5, measured).

§2.6 states precisely what that changes about the goal definition, and it is
less than one might hope and more than the family currently has language for.

### 0.1 THE REGISTRY ROW, ratified

[docs/family-architecture.md](family-architecture.md) §1.2's row for Ada
reads `Ada | spec-mirror — ISO/IEC 8652 | PROPOSED | a compiler | ACATS |
founding`, and §8 step 0 makes it the founding lane's to ratify with a
census. Filled:

| field | value | measured where |
| --- | --- | --- |
| `<Lang>` | `Ada` | — |
| authority | **spec-mirror**, ISO/IEC 8652 | §1.7 |
| edition tokens | **`Ada2022`** (the spec head) and **`Ada2012`** (the suite's edition) | §1.3 |
| oracle | **a GNAT toolchain, and there is none on this host** | §4.2 |
| corpus | **ACATS 4.2**, 4,188 tests | §2.2 |

The two tokens satisfy §1.1's four laws — each is a valid Lean identifier,
self-identifying out of context (`LeanModels/Ada/Ada2012/` says exactly what
it is), naming a published edition rather than a patch level, and neither
will ever need renaming. **Ada is the first tier in the family to declare TWO
edition tokens at founding**, and §1.3 is why that is forced rather than
ambitious.

**One correction to the registry row, and it is not cosmetic.** The `oracle`
column says *"a compiler"*, which for every other spec-mirror tier is the
whole story: C targets ISO 9899 and runs clang; SV targets IEEE 1800 and runs
a simulator. Ada has a third authority those tiers do not — **an official
suite with its own published grading rules and its own grading tool**, owned
by neither the standards body nor an implementer. §2.4 and §2.6 are about
what that changes, and §4.2 of the family charter's precedence rule needs one
sentence added for it: the SPEC is the target, the IMPLEMENTATION is the
oracle for behavior, and **the SUITE OWNER is the authority for the expected
VERDICT.**

---

## 1 THE SPEC MAP

### 1.1 The instrument

`harness/ada_spec_census.py`, landed with this charter, run as

```
python3 harness/ada_spec_census.py <dir-of-RM-*.TXT> -o docs/ada-spec-census.json
python3 harness/ada_spec_census.py <dir> --compare docs/ada-spec-census.json
python3 harness/ada_spec_census.py --self-test
```

Input is the ARM's own plain-text rendering, which the ACAA publishes.
Nothing is vendored (§1.7). Output is sorted and a double run is
byte-identical (verified).

**The measurement rule it had to get right, and the trap in it.** At column 0
a subclause heading (`9.1 Task Units`) and a dotted paragraph number
(`28.1  Storage_Error is propagated ...`) have the SAME SHAPE, and both occur
in the real document — the second in Annexes B, G and H. A line-shape rule
would silently miscount either subclauses or paragraphs, and there would be
no symptom. So the instrument reads the subclause list out of the document's
own **table of contents** and then REFUSES if a clause file does not contain
exactly the headings the TOC promised, in order. The two halves of the
document check each other.

**All refusal paths were RUN, not admired**: a missing directory, a directory
with no `RM-*.TXT`, a missing `RM-TOC.TXT` (without which the instrument
would be guessing), a clause file whose headings disagree with the TOC, and a
run attributing zero paragraphs — an empty census is an instrument fault,
never a finding. The `--self-test` fixture is built from the shapes that
would produce a wrong answer, the dotted-paragraph-number ambiguity included.

### 1.2 The document, measured

The edition is read out of the text rather than assumed: **ISO/IEC 8652:2023,
informally Ada 2022**, in the consolidated edition that carries the 2025
Amendment 1.

| dimension | measured |
| --- | ---: |
| clause and annex files | **28** |
| subclauses | **477** |
| numbered paragraphs | **14,262** |
| core (clauses 1-13 + Annexes A, B, J) — ARM 1.1.2's own partition | 373 subclauses, **11,156** paragraphs |
| clauses 1-13 alone (the language, no library) | 232 subclauses, **5,927** paragraphs |
| Specialized Needs Annexes (C, D, E, F, G, H) | 92 subclauses, **2,083** paragraphs |

The core/SNA split is not a scoping choice this charter invented: ARM 1.1.2
partitions the document that way and ARM 1.1.3 defines conformance
**separately** for the core and for each SNA. A tier scoped to the core is
making a claim the standard already has a word for — which no other tier in
the family can say.

### 1.3 THE VERSION PAIR IS FORCED, NOT CHOSEN — and this is the charter's first real finding

The family directive asks for versioned, spec-mirrored surfaces. In Ada the
version structure is not a design decision available to us:

* the **ARM** censused above is **Ada 2022** (ISO/IEC 8652:2023, plus the
  2025 amendment);
* the **ACATS baseline is 4.2**, dated 2024-06-28, and its own modification
  list states that it *"is the current test suite for Ada, covering the third
  edition of Ada, ISO/IEC 8652:2012"*. The suite's User's Guide §1 says the
  same. Measured: the string "Ada 2022" appears nowhere on the ACAA's ACATS
  page, and no ACATS 5.x exists.

**So the official suite is two editions behind the current standard, and
there is no way to score Ada 2022 against an official corpus today.** The
version sibling the directive asks for is therefore *Ada 2012 = ACATS 4.2*,
with Ada 2022 as the spec-side head. That is the opposite of the C tier's
shape, where the standard moved and the suites followed; here the suite is
the pinned artifact and the spec is the moving one.

Two consequences, both load-bearing and neither optional:

1. **A "conforms to Ada 2022" claim can never be scored against ACATS.** Any
   Ada-2022-only feature is, by construction, outside the official corpus.
2. **The tier's version pin belongs in the ENVELOPE**, exactly as the C
   tier's `profile_id` does ([docs/c-envelope-schema.md](c-envelope-schema.md)
   §2): same source + different language version = a different program, and
   Ada makes this concrete — ARM Annex J is a whole annex of obsolescent
   features, and ACATS 4.2's legacy tests are written against Ada 83's
   organization (§2.2).

Older baselines are maintained on the same page and are a real asset for a
versioned family: ACATS 3.1 for Ada 2005 and 2.6 for Ada 95, both on limited
maintenance since 2021-10-01, and ACVC 1.11 for Ada 83, unmaintained.

### 1.4 THE RIGOR APPARATUS — the richest behavior taxonomy in the family, counted

ARM 1.1.2 labels the text of every subclause under a fixed set of headings.
This is the thing that makes Ada different from every other spec the family
has met: the standard has already done the classification work that the C
tier had to do by hand across 45 node kinds and eleven armed UB classes.

Measured, whole document and clauses 1-13 (the language proper):

| ARM heading | paragraphs, whole doc | paragraphs, clauses 1-13 | subclauses carrying it |
| --- | ---: | ---: | ---: |
| Syntax | 572 | 480 | 162 |
| Name Resolution Rules | 248 | 229 | 98 |
| **Legality Rules** | **953** | **806** | 164 |
| **Static Semantics** | **6,973** | 1,707 | 351 |
| Post-Compilation Rules | 67 | 41 | 20 |
| **Dynamic Semantics** | **1,340** | 859 | 181 |
| **Bounded (Run-Time) Errors** | **104** | **57** | **40** |
| **Erroneous Execution** | **115** | **23** | **47** |
| Implementation Requirements | 343 | 69 | 90 |
| Documentation Requirements | 68 | 4 | 31 |
| Metrics | 61 | 1 | 12 |
| Implementation Permissions | 275 | 159 | 99 |
| Implementation Advice | 387 | 162 | 101 |
| Usage | 6 | 4 | 4 |
| Examples | 963 | 823 | 157 |
| *(no heading — subclause intros)* | 1,787 | — | — |

`NOTES` is in ARM 1.1.2's list and measures **zero**: the plain-text
rendering inlines notes as `NOTE n` paragraph text instead of emitting a
heading. The instrument reports what it found rather than what it expected,
and this line is here so the zero is not mistaken for a bug.

Two readings worth stating:

* **Static Semantics dominates the document (6,973) but not the language
  (1,707).** The gap is Annex A — 102 subclauses, 4,507 paragraphs, almost
  all of it library package specifications published under that heading. Any
  "how big is Ada's static semantics" number that does not say which of the
  two it means is not a number.
* **The two hazard classes are SMALL and they are concentrated.** 104
  bounded-error paragraphs over 40 subclauses; 115 erroneous-execution
  paragraphs over 47. In clauses 1-13 — the language proper — it is 57
  paragraphs over 16 subclauses and 23 over 15. Compare the C tier,
  which had to enumerate its eleven UB classes itself and then argue they
  were the right eleven. Here the standard hands over the list, indexed by
  subclause.

### 1.5 THE MAP to the family's refusal taxonomy — §4.3's Ada row, FILLED

[docs/family-architecture.md](family-architecture.md) §5.2 fixes REFUSE as
**four** disjoint causes that *"retire on completely different schedules"*:
`unsupported` (out of tier — retires by climbing a rung), `undefined` (the
language says this run has no meaning — **never** retires, it is the
product), `environment` (outside the modeled slice — retires by widening it),
and `order-dependence` (several admissible orders, the invariant not shown
under all). Ada's four error categories, which ARM 1.1.5 sets out directly,
map onto that as follows. Three of the four fit an existing slot. One does
not fit any.

| ARM 1.1.5 category | ARM's own words, paraphrased | the family's class |
| --- | --- | --- |
| errors detected before run time | any violation of a Legality Rule or Post-Compilation Rule; the program is **not a legal Ada program** | **not a refusal at all** — this is a VERDICT the family lacks, see §2.3 |
| errors detected at run time | the predefined exceptions; the implementation is *required* to raise the corresponding exception | an ORDINARY OUTCOME. `Run.exn` already carries this shape ([docs/c-tier-charter.md](c-tier-charter.md) §2.3) |
| **bounded errors** | not expected to be detected, but *"the range of possible effects shall be bounded"*, and the possible effects are **specified for each such error** | **fits none of the four** — §1.5.1 |
| **erroneous execution** | like bounded errors, but *"there is no language-specified bound on the possible effect"* | cause 2, **`undefined`**, exactly. Never retires; it is the product |

And the two non-error variabilities:

| ARM notion | the family's answer, already decided elsewhere |
| --- | --- |
| **implementation defined** | the PROFILE. [docs/c-profile.md](c-profile.md)'s ruling — *pin the facts the corpus depends on as a schema every host must satisfy*, with a `#guard` per host rather than an anointed machine — transfers verbatim, and [docs/family-architecture.md](family-architecture.md) §8 step 3 makes it a founding step. §1.5.2 is why Ada makes it far cheaper |
| **unspecified** | cause 4, **`order-dependence`**, plus the ∀-PARAMETER shape [docs/family-architecture.md](family-architecture.md) §3.6 states in general and [docs/c-tier-architecture.md](c-tier-architecture.md) §3.2 instantiates for C: fix a canonical resolution, census that the choice is unobservable, refuse where the census cannot show it. §1.5.3 measures the scale |

#### 1.5.1 BOUNDED ERRORS — the answer to §4.3's question, and it is not a fifth cause

[docs/family-architecture.md](family-architecture.md) §4.3 predicts that if a
fifth REFUSE cause is needed, Ada is where it will show. **It does not show.
Something else does.**

Walk the four causes against a bounded-error site. The construct is in the
vocabulary, so not **cause 1**. The standard describes the behavior fully —
*"the possible effects of a given bounded error are specified for each such
error"* — so calling it **cause 2, `undefined`, would be a false statement
about the language**, and false in the expensive direction: it refuses a
program the standard fully describes, and the refusal is then
indistinguishable on the scoreboard from a tier gap, which is the exact
conflation §5.2's breakdown exists to prevent. Nothing is missing from the
modeled slice, so not **cause 3**. And it is not **cause 4**: cause 4 is
about ORDERS, and its obligation is that *every* admissible order gives the
same observable — a ∀. A bounded error admits several OUTCOMES and its
obligation is that the model's outcome is *some* permitted one — an ∃.

> A bounded error's meaning is a **finite, spec-enumerated SET of permitted
> outcomes**, always including `Program_Error`, and a model is correct at
> such a site when the outcome it produces is **in** that set.

**The ∀-parameter shape handles the proof side and does NOT handle the
scoreboard side, and that asymmetry is the finding.**
[docs/family-architecture.md](family-architecture.md) §3.6 makes
nondeterminism an explicit parameter and puts the quantifier at theorem
level: `∀ schedule, the run under that schedule satisfies the spec`. That
works for a bounded error too — make the choice a parameter, quantify ∀ over
the permitted set, and every theorem goes through. What it does not survive
is a DIFFERENTIAL score. A scoreboard compares one observable to one oracle's
observable, and at a bounded-error site **two conforming implementations may
disagree and both be right**. Scoring byte equality there manufactures
DIVERGEs, and DIVERGE is the family's zero-tolerance invariant.

So the gap is not in the REFUSE taxonomy. It is one level up:

> **The DIVERGE test is not equality at every site.** At a bounded-error site
> it is membership in a spec-enumerated set. The family's scoreboard has no
> way to say that, and refusing instead is a coverage loss the language does
> not require.

Two ways to close it, and **this charter takes neither** — it is Thomas's,
and §6 lists it:

* **MATCH-by-membership.** The site carries its permitted set; MATCH means
  the model's outcome is in it; DIVERGE means it is not. Costs: the
  scoreboard gains a per-site datum, and MATCH stops meaning "agrees with the
  oracle" at those sites, which must be reported separately or the headline
  number quietly weakens.
* **REFUSE with a new cause.** Cheap, honest, and it forfeits every
  bounded-error site. Given the measured scale that may be the right trade.

The scale, measured, is what makes either affordable: **104 paragraphs over
40 subclauses whole-document, and 57 paragraphs over 16 subclauses in clauses
1-13.** Small enough to enumerate by hand at the milestone that needs it —
and the standard has already done the enumeration, which is the whole reason
Ada could surface this and C could not.

#### 1.5.2 IMPLEMENTATION-DEFINED: Ada enumerates its own profile

The C tier had to DERIVE its profile: [docs/c-profile.md](c-profile.md)
records 13 facts probed by `_Static_assert`, 8 of them depended on, because
C's implementation-defined characteristics are scattered through the standard
with no index. Ada publishes the index.

Measured: **Annex M.2, "Implementation-Defined Characteristics", lists 202
items**; M.1 lists 53 further specific documentation requirements; M.3 lists
174 implementation-advice items. Across the whole document the phrases
"implementation defined" and "implementation-defined" occur 441 times, 283 of
them in the core.

So the Ada profile schema is not a research task — it is a transcription task
with a fixed, standard-supplied denominator, and the interesting number is
how many of the 202 a given corpus actually DEPENDS ON. That is a
`c_profile_probe.py`-shaped measurement, and it is milestone work rather than
charter work.

**One consequence that is charter work.** ARM 1.1.3 requires a conforming
implementation to *"contain no variations except those explicitly permitted
by this Reference Manual"* and to *"specify all such variations in the manner
prescribed"*. Annex M is that specification. A Lean tier claiming core
conformance therefore owes a document of the same shape — its own Annex M —
and the family's `profile_id` field is where it lives.

#### 1.5.3 UNSPECIFIED: the shape transfers, the scale is measured

"Unspecified" appears **128 times whole-document, 109 in the core**. The
family's answer applies unchanged in shape —
[docs/family-architecture.md](family-architecture.md) §3.6's explicit
parameter with the ∀ at theorem level, and §5.2 cause 4 on the scoreboard,
instantiated for C by [docs/c-tier-architecture.md](c-tier-architecture.md)
§3.2 as canonical resolution plus a census that the choice is unobservable.
The C tier's argument for that over Cerberus-style exploration is a fact
about the family's `Run σ α` outcome type and its one-line-per-job batch
protocol, not about C, so it carries.

What does NOT carry is the C tier's *content*: C's unspecified surface is
dominated by evaluation order within full expressions, which
[docs/c-semantics-design.md](c-semantics-design.md) §4.4 reduced to 20 sites
on the flagship corpus. Ada's is broader by construction — parameter
evaluation order, the order of some checks, and more — and nobody has counted
it against a corpus. That count is milestone work, and it needs a frontend
(§4).

### 1.6 What the spec map settles, and what it does not

**Settles.** The version pair, and that it is forced (§1.3). That the
core/SNA scope split is the standard's own and carries a conformance
definition with it. That the hazard classes are enumerable and small. That
"implementation defined" has a standard-supplied index of 202. That bounded
errors are a genuinely new class for the family, with a measured size.

**Does not settle.** Any mapping from ARM clause to a Lean construct — that
needs a frontend, and there is none (§4). Which of the 202 implementation-
defined characteristics a corpus depends on. Whether the tier's Unspecified
census is the same census shape the C tier uses, since Ada's unspecified
surface has not been walked. And nothing here re-measures the ACATS: §2 does
that with a separate instrument, deliberately, because a spec census and a
suite census that shared code would agree with each other for the wrong
reason.

### 1.7 Licence, and the cite-and-paraphrase convention

The ARM's own title page carries the terms, and they are unusually generous
for a standards document: it may be copied in whole or in part, in any form,
as is or with alterations, provided alterations are clearly marked as such
and the copyright notice is included unmodified in any copy. Copyright is
held across Intermetrics, MITRE, Ada-Europe and AXE Consultants, with the
1992-1995 portion assigned to the U.S. Government.

**The convention this charter follows, and every Ada-lane document after it:
CITE by clause number, PARAPHRASE the rule, and quote only short operative
phrases.** The reason is not doubt about the licence — it is the notice
requirement. Reproducing ARM text at length would drag an unmodified
copyright notice into this repository's files, and the family's
fetch-don't-vendor default ([docs/c23-goal.md](c23-goal.md) §2) already says
the right thing: **fetch the ARM at census time, pin the edition, vendor
nothing.** `docs/ada-spec-census.json` stores per-file sha256 digests, so a
re-census is checkable without a copy of the text living here.

---

## 2 THE ACATS CENSUS

### 2.1 The instrument

`harness/ada_suite_census.py`, landed with this charter:

```
python3 harness/ada_suite_census.py <unpacked-ACATS-dir> -o docs/ada-suite-census.json
python3 harness/ada_suite_census.py <dir> --compare docs/ada-suite-census.json
python3 harness/ada_suite_census.py --self-test
```

It groups files into tests by the suite's own seven-character naming
convention, and reports per test: class, legacy-vs-modern naming, core vs
SNA, the clause under test, files and extensions, foundation dependence,
size, the per-file rights grant, the B-test error markings, the Report
protocol calls, the library units `with`ed, and the Ada features used.

**Three things about how it measures, because each could have been a silent
wrong answer.**

1. **There is no Ada frontend on this host (§4.2), so this is a LEXICAL
   census.** Comments, string literals and character literals are removed by
   a small Ada scanner before anything is counted. Ada's `'` is both the
   character-literal bracket and the attribute prefix (`Integer'Last`), so a
   naive scanner eats the rest of the file at the first attribute; the
   scanner uses the language's actual rule — `'x'` is a literal only when the
   preceding token cannot end a name — and the `'"'` case is pinned in the
   self-test. With literals gone, RESERVED WORDS are unambiguous, so every
   bucket built from them is exact.
2. **Constructs that are not reserved words are NOT approximated.**
   Representation clauses and aspect specifications are left unmeasured and
   said to be unmeasured, rather than guessed at by regex. The one exception
   is generic INSTANTIATION, taken because leaving it out would understate
   Ada's scale badly — a test can instantiate the whole predefined generic
   library and never write the word `generic`. Its shape is unambiguous
   (`package|procedure|function <name> is new`, where a derived type is
   `type T is new`), it is measured by that shape, and it is named as a
   shape rather than as a reserved word. The self-test pins both directions.
3. **It cross-checks against the delivery's own manifest.** ACATS ships
   `ACATS42.LST`, a list of its 5263 files. An incomplete unpack would shrink
   every number in this census with no symptom, so a MISSING file refuses.
   Files on disk the list does not name are reported rather than refused —
   there is exactly one, `DIRS.BAT`, and reporting it is how that was found.

**All refusal paths were RUN**: a missing directory, a directory with no test
files, a run classifying zero tests, an undecodable file, and the manifest
check (exercised by deleting a file from a copy — it named the shortfall and
exited non-zero). Double run byte-identical, verified.

### 2.2 The delivery, measured — and it re-derives the User's Guide's own table

The strongest validation available for a census instrument is that the corpus
publishes its own count and the instrument reproduces it. ACATS User's Guide
§4.1 publishes a table. Measured against it:

| dimension | User's Guide §4.1 | this census |
| --- | ---: | ---: |
| files, total | 5263 | **5264** (the 5263 listed, plus the unlisted `DIRS.BAT`) |
| tests | 4188 | **4188** |
| core tests | 3996 | **3996** |
| SNA tests | 192 | **192** |
| core test files | 4707 | 4961 test files = 4707 + 250 + the 4 `CZ` files |
| SNA test files | 250 | *(as above)* |
| foundation files | 70 | **70**, in **68** foundation units |
| documentation files | 208 | **208** |
| other | 28 | **28** = 24 support files + the 4 `CZ` tests |

Every row agrees. Two reconciliations were needed and both are findings
rather than fudges: the four `CZ` tests check the ACATS's own reporting code
and the User's Guide counts them under *Other*, not as tests; and `FCNDECL`
begins with `F` but is a customization package (User's Guide §5.2.3), not a
foundation. Counting it as one is off by exactly the amount that stops this
census reproducing the table, **which is how it was found**.

The rest of the delivery, measured:

| dimension | measured |
| --- | ---: |
| Ada source files in tests | **4,945** |
| lines of Ada in tests | **787,645** |
| tests by class | A **75**, B **1,484**, C **2,543**, D **4**, E **11**, L **71** |
| naming | legacy **2,788**, modern **1,400** |
| distinct units `with`ed | 1,907 — 138 predefined, 5 ACATS support, 1,764 test-local |

**Two-thirds of the official suite is LEGACY** — inherited from ACVC 1.12,
written in an ALL-CAPITALS style, and named on a scheme whose second
character is a chapter of the *Ada 83* implementer's guide. The User's Guide
says plainly that a legacy test's name *"sometimes will not correspond"* to
the clause of Ada 2012 that describes the feature. So the instrument reports
legacy tests' AIG chapter as such and never as an ARM clause; only the 1,400
modern tests are clause-indexed, and their distribution is in the JSON.

### 2.3 THE SIX CLASSES — and the verdict class the family does not have

User's Guide §4.2 defines six classes and says each test belongs to exactly
one, encoded in its name. Paraphrased, with the census's counts:

| class | what passing MEANS | count |
| --- | --- | ---: |
| **A** | compiles, binds, runs, reports `PASSED`. Legacy only | 75 |
| **B** | **must be REJECTED at compile time**, at the lines marked `-- ERROR:`, and no other error reported | **1,484** |
| **C** | compiles, binds, runs, reports `PASSED` or `NOT-APPLICABLE` | 2,543 |
| **D** | exact arithmetic on large literals; **a capacity error also passes** | 4 |
| **E** | runs, reports `TENTATIVELY PASSED`; graded by inspection against criteria in the source | 11 |
| **L** | **must fail to BIND**; must not begin execution | 71 |

> **1,555 of 4,188 tests — 37.1% of the official suite — are scored on a
> REFUSAL, not on a result.**

This is the census's most decision-relevant structural finding, and it is
worth being precise about why it is not merely a new verdict name.

**What a B test asks for is the opposite of what `.unsupported` means.** In
the family's vocabulary a refusal is the model declining: *the tier does not
cover this*, or *this run has no meaning*. A B test asks the model to
ASSERT — that a specific construct at a specific line is **illegal Ada**, and
that everything marked `-- OK` is not. Getting a B test right is a positive
claim about the Legality Rules, which §1.4 measured at 953 paragraphs
(806 in clauses 1-13). Getting it wrong by refusing too much fails the test
exactly as surely as refusing too little.

So `REFUSE` and `expected-illegal` must never be pooled. Concretely:

| the model | the test expects a rejection | the test expects a run |
| --- | --- | --- |
| rejects at a marked line | **MATCH** | **DIVERGE** |
| rejects at an unmarked line | **DIVERGE** (a false positive on legal code) | **DIVERGE** |
| runs it | **DIVERGE** | scored on the observable |
| declines — out of tier / unmodeled | **REFUSE** | **REFUSE** |

The bottom row is the family's existing REFUSE and it is honest in both
columns; the point is that the top three rows are all VERDICTS and none of
them is a refusal. A tier that mapped "my Legality Rules said no" onto
`.unsupported` would score B tests as agreement by declining to have an
opinion — the precise reward-hacking shape AGENTS.md's `~~>` discussion
exists to prevent.

**The B-test grading rules are finer than a binary, and the census counted
the fineness.** Measured across the 1,484 B tests:

| marking | occurrences | tests carrying it | what it means (User's Guide §4.2.2, §5.6.2) |
| --- | ---: | ---: | --- |
| `-- ERROR:` | **16,404** | 1,474 | an error MUST be reported here. Median 6 per test, max 251 |
| `-- OK` | 7,568 | 748 | this construct must **not** be flagged — the false-positive guard |
| `-- POSSIBLE ERROR:` | 584 | 43 | an error at **any one** of the marked places passes |
| `-- OPTIONAL ERROR:` | 313 | 84 | reporting or not reporting does not affect the grade |
| `-- ANX-C RQMT` | 167 | — | lines an implementation not claiming Annex C may reject |

Three rules follow that a scorer must implement and that the family has no
precedent for. **Only the LOCATION of a reported error is graded, never its
text** — the User's Guide is explicit that the manual does not specify error
message form and *"the ACATS must not prevent innovation in error handling"*.
**289 B tests carry exactly one `-- ERROR:` mark**, and for those the rule
degenerates to *rejected at compile time for any reason passes*. And
`POSSIBLE ERROR:` is a disjunction over locations, `OPTIONAL ERROR:` a
don't-care — so the grading predicate is a small constraint language, not a
diff.

`-- ANX-C RQMT` is the profile in miniature: the same test is graded
*unsupported* for an implementation not claiming Annex C and must pass for
one that does. It is the closest thing the family has yet seen to a
profile-parameterized expected result.

### 2.4 THE ORACLE — and it has two layers, one of which is machine-readable

**Layer one: the `Report` package.** Every executable test is structured
around it (User's Guide §4.6): `Report.Test` at the start, `Report.Failed`
at each failed post-condition, `Report.Result` at the end, printing a line
containing `PASSED`, `NOT-APPLICABLE`, `TENTATIVELY PASSED` or `FAILED`. The
`Ident_*` family exists to defeat optimizers — `Report.Ident_Int (1)`
returns 1 but not statically, so test code cannot be folded away.

Measured usage across the suite: `Report.Test` **2,707**, `Report.Result`
**2,707**, `Report.Failed` **2,586**, `Report.Ident_Int` **959**,
`Report.Comment` 493, `Report.Equal` 367, `Report.Not_Applicable` **308**,
`Report.Legal_File_Name` 77, `Report.Special_Action` 14. **2,717 tests use
Report.**

One measurement worth its own line, because getting it wrong halves the
number: **legacy tests write `USE REPORT;` and then call `TEST (...)`
unqualified.** A detector looking only for `Report.Test` finds 819 tests
instead of 2,707. The census looks for both and the self-test pins the legacy
shape.

The whole package is 15 subprograms in one 591-line file that ships with the
suite, and its body may be modified only with advance approval (§5.2.4).

**Layer two, and it is the part that has no analogue anywhere else in the
family: the suite ships a GRADER and an implementation-neutral trace
format.** ACATS 4.2 introduced automated grading tools — `GRADE` (2,825
lines), `GRD_DATA` (1,139), `TRACE` (247), `SPECIAL` (603), `VERSION` (65),
plus a summary tool `SUMMARY` (2,899) and `TST_SUM` (447). Their input is an
**event trace file**: a CSV whose records carry an event kind, a timestamp, a
name, a line, a position and a message, over 14 event kinds —
`CSTART/CEND/CERR/CWARN` for compilation, `BSTART/BEND/BERR/BWARN` for
binding, `EXSTART/EXEND/EXFAIL/EXNA/EXSACT` for execution, and `UNKN`.

The User's Guide states the design intent directly: the events are *"abstract
representations of the processes of an implementation"* and *"it should be
possible to map the processes of any Ada implementation into an event trace
file"*, chosen so that grading does not become a disincentive to innovation
in error handling.

> **That is a specified, machine-readable interface between "an
> implementation processed these tests" and "here is the grade".** Every
> other tier in the family had to invent its own scorer —
> `harness/refusal_census.py`, `harness/leanpy_survey.py`,
> `harness/c_refusal_census.py` as specced in
> [docs/c23-goal.md](c23-goal.md) §4.2. The Ada tier's scoreboard should
> **emit an event trace and run the ACAA's grader**, not re-implement
> grading. The B-test location rules, the `POSSIBLE`/`OPTIONAL` disjunctions
> and the L-test exceptions are then the ACAA's problem and not ours, which
> removes the single largest source of "we graded ourselves generously".

The tools are optional for ACATS 4.2 and the ACAA says it will use experience
with them to decide whether they become required.

### 2.5 THE LICENCE, per file, and it is the cleanest in the family

The family's law is per-file licences, and
[docs/c23-goal.md](c23-goal.md) §2 records why: c-testsuite's top-level MIT
covers *"all testing software, but not for individual test cases"*, and a
lane that vendored on the strength of it would have redistributed LGPL code
under a wrong notice.

Measured here, per file, on all 4,945 Ada test files:

| grantor | files |
| --- | ---: |
| the U.S. Government, under named DoD contracts (older tests) | **4,165** |
| the Ada Conformity Assessment Authority | **730** |
| AdaCore (contributed tests) | **50** |
| **no grant found** | **0** |

Every file carries a *Grant of Unlimited Rights* conferring, in the ACAA's
own words, rights *"to use, duplicate, release or disclose the released
technical data and computer software in whole or in part, in any manner and
for any purpose whatsoever, and to have or permit others to do so"*, with an
as-is disclaimer.

**The census carries two detectors and the difference between them is the
finding.** Keying on the heading *"Grant of Unlimited Rights"* finds 4,931 of
4,945: **14 files carry the operative sentence under no heading at all**. And
there is not one operative sentence but three grantors — a census that looked
for the ACAA's wording alone would have reported 730 of 4,945 files licensed
and 85% of the official suite unlicensed. That is the c-testsuite trap with
the sign flipped, and it is why the instrument matches the operative verb and
reports the grantor by name, with an `other` bucket that is listed rather
than swallowed.

**RULED (§6.4): fetch, pin by version, vendor nothing — unchanged from
[docs/c23-goal.md](c23-goal.md) §2, and for a different reason.** Here the
licence would permit vendoring outright, so **Ada is the one tier where
vendoring stays a legal one-command option**; the c-testsuite trap that forced
the policy elsewhere does not exist. The reason to fetch anyway is the one
that policy already had: uniformity across the family, a 41 MB corpus kept out of
the repository, and a pinned artifact that the `--compare` mode makes
staleness-detectable. The ACAA's own Notice adds a second reason to be
careful with wording rather than with copying: the suite *"should not be used
to make claims of conformance unless used in accordance with ISO/IEC 18009
and any applicable ACAA procedures"* (§2.6).

The one non-Ada thing in the delivery: 9 C files, 4 Fortran and 3 Cobol, used
by foreign-language-interface tests (User's Guide §4.1.6 names them: two
Fortran tests, eight C, one Cobol).

### 2.6 WHAT AN OFFICIAL SUITE CHANGES ABOUT THE GOAL DEFINITION

This is the question the charter exists to answer, and the answer has a sharp
positive half and a sharp negative half.

**What it changes — three things, each real.**

1. **The denominator stops being a judgment call.** The C goal document has
   to sample two of its five corpora and admit that *"a stratified sample is
   owed before any Fujitsu number is used for pricing"*. Here the denominator
   is 4,188 tests, of which 3,996 are core, and the User's Guide says
   directly that **all core tests must be processed with acceptable results
   for conformity assessment of the core language**. There is a defined 100%,
   it is published, and it is not ours to choose.

2. **The expected result is part of the artifact, per test, in a graded
   form.** Not "the suites' expected behavior" inferred from a `.expected`
   file or an exit convention, but a class, a set of marked locations, an
   applicability criterion, and — since 4.2 — a grading tool that consumes a
   specified trace format (§2.4). The scoring rules are the ACAA's, published
   in the User's Guide, and a disputed result has a defined process: a
   petition to the ACAA.

3. **"Not applicable" is a first-class, legitimate outcome.** 308 tests can
   report `NOT_APPLICABLE`; User's Guide §5.6.4 and Annex D list the common
   reasons. The family currently has no verdict that means *the artifact
   under test is permitted not to support this* — the closest is the C
   tier's profile, and the ACATS treats it as a graded result rather than a
   configuration. That is a better shape and the tier should adopt it.

**What it does NOT change — and this is the part that must be written down
before anyone is tempted.**

1. **It does not license the word "conformant".** The ACAA's Notice appears
   at the top of every test file and on its distribution page: the suite
   *"should not be used to make claims of conformance unless used in
   accordance with ISO/IEC 18009 and any applicable ACAA procedures"*. Those
   procedures involve an Ada Conformity Assessment Laboratory. **Running the
   ACATS in this repository produces a SCORE, not a conformance claim**, and
   every document in this lane must word it that way. This is stricter than
   the C tier's honest-scale statement, not looser: there, the disclaimer was
   ours to write; here, it is the corpus owner's and it is binding on how we
   speak.

2. **It does not make the suite a specification.** ACATS coverage is coverage
   of *test objectives*, not of ARM paragraphs. A high ACATS score means
   "agrees with the tests the ACAA wrote", which is a much better proxy than
   three compiler projects' regression histories but is still a proxy for
   §1.4's 14,262 paragraphs.

3. **It does not cover Ada 2022** (§1.3), and it does not cover the SNAs
   unless they are claimed — 192 of the tests are optional by construction.

4. **It does not make the tests easy to run.** The suite requires
   customization before use: `ImpDef` per implementation, macro expansion of
   the 62 `.TST` files, and `SPPRT13`/`FCNDECL`. Those are steps, not
   downloads.

**So the goal, restated in the form this project can actually score** — the
same restatement [docs/c23-goal.md](c23-goal.md) made, with the two Ada
amendments in bold:

> The Lean semantics, run over ACATS tests, reproduces **the grade the ACAA's
> own rules assign**, scored MATCH / REFUSE / DIVERGE with the zero-DIVERGE
> invariant — **with `NOT_APPLICABLE` a fourth first-class verdict, and with
> the B and L classes graded on rejection-with-location rather than on an
> observable.**

**And §6.3 ruled the last four words of that literally**: the grade is
assigned by the ACAA's own rules because it is assigned by the ACAA's own
TOOL. The tier emits an event trace and `GRADE` issues the verdict (§4.4).
Under §6.1 the score is then joined to a paragraph-granular coverage map of
the ARM itself (§5.8), so the two halves of the goal are: *what does the
standard say, clause by clause and paragraph by paragraph*, and *what does
the official suite, graded by its owner, say we got right*.

---

## 3 SCALE, HONESTLY

### 3.1 The frontend vocabulary: Ada is about seven times C's v0

[docs/c-tier-charter.md](c-tier-charter.md) §1.3 scoped the C tier's v0 to
**45 distinct AST node kinds**, and §1.4's headline was that the number did
not move across a real engine release. Measured from libadalang's grammar
(§4.2), which is the candidate Ada frontend:

| dimension | measured |
| --- | ---: |
| node classes declared | **315** — 294 `class` + 21 `enum class` |
| abstract | 47 |
| concrete plain classes | 247 |
| qualifier enums (each expands to a `Present`/`Absent` pair) | 14 → 28 |
| other enum alternatives | 41 |
| **concrete node kinds** | **316** |

**316 against 45.** That is the single number a reader should carry away from
this section, and it is not a criticism of Ada — it is a statement about how
much syntax a language with tasking, generics, tagged types, protected
objects, aspects, representation clauses and Annex J obsolescent forms
actually has. A tier that scoped itself to "the whole language" would be
pricing seven C tiers.

The count is derived from the grammar file's own declarations under a stated
rule; the authoritative count is whatever the built frontend reports, and
that is milestone-1 work, not charter work.

### 3.2 The feature census, and the ladder

Measured over the 4,188 language tests, by the reserved-word buckets of §2.1:

| bucket | tests using it |
| --- | ---: |
| exceptions (`exception`, `raise`) | **1,418** |
| separate compilation (`separate`, `limited`, `private`) | 1,190 |
| generic instantiation (by shape) | **1,113** |
| access types (`access`, `aliased`) | 979 |
| generic declaration (`generic`) | 915 |
| **tasking** (`task`, `protected`, `entry`, `accept`, `select`, `requeue`, `delay`, `abort`, `terminate`, `synchronized`) | **768** |
| real types (`digits`, `delta`) | 451 |
| tagged types (`tagged`, `abstract`, `interface`, `overriding`) | 413 |
| `goto` | 39 |
| `parallel` (Ada 2022) | **0** |
| *no bucket at all* | **755** |

`parallel` measuring zero is the §1.3 version gap showing up in the data: it
is an Ada 2022 keyword and ACATS 4.2 is an Ada 2012 suite.

**The ladder, with tasking excluded throughout** — the sequential-first
reading the charter is actually asking about. At each step the named bucket
is added; `cleared` is the number of tests using nothing outside the
accumulated set:

| step | added | tests cleared (of 4,188) | core (of 3,996) |
| ---: | --- | ---: | ---: |
| — | *nothing* | 755 (18.0%) | 739 (18.5%) |
| 1 | exceptions | 1,187 (28.3%) | 1,165 (29.2%) |
| 2 | access types | 1,437 (34.3%) | 1,406 (35.2%) |
| 3 | separate compilation | 1,753 (41.9%) | 1,721 (43.1%) |
| 4 | generic instantiation | 2,072 (49.5%) | 2,025 (50.7%) |
| 5 | generic declaration | 2,647 (63.2%) | 2,595 (64.9%) |
| 6 | real types | 3,048 (72.8%) | 2,958 (74.0%) |
| 7 | tagged types | 3,390 (80.9%) | 3,291 (82.4%) |
| 8 | `goto` | **3,420 (81.7%)** | **3,321 (83.1%)** |

The unrestricted greedy ladder — which is free to spend a step on tasking —
is in `docs/ada-suite-census.json` (`reach_ladder`); it picks tasking second
and reaches 100% at step 9.

### 3.3 THE MEASURED VIABLE CORE

The charter was asked to define one and say what ACATS fraction it reaches.

> **Sequential Ada — the language minus tasking — reaches 3,420 of 4,188
> tests, 81.7%; 3,321 of 3,996 core tests, 83.1%.**

Dropping tasking costs **18%** of the official suite. That is the number that
makes sequential-first defensible rather than a retreat, and it was not
predictable: tasking is Ada's most famous feature and it is used by 768 tests.

The comparison with the C tier is worth making because the shape is
strikingly similar: `docs/c23-goal.md` §4's headline was *"rung 0 already
clears 357 of 431 — 83%"*. Two different languages, two different corpora,
two different definitions of a core, and the same 83%. Nothing follows from
the coincidence, but it does mean the Ada tier is not proposing a worse
bargain than the one Thomas already ruled on.

**And the ladder says something sharper than "sequential is 82%": the bottom
of it is not where the value is.** A core with nothing in it clears 18%. The
first four rungs — exceptions, access types, separate compilation, generic
instantiation — take it to 49.5%, and none of those four is optional in any
realistic Ada. So the honest v0 statement is not "sequential Ada" but:

> **v0 = sequential Ada with exceptions, access types, separate compilation
> and generic instantiation — 2,072 tests, 49.5% — with generics, real types
> and tagged types as the three rungs that take it to 81%.**

### 3.4 THE CHEAPEST FIRST SCOREBOARD

The C tier's rung 1 was *"the exit-status corpora at rung-0 vocabulary: 196
reachable, needing only `abort`/`exit`"* — the cheapest first score because
it needs no output modeling. The Ada analogue, measured:

| filter | tests |
| --- | ---: |
| executable classes (A, C, D, E) | 2,633 |
| ...and no tasking | 2,194 |
| ...and `with`s **no predefined library unit at all** | **1,374** |
| ...of which core | 1,364 |
| ...of which class C | 1,322 |
| ...using **no feature bucket at all** | 322 |
| ...using at most `exceptions` | 517 |
| ...within {exceptions, access types, separate compilation} | 812 |

**1,374 executable tests need no predefined library beyond the ACATS's own
support packages.** That is the first scoreboard, and it is available before
any model of `Ada.Text_IO` exists.

### 3.5 THE LIBRARY SURFACE IS `Report`

The C tier's equivalent finding was *"the libc surface is not 'libc' — it is
`printf`"*. Ada's is stronger:

**3,025 of 4,188 tests — 72.2% — `with` no predefined language unit at all.**
Their entire library dependence is `Report` (and, for some, `ImpDef` and
`TCTouch`), all of which ship with the suite in source form under the same
grant. Only 222 tests `with` `Text_IO` or `Ada.Text_IO` directly.

`Report` is 15 subprograms in 591 lines: six reporting procedures (`Test`,
`Failed`, `Not_Applicable`, `Special_Action`, `Comment`, `Result`), six
optimizer-defeating identity functions, a recursive `Equal`, a
`Legal_File_Name` generator, and `Time_Stamp`. Its body uses `Ada.Text_IO`
and `Ada.Calendar` — so modeling `Report` means modeling exactly two library
units, and the tier controls the boundary because a model may implement
`Report` natively rather than execute its body.

That is a much smaller obligation than "model Annex A", whose specifications
are 4,507 of the ARM's paragraphs (§1.4).

### 3.6 WHAT IS NOT MEASURED HERE, and why that is deliberate

* **Representation clauses and aspect specifications.** Neither is a reserved
  word; both would need a parser to count. They are left out of the buckets
  rather than approximated by regex, so no ladder number here silently
  includes or excludes them. The frontend census (§5) settles them.
* **Anything semantic.** The buckets say what a test WRITES, which is a claim
  about what an ingester must accept. It is not a claim that a semantics
  would run any test, because **there is no semantics and none is designed
  here**. This is the same disclaimer [docs/c23-goal.md](c23-goal.md) §4
  attaches to its ladder, and it applies with more force: the C tier had an
  ingested corpus when it wrote its ladder, and this tier has nothing.
* **Any per-clause ARM coverage.** ACATS test objectives are gathered in the
  suite's own Test Objectives Document; joining that to §1.4's subclause
  table is a real and valuable measurement, and it is milestone work.
* **The 192 SNA tests are counted but not scoped in.** They are optional
  under ARM 1.1.3 and this charter does not propose claiming any annex.

---

## 4 THE DRIVER ARTIFACT

### 4.1 There is no ctwin analogue, and that is the tier's biggest structural gap

The C tier's whole method rests on a flagship: `tools/ctwin/sunfish.c`, a
node-identical transcription of `sunfish.py`, which is what makes it *"a
semantics corpus rather than a second engine"* and what makes the A ≡ C ≡ D
square possible at all. The Ada tier has no such artifact. Nothing in the
sunfish repository is Ada; nothing in this repository is Ada.

That is not fatal — the ACATS is a far better corpus than any single program
— but it costs two specific things, and they should be named rather than
discovered later: there is no **cross-language square** (no second model of
the same program to catch a misreading shared by a model and its oracle), and
there is no small, real, well-understood program to be the first thing
ingested, the way `pyfloordiv` was for C.

### 4.2 THE FRONTEND CENSUS — measured, and there is a trap in it

**There is no Ada compiler on this host.** Measured: `gnat`, `gnatmake`,
`gnatls`, `gprbuild` and `alr` are all absent; the installed `gcc` reports no
Ada in its enabled languages; Homebrew has no `gnat` or `alire` formula;
`libadalang` is not importable and is not on PyPI.

**The trap, recorded so nobody else loses an hour to it:** this host DOES
have an executable called `adaparse` on `PATH`. It is from the `ada-url`
package — a WHATWG **URL** parser named "Ada" — and has nothing whatever to
do with the Ada language. A frontend census that grepped `PATH` for `ada`
would report a parser that is not one.

The candidates, censused with licences verified from the repositories rather
than recalled:

| candidate | licence | state | verdict |
| --- | --- | --- | --- |
| **libadalang** | **Apache-2.0 WITH LLVM-exception** | active | **the extractor** |
| libadalang-tools (`gnatpp`, `gnatmetric`, `gnatstub`) | GPL-3.0 | active | tools, not a frontend |
| ada_language_server | GPL-3.0 | active | libadalang-based; wrong interface |
| tree-sitter-ada | MIT | active | a CST with no semantics — see below |
| `gnat2xml` / ASIS | — | **gone** | measured: no `gnat2xml` sources remain in libadalang-tools |
| GNAT's own dumps (`-gnatD`, `-gnatG`) | GPL-3.0 | — | expanded SOURCE, not an AST |

**libadalang can emit a usable AST, and this was checked rather than
assumed.** Its documented Python API — supporting Python 3.9 and 3.10 — is
`AnalysisContext()`, `context.get_from_file(path)`, `unit.root`, and
`root.finditer(...)` to walk every node. That is the same shape
`extractors/c/extract.py` gets from clang's JSON AST dump, and its licence is
the same Apache-2.0-with-LLVM-exception the C lane already accepted for two
of its corpora.

**The acquisition path, priced.** libadalang is written in Ada and generated
by Langkit, so building it needs a GNAT toolchain. Both pieces are in the
Alire index — `gnat_native` up to 16.1.0 and `libadalang` up to 26.0.0, the
latter declaring dependencies on `gnatcoll`, `gnatcoll_projects`,
`gnatcoll_gmp`, `gnatcoll_iconv`, `libgpr2` and `langkit_support`, all at
`^26`. So the path is: install `alr`, select a `gnat_native` toolchain, build
libadalang and its Python bindings. **That is a real, multi-step, from-source
build on a host that has no Ada compiler at all, and it is the first
milestone's critical path** — the exact analogue of the C tier's profile
inch, which was also a blocker that had to clear before any Lean was
possible.

**tree-sitter-ada is the fallback and the charter names it as one.** MIT,
active, no toolchain needed. It produces a concrete syntax tree with no name
resolution and no semantics, which is not enough for a semantic tier — but it
IS enough to run the frontend census of §3.6 (representation clauses,
aspects, per-clause coverage) if the libadalang build proves expensive. Using
it for the census and libadalang for the envelope would be two frontends,
which the family's cache-key discipline (`(source, extractor, profile)`)
handles by construction.

### 4.3 DRIVER-ARTIFACT CANDIDATES, priced

**(a) The ACATS's own tools — available today, and censused.** The suite
ships real Ada programs that do real work, under the same per-file grant:

| program | lines | features used (measured) | library units `with`ed |
| --- | ---: | --- | ---: |
| the grading tool (`GRADE`, `GRD_DATA`, `TRACE`, `SPECIAL`, `VERSION`) | 4,879 | access types, exceptions, `goto`, one generic instantiation | 10 predefined + 3 local |
| the summary tool (`SUMMARY`, `TST_SUM`) | 3,346 | exceptions, `goto` | 6 predefined + 3 local |
| the macro substituter (`MACROSUB`) | 548 | exceptions | `TEXT_IO` + 3 local |
| `Report` | 591 | exceptions | `Ada.Calendar`, `Ada.Text_IO` |
| `TCTouch` | 376 | exceptions | `ImpDef`, `Report` |

**Every one of them is sequential Ada.** No tasking, no tagged types, no
generic declarations. They sit inside §3.3's viable core, they are in hand,
and the grading tool is *the program that scores the suite* — modeling it
would be a pleasing kind of self-application. `Report` at 591 lines is the
obvious first ingest: small, sequential, and every executable test depends on
it, so it is on the critical path anyway.

**(b) An Ada twin of sunfish — RULED OUT by Thomas (§6.5), and the charter
records the reasoning rather than the option.** A hand-written Ada
transcription of `sunfish.c` would have made the Python↔C square a triangle
and bought the tier a cross-language differential claim. It was priced as a
from-scratch transcription of a 1,458-line program, nobody had volunteered,
and **it is dead**: the driver artifact is the corpus, not a bespoke program.

That decision has a consequence worth stating plainly, because it is what
makes §4.4 load-bearing rather than convenient: **the Ada tier will never
have a second independent model of the same program.** The C tier's §5.4
capstone exists to catch a misreading shared by a model and its oracle, and
Ada now has no structural defense of that kind. What it has instead is an
oracle nobody in this project wrote — the ACAA's grader (§2.4, §4.4) — which
is a different and, for a spec-mirror tier, arguably better answer to the
same worry: the entity that decides whether we passed is neither our model
nor our reading of the standard.

**(c) Nothing else.** The charter deliberately does not go shopping for a
third-party Ada program. The family's method is census-then-price, and a
corpus nobody has censused is not a candidate.

**So the driver artifact is (a), and it is not a placeholder.** `Report` is
the first ingest — small, sequential, and on the critical path regardless —
and the ACATS's own tools are the corpus behind it.

### 4.4 THE GROUNDING MOVE — Thomas ruled the grader, and it defines the tier

> **RULED (§6.3): the scoreboard is a TRACE EMITTER from day one. Verdicts
> for B-class tests and every other class come from the ACAA's own `GRADE`
> tool, consuming the event-trace CSV of §2.4.**

This is the tier's defining decision and it deserves to be stated where a
reader meets it rather than buried in a milestone list. Every other tier in
this family grades itself. The Ada tier does not.

**What it means concretely.** The Lean tier's job is not to decide MATCH or
DIVERGE. Its job is to *process a test and report what happened* in the
ACAA's published vocabulary — `CSTART`/`CEND`/`CERR` when it accepts or
rejects a compilation unit and at which line, `BSTART`/`BEND`/`BERR` for the
post-compilation rules, `EXSTART`/`EXEND`/`EXFAIL`/`EXNA` for a run and what
`Report` said. Those rows go into a CSV; `GRADE` reads the CSV beside the
suite's test summaries and issues the verdict.

**Four things this buys, each of which the charter would otherwise have had
to build and defend:**

1. **The B-test grading rules stop being ours.** §2.3 measured them: location
   only and never message text, 16,404 `-- ERROR:` marks, `POSSIBLE ERROR:`
   as a disjunction over locations, `OPTIONAL ERROR:` as a don't-care, 7,568
   `-- OK` false-positive guards, and 289 tests where one mark degenerates to
   "rejected for any reason passes". That is a small constraint language, and
   **we do not implement it.** The suite's own tool does.
2. **Self-generous scoring becomes structurally impossible.** The single
   largest failure mode for a self-scored conformance claim is a scorer
   tuned, however innocently, until the board is green. A scorer we cannot
   edit removes the temptation rather than resisting it.
3. **`NOT_APPLICABLE` arrives for free**, as a graded result rather than as a
   configuration flag — the verdict §2.6 identified as the one the family has
   no word for.
4. **The interface is designed to be implementation-neutral.** The User's
   Guide says the events are *"abstract representations of the processes of
   an implementation"* and that *"it should be possible to map the processes
   of any Ada implementation into an event trace file"*. A Lean definitional
   interpreter is an unusual Ada implementation, and it is exactly the kind
   the format was written to admit.

**What it costs, stated honestly.** `GRADE` is an Ada program (2,825 lines,
plus `GRD_DATA`, `TRACE`, `SPECIAL`, `VERSION` — 4,879 in total). Running it
requires an Ada compiler. **So the toolchain is load-bearing twice** — once
for libadalang as the frontend, once for `GRADE` as the scorer — which is why
§5.2 is the critical path and why §5.2's GNAT census is an M1 item rather
than a footnote. Grading with the ACAA's tool is optional for ACATS 4.2 and
the ACAA has said it will use experience with the tools to decide whether it
becomes required; this tier is choosing the stricter road while it is still
the optional one.

**And the corollary for M1's design.** A trace emitter is not something to
retrofit. The envelope (§5.4) must carry the spans a `CERR` row needs — a
line and a position per rejection — and the ingester must preserve the
ACATS's `-- ERROR:` markings, which live in comments an AST discards. Both
are listed in §5.4 as forced fields, and the ruling is why.

---

## 5 THE FIRST MILESTONE, planned

**M1: an Ada compilation unit is INGESTED. `Report`'s specification
round-trips source → envelope → Lean AST literal → `#guard`.** No semantics,
no memory model, no interpreter — the family template, and the same milestone
the C tier's M1 was.

**M1 was drafted endgame-NEUTRAL and §6's rulings did not change its
shape — they changed what three of its inches must carry.** Recorded so the
difference is visible rather than assumed: inch 2 gains the **GNAT toolchain
census**, because the ruling makes an Ada compiler load-bearing for the
behavior oracle and for the grader, not only for the frontend (§5.2); inch 4
gains **`CERR`-grade spans**, because a trace emitter cannot be retrofitted
onto an envelope that dropped them (§5.4); and inch 8's manifest goes to
**paragraph granularity** and is promoted from someday to planned (§5.8).
Everything else stands as drafted, which is what "endgame-neutral by
construction" was supposed to buy.

The inches follow [docs/family-architecture.md](family-architecture.md) §8's
founding checklist **in its order**, which is the C lane's measured order.
Each is separately green and separately landable; none touches
`lakefile.toml`, `LeanModels.lean` or `lean-toolchain`. Steps 0 and 2 of the
checklist — the registry row and the authority declaration — are done in this
document (§0.1, §1.5, §1.7) rather than in an inch, because they are prose
and they gate everything else.

**The layout this milestone commits to**, per §1.1 and §1.3: `LeanModels/Ada/`
is version-NEUTRAL and `LeanModels/Ada/Ada2012/` is version-SCOPED. The
boundary between them is a claim with an instrument behind it, and **inch 2
is that instrument** — the family charter's rule is to state the boundary
before writing the second edition's first line, and Ada declares two editions
at founding (§0.1), so the boundary must be drawn on day one rather than
discovered.

### 5.1 Inch 1 — the two census instruments and this charter. **LANDED.**

`harness/ada_spec_census.py` + `docs/ada-spec-census.json`,
`harness/ada_suite_census.py` + `docs/ada-suite-census.json`,
`docs/ada-charter.md`, and `docs/backlog.md` §L63. Zero Lean, zero risk to
any existing lane, and the artifact every later inch cites.

### 5.2 Inch 2 — THE TOOLCHAIN, and §6's rulings made it load-bearing THREE times

**Sequenced first because everything after it is blocked on it**, and the
rulings raised the stakes rather than lowering them. An Ada toolchain is now
needed for three separate reasons, and a plan that discovered that at inch 5
would be a bad plan:

| need | what for | ruled where |
| --- | --- | --- |
| **libadalang** | the frontend that emits the envelope | §4.2 |
| **GNAT** | the **behavior oracle** for differential grounding | §6.1 |
| **GNAT** | building the ACAA's `GRADE`, which issues our verdicts | §6.3, §4.4 |

The first half of the inch is therefore a census, not a build:
**`harness/ada_toolchain_census.py`** — what Ada compilers exist on each
development host, what Alire offers, and what it costs to get from here to a
working `gnatmake` and a working `import libadalang`. **At charter time the
answer on this host was NOTHING** (§4.2), and the census is what turns that
into a priced path rather than an impression. It is the M1 item the ruling
explicitly asked for.

The second half is `harness/ada_construct_census.py` — the §5.4 instrument
contract, named to the family convention — reporting the toolchain identity,
the libadalang version, and the concrete node-kind list the built frontend
actually has, replacing §3.1's grammar-derived 316 with a measured number.

**It also draws the version-neutral boundary** (§1.1's commitment above), the
same way the C lane drew its own: census the node kinds each edition's corpus
reaches and report the INTERSECTION. The C lane's evidence was *"zero of the
45 AST node kinds the tier ingests is post-C99"*; Ada's answer is unknown and
will be measured, and the interesting number is how many of the 316 kinds
exist only for Ada 2022. **The version pair is forced (§1.3), so
`LeanModels/Ada/Ada2012/` exists from commit one and the only open question
is what stays in the trunk above it.**

**This is the inch that can fail.** The failure mode is a from-source build
on a host with no Ada compiler; the fallback for the census half is
tree-sitter-ada (§4.2), and there is **no fallback for the oracle or the
grader** — those need a real GNAT. Which is precisely why the toolchain
census comes before anything that assumes one.

#### 5.2.1 THE TOOLCHAIN HALF IS DONE — the oracle and the grader are ALIVE

**`harness/ada_toolchain_census.py` + `docs/ada-toolchain-census.json`,
landed.** The charter said this host had no Ada compiler. It has one now, and
the acquisition path is measured rather than described:

| step | measured |
| --- | --- |
| `alr` | **2.1.1**, a prebuilt `aarch64-macos` binary — needs no Ada compiler to run |
| `alr -n toolchain --select gnat_native gprbuild` | **GNAT 16.1.0** and **gprbuild 26.0.1**, installed |
| `ALIRE_SETTINGS_DIR` pointed at a scratch dir | the whole install stays out of the home directory |

**And `--verify` drives §4.4's ruled grounding loop end to end, on the real
suite. All nine checks pass:**

1. a real class-C test (`C324001`) **builds and prints `PASSED`** through the
   shipped `Report` package — the oracle is alive;
2. the ACAA's **`GRADE` builds** from the suite's own sources;
3. the ACAA's **`SUMMARY` builds**;
4. **the CRLF trap fires** (below);
5. a C-test event trace grades to *"passed execution"*;
6. a B-test trace with a `CERR` at every `-- ERROR:` location grades to
   ***"passed by detecting all expected errors"***;
7. **NON-VACUITY, both ways** — drop one expected error and `GRADE` says
   *"failed by not reporting an error for an ERROR item at line 259"*; flag an
   error on a line marked `-- OK` and it says *"failed by having an error for
   an OK item at line 105"*. A grader that always said PASSED would be
   worthless, so this is checked rather than assumed.

> **The ruled grounding move is not a plan. It runs, it is re-runnable, and
> it fails correctly.** The one thing standing between here and a real
> scoreboard is a Lean tier that can emit those trace rows.

**THE CRLF TRAP, and it would have cost a later lane a day.** The ZIP
delivery ships CRLF, and the ACAA's `SUMMARY` tool **dies with an unhandled
Ada exception on every CRLF source**. Measured: **0 of 120 files summarized
as shipped; 150 of 150 after `\r` removal.** Which exception varies with the
input — `SUMMARY.PARSE_ERROR` and `ADA.STRINGS.LENGTH_ERROR` both observed —
so the check asserts that it raised, not which. `--verify` converts before
summarizing *and* asserts the trap on an unconverted copy, so the workaround
cannot silently stop being needed. (The ACAA also ships a `.tar.Z` delivery,
which is the likely LF-clean route; the census records the workaround because
it works on either.)

**What is NOT done: the frontend.** `libadalang` **26.0.0** deploys through
Alire with its whole dependency closure (`gnatcoll`, `libgpr2`,
`langkit_support`, `adasat`, `vss`, `xmlada`, `prettier_ada`) and **ships its
Python bindings in-tree** (`python/libadalang/__init__.py`), so the API §4.2
verified from the repository is present. What is not yet built is the
**shared** library the ctypes bindings load. Diagnosed precisely rather than
left as "it didn't work": a relocatable `libadalang` cannot import a static
dependency, so the whole closure has to be built relocatable together, and
the census records the exact `-X` externals. **`needs.frontend` is therefore
still `met: false`, and the instrument says so** — which is the point of
having it. The oracle and the grader are met; the frontend is inch 2's
remaining half.

### 5.3 Inch 3 — the profile

`docs/ada-profile.md` + `docs/ada-profile.json` + a probe, mirroring
[docs/c-profile.md](c-profile.md). The ruling to inherit is that document's:
**pin the FACTS the corpus depends on as a schema every host must satisfy,
with a guard per host rather than an anointed machine.** Ada makes the
denominator explicit — Annex M.2's 202 implementation-defined characteristics
(§1.5.2) — so the inch's real content is measuring which of the 202 the
corpus depends on, and it carries the same stop-condition the C profile
carried: *if the corpus depends on any fact where two hosts differ, stop and
flag.*

The `language_version` field lands here too, and it is not optional:
[docs/family-architecture.md](family-architecture.md) §1.5 makes it a
first-class top-level envelope field carrying the registry's edition token,
and Ada is the tier where the field earns its keep on day one, because §1.3's
spec/suite gap means the two tokens are BOTH live from the first envelope.

### 5.4 Inch 4 — `docs/ada-envelope-schema.md`

Schema `ada-0.1`, mirroring [docs/c-envelope-schema.md](c-envelope-schema.md).
**Every vocabulary table DERIVED from the frontend census of inch 2 rather
than chosen**, with a check that the schema lists exactly the kinds the
census found and nothing extra.

**Four things this envelope needs that its siblings do not**, each forced by
a measurement above or by a §6 ruling:

1. **`language_version` as a first-class field** alongside `profile_id`
   (§1.3, and [docs/family-architecture.md](family-architecture.md) §1.5).
2. **The ACATS's own markings, with line AND column** — `ERROR:`, `OK`,
   `POSSIBLE ERROR:`, `OPTIONAL ERROR:`, `ANX-C RQMT`. They are the expected
   result of 1,484 tests (§2.3) and they live in comments an AST discards, so
   the extractor must carry them out of the source itself.
3. **A compilation-unit list with ORDER.** Ada tests are multi-unit — 248 of
   4,188 span more than one file — and the compilation order is part of the
   test, encoded in the eighth character of the file name. The trace's
   `CSTART` rows are per compilation unit, so this is not bookkeeping.
4. **Spans sufficient to emit a `CERR` row** — a line and a position for
   every construct the tier could reject. **This is §6.3's ruling reaching
   back into the envelope**: the scoreboard is a trace emitter from day one
   (§4.4), a `CERR` record carries `line` and `position`, the User's Guide
   calls the line *"critical to the correct operation of the grading tool"*,
   and a span the ingester dropped is a verdict we cannot produce. A trace
   emitter is not something to retrofit, which is why this lands in the
   schema rather than in the scoreboard inch.

### 5.5 Inch 5 — `extractors/ada/extract.py`

Contract unchanged from the other lanes: never fails on valid Ada; anything
outside the pinned vocabulary becomes an `Unsupported` leaf carrying the node
class and ≤200 characters of source; output deterministic; hard errors exit
non-zero and say why. Cache key
`<stem>-<sha256(source)[:16]>-<sha256(extract.py)[:8]>-<profile_id>`, plus
the language version.

Anchored: the Python extractor is 1,913 lines, SV's 2,495, C's rides on
clang. libadalang does the hard work here, so the low end — but Ada's 316
node kinds against C's 45 argue against assuming C's cost.

### 5.6 Inch 6 — `LeanModels/Ada/{Ast,Json,Load}.lean`

The deep-embedded AST for the vocabulary inch 2 measures, and the ingester
that builds it at elaboration time. No semantics: the inch produces a Lean
TERM and nothing evaluates it. It lives in the version-NEUTRAL layer if and
only if inch 2's intersection census says it may — the same rule and the same
evidence standard the C lane's `Ast.lean`/`Json.lean`/`Load.lean` met.

The architecture decision [docs/c-tier-charter.md](c-tier-charter.md) §2 took
applies unchanged and is inherited rather than re-argued: **own semantic
model, shared world DISCIPLINE, shared code only where the Python tier is
already parametric.** `LeanModels/Ada/` is a SIBLING of `LeanModels/Python/`
and `LeanModels/C/`, never a client. The C charter's warning transfers
verbatim: **if an Ada interpreter ever lands with its own copy of `Run`, that
is a defect, not a design** — and by then there will be three consumers, so
the `LeanModels/Core/` move that §2.4 priced and deferred is likely to be
overdue rather than premature.

### 5.7 Inch 7 — `Report`'s specification round-tripped, with its `#guard`s

`Report`'s spec is the right first unit for the same reasons `pyfloordiv` was
right for C: it is small (a package spec with 15 subprogram declarations, one
subtype, one constant), it is the unit every executable test depends on so it
is on the critical path regardless, and it exercises the declarations an Ada
ingester must get right first — a package specification, subprogram
declarations with parameters and defaults, a subtype with a range constraint,
and a deferred-free constant.

The `#guard`s, fixed in advance by inch 4's schema so they are checkable
rather than post-hoc: the unit's kind and name, 15 subprogram declarations,
6 of them procedures and 9 functions, `File_Num`'s range `1 .. 5`,
`Generate_Event_Trace_File`'s type and default, the parameter names of
`Report.Test`, and zero unsupported nodes in the unit. Non-vacuity is checked
the way the C lane checks it: flip a count and Lean must report the failing
expression.

### 5.8 Inch 8 — THE PARAGRAPH MAP, and §6.1's ruling promoted it

[docs/family-architecture.md](family-architecture.md) §5.5 requires one
manifest per (language, edition) with a row per claimed CLAUSE.
**§6.1's ruling needs one row per PARAGRAPH**, and the artifact must be
*readable beside the ARM*. So:

    docs/ada-2022-paragraph-map.json     the rows
    docs/ada-2022-paragraph-map.md       the same rows, in the ARM's order

One row per paragraph the tier claims, keyed by the standard's own citation
form `<clause>(<para>)` — `4.1(9/3)`, exactly as the ARM cites itself —
carrying the paragraph's rule CATEGORY (§1.4's sixteen), `status`,
`declarations`, `gates` and `layer`. Coverage is
`stated / (stated + refused + out-of-tier)`, **generated and checked, never
hand-maintained**, and reportable per category — which is the number the
ruling actually wants, because "we cover 61% of Dynamic Semantics and 4% of
Bounded Errors" says something a single percentage cannot.

**Ada supplies the row skeleton for free and nobody else in the family
gets that.** `docs/ada-spec-census.json` already carries all 477 subclauses
with the standard's own numbers and titles, the paragraph COUNT of each, and
the rule categories each contains. The denominator is the standard's — 14,262
paragraphs, or 5,927 scoped to clauses 1-13 — and it is not ours to choose.

**Promoted from "someday" to inch 8 by the ruling**, and the reason it is
still inch 8 rather than inch 3 is unchanged: a map of stated rules needs
stated rules, and M1 states none. What M1 owes it is the *generator's input
format*, which the census already is.

### 5.9 What M1 deliberately does NOT decide

**Shorter than it was, because §6 closed four of the five things that used to
be here.** What remains open at M1:

* **The neutral/scoped split's contents** — `LeanModels/Ada/` versus
  `LeanModels/Ada/Ada2012/`. The directory LEVEL exists from commit one
  because §1.3's version pair is forced; what lives at each level is inch 2's
  intersection census to decide, and stating it before measuring it is the
  mistake §1.3 of the family charter exists to prevent.
* **Which of Annex M.2's 202 implementation-defined characteristics the
  corpus depends on** — inch 3 measures it.
* **The paragraph map's `status` vocabulary beyond §5.5's four values** —
  whether a membership-MATCH site (§6.2) needs a fifth. Do not invent it
  before a bounded-error paragraph is actually claimed.

---

## 6 THE RULINGS, and what is still open

**Thomas ruled the whole menu on 2026-08-22, the day the charter landed.**
The items below are recorded as decided rather than as asked, because the
charter's job was to present the fork and the fork is closed. §5 is updated
to the rulings; this section is the record of what was chosen and why it
changes the plan.

1. **THE ENDGAME — RULED: BOTH, and they are not alternatives.**

   > **The SPEC LADDER *and* differential grounding against a real
   > implementation.** The coverage instrument generalizes to ARM-PARAGRAPH
   > granularity and the map is *readable beside the ARM*; GNAT is the
   > behavior oracle.

   The charter had presented (a) the ACATS ladder, (b) the spec ladder and
   (c) a triangle. **(c) is dead (§6.5). (a) and (b) are the same program**,
   and the ruling is what makes that visible: a paragraph-granular coverage
   map is a claim about the STANDARD, and it is worthless without evidence,
   while ACATS tests are evidence that is worthless without a claim they
   support. Joined, the two are one artifact — **each ARM paragraph carries
   its status and the tests that witness it.**

   **Three things follow immediately, and §5 now carries all three.**

   * **The manifest goes to PARAGRAPH granularity, not clause.**
     [docs/family-architecture.md](family-architecture.md) §5.5 specifies one
     row per CLAUSE. Ada's ruling needs one row per **paragraph**, and the
     denominator is §1.2's **14,262** — or, scoped to the language, clauses
     1-13's **5,927**. This is a generalization of the family contract rather
     than a departure from it, and it is only affordable because the ARM
     numbers its own paragraphs and `docs/ada-spec-census.json` already
     carries every one of them with its rule category. **No other tier in the
     family could take this ruling**, and §5.8 is now an M1-adjacent inch
     rather than a someday.
   * **"Readable beside the ARM" is a requirement on the ARTIFACT.** The map
     is ordered by the standard's own numbering so a reader can hold the two
     side by side, paragraph for paragraph. That is a rendering obligation,
     and it is cheap only because the census is already keyed the ARM's way.
   * **GNAT is the behavior oracle**, which is
     [docs/family-architecture.md](family-architecture.md) §4.2's precedence
     rule taken at face value: the SPEC is the target, the IMPLEMENTATION is
     the oracle, a divergence between them is a FINDING with both citations
     and blocks neither side. **There was no Ada compiler on this host at
     charter time (§4.2), so censusing GNAT's availability and
     installability is an M1 item** — §5.2.

2. **THE BOUNDED-ERROR VERDICT — MATCH-BY-MEMBERSHIP, adopted.** §1.5.1's
   analysis stands and the recommendation is taken as family law unless
   Thomas overrides: at a bounded-error site the DIVERGE test is **membership
   in the spec-enumerated permitted set**, not equality, because two
   conforming implementations may legitimately produce different members.
   This answers [docs/family-architecture.md](family-architecture.md) §4.3's
   standing question — **no fifth REFUSE cause is needed**; what was missing
   was a verdict, one level up from the refusal taxonomy. The obligations
   that come with adopting it: the site carries its permitted set, and MATCH
   stops meaning "equals the oracle" there, so **membership-MATCHes are
   reported as their own column** or the headline number quietly weakens.
   Scale, so the cost is known: 104 paragraphs over 40 subclauses; 57 over 16
   in clauses 1-13.

3. **THE GRADER — RULED: the ACAA's own `GRADE`, via the event-trace CSV, and
   the scoreboard is a trace emitter from day one.** This is the tier's
   defining grounding move and it is stated in full at **§4.4** rather than
   here. In one line: **we do not decide our own verdicts.** The B-class
   grading rules §2.3 measured — location-only, `POSSIBLE`/`OPTIONAL`
   disjunctions, 7,568 `-- OK` false-positive guards — are the ACAA's tool's
   problem, not ours, and self-generous scoring becomes structurally
   impossible rather than merely discouraged. Its cost is that the toolchain
   is load-bearing twice (frontend *and* scorer), which is why §5.2 is the
   critical path.

4. **VENDORED VERSUS FETCHED — FETCH-PINNED, implemented now.** It is the
   default and the uniform family policy (§2.5), so nothing waits on a
   further word. Recorded for completeness: **vendoring stays a
   one-command option and Ada is the one tier where it would be
   unambiguously legal** — every one of the 4,945 Ada files carries a grant
   of unlimited rights (§2.5), so the c-testsuite trap that forced the policy
   elsewhere does not exist here. The reasons to fetch anyway are uniformity,
   keeping a 41 MB corpus out of the repository, and `--compare` making
   staleness mechanically detectable.

5. **THE ADA SUNFISH TWIN — RULED: NO.** Dead, and removed from the endgame
   menu. The driver artifact is the corpus (§4.3(a)), consistent with the
   family driver policy. §4.3(b) records the consequence rather than the
   option: **this tier will never have a second independent model of the same
   program**, and the ACAA's grader (§4.4) is the structural defense that
   replaces it.

**STILL OPEN — two amendments back to
[docs/family-architecture.md](family-architecture.md)**, found by this census
and not the Ada lane's to make:

* **§1.2's `oracle` column is one column short for Ada.** For every other
  spec-mirror tier the oracle is an implementation. Ada has a third
  authority — an **official suite** with published grading rules and a
  shipped grading tool, owned by neither the standards body nor an
  implementer — so §4.2's precedence rule wants one more clause: *the SPEC
  is the target, the IMPLEMENTATION is the oracle for behavior, and the
  SUITE OWNER is the authority for the expected VERDICT* (§0.1, §2.4). The
  ruling in §6.1 makes this concrete rather than theoretical: Ada now has an
  implementation oracle (GNAT) AND a suite owner (the ACAA) in the same
  pipeline, and they answer different questions.
* **§4.3's Ada row is now fillable**, and §1.5 fills it. The row's
  prediction that a fifth REFUSE cause would show here is answered in
  §1.5.1 — it does not, and what shows instead is one level up. §6.2 adopts
  the answer.
* **§5.5's manifest is one row per CLAUSE, and §6.1's ruling needs one row
  per PARAGRAPH.** Stated as a generalization the Ada lane is taking, not a
  departure it is making unilaterally: `clause` becomes `<clause>(<para>)`,
  which is the ARM's own citation form, and every other tier's rows are
  unaffected because a clause-granular row is the degenerate case.

*(The `∀`-resolution ruling the founding dispatch cited by name is
[docs/family-architecture.md](family-architecture.md) §3.6, which landed
three commits before this charter did. §1.5.3 cites it. This item stood open
in draft as "not in this repository" and is closed by the landing rather than
by an answer, which is worth one line so the next lane does not go
looking.)*

---

## 7 WHAT LANDED WITH THIS CHARTER

* `harness/ada_spec_census.py` — the ARM instrument, with `--compare` and
  `--self-test`, validated against the document's own table of contents.
* `docs/ada-spec-census.json` — the Ada 2022 ARM, machine-readable: 28
  clauses, 477 subclauses, 14,262 paragraphs, per-category counts, per-file
  sha256.
* `harness/ada_suite_census.py` — the ACATS instrument, with `--compare` and
  `--self-test`, validated against the suite's own file manifest and against
  the User's Guide's own table.
* `docs/ada-suite-census.json` — ACATS 4.2, machine-readable: 4,188 tests,
  per-test class, naming, clause, markings, Report calls, `with`s, features.
  The committed file omits four per-test fields the summary already carries
  in full (the raw reserved-word lists and the licence-audit counts) and
  drops test-local `with`s and all-zero marking rows, so the artifact stays
  in the size range of its siblings in `docs/`; `--full` restores them, and
  the summary is computed BEFORE the trim so no number here depends on which
  mode produced the file.
* `docs/ada-charter.md` — this document.
* `docs/backlog.md` §L63 — the record.

**Landed after Thomas's rulings, as M1 inch 2's first half (§5.2.1):**

* `harness/ada_toolchain_census.py` — the toolchain probe, with `--verify`,
  which drives §4.4's ruled grounding loop end to end and asserts the two
  NEGATIVE grader cases. `--self-test` covers the probe's own decision logic.
* `docs/ada-toolchain-census.json` — this host, measured: GNAT 16.1.0 and
  gprbuild 26.0.1 present via Alire 2.1.1, `libadalang` not yet importable,
  and the unmet need named.

**No Lean, and no change to any existing file** other than `docs/backlog.md`.
Both instruments meet
[docs/family-architecture.md](family-architecture.md) §5.4's contract —
`harness/<lang>_<subject>_census.py`, `docs/<lang>-<subject>-census.json`,
sorted, `--compare`, every refusal path run, double-run byte-identical, and
each stamps the frontend it used (both stamp *none*, honestly: one reads the
ARM's own plain text, the other is a lexical scanner) and the edition token it
DERIVED from the artifact rather than asserted (`Ada2022` from the ARM's own
front matter, `Ada2012` from the suite's own `ACATS_Version` constant).
Neither is wired into CI: both corpora are out-of-tree, and §5.4 is explicit
that a gate which is a permanent SKIP is a check pretending.

**What was verified, and what was NOT — stated plainly, because a charter
that claimed a green it had not seen would fail its own covenant in its last
paragraph.** `python3 tools/docs_check.py` is green — unchanged. All three instruments pass `--self-test`,
the two census instruments produce byte-identical output on a double run, and
every refusal path in all three was executed rather than described — including
`--verify`'s nine checks against the real ACATS delivery, which pass.

`lake build`, `harness/diff_test.py` and `harness/script_corpus.py` were
**NOT re-run**, and the reason is a machine-wide build-lock protocol in force
since 2026-08-22: concurrent Lean builds were taking the machine down. At
landing time the lock was HELD and three `lake` processes were already
running. This landing changes only `docs/`, `harness/*.py` and this file —
**no Lean, and no Python that any Lean or any existing harness imports** — so
the Lean third of the triad has nothing to report that §L58's run did not
already report. Re-running it here would have meant a full rebuild of a
freshly-checked-out tree, which is the single most expensive build available
and the exact behavior the protocol exists to stop. **The next Ada-lane
landing that touches Lean owes a full triad under the lock**, and inch 2
(§5.2) is the first one that will — taken under the protocol's amended form
(`rm -rf` release inside a failure-reporting trap, `nice -n 10 lake build`
with **no** `-j` flag, which is an argument error on this toolchain and
masquerades as a build failure).
