# The Go tier: FOUNDING CHARTER

**Status: the workstream's founding document.** Thomas chartered it on
2026-08-22, and gave the reason in one line: *"I like Go — short spec,
and it's a common language for concurrency, which is itself interesting
to formalize."* Both halves of that sentence are claims, and this
charter's first job is to **measure** them rather than repeat them.

It follows `docs/c-tier-charter.md`'s template exactly — census the
surface with an instrument that lands beside it, take the architecture
decisions the census forces, price nothing that was not measured, and
plan the first milestone. **It builds no semantics** and recommends no
endgame. §9 lists what is Thomas's to answer.

**The two claims, answered up front, because both survived contact with
a measurement and one of them is stronger than it sounded:**

| the claim | the measurement | verdict |
| --- | --- | --- |
| "short spec" | the Go spec is **39,149 words** in **19** top-level sections. The C23 draft (WG14 N3220) is **309,405** words. | **TRUE, by 7.90×** |
| "common language for concurrency" | the Go standard library alone carries **1,074 `go` statements, 987 sends, 1,706 channel types and 458 `select`s** over 5,419 files | **TRUE** |
| *(unclaimed, and the census's own headline)* | Go's entire AST vocabulary is **56 node types**, of which the whole 1.98-million-line standard library exercises **52** — the other four are parse-error placeholders and one deprecated node | **the vocabulary is CLOSED, not merely small** |
| *(unclaimed, and the one that reshapes the refusal taxonomy)* | the string **"undefined" appears ZERO times in the Go specification**. C23 uses it 284 times and enumerates 221 undefined-behavior circumstances in Annex J.2. | **Go has no UB class to refuse** |

---

## 1 THE SPEC MAP — two co-equal documents

The C tier mirrors one document. **The Go tier must mirror two**, and
they are co-equal rather than primary-and-appendix, because the memory
model is not a commentary on the spec: it *delegates to* the spec for
its intra-goroutine order and the spec *declines to define* anything
about inter-goroutine visibility. Neither is complete without the other.

### 1.1 The instrument, and the pin

`harness/go/construct_census.go`, landed with this charter, run through
`harness/go/census.sh`:

```
harness/go/census.sh --root <dir> <path>... -o docs/go-construct-census.json
harness/go/census.sh --root <dir> <path>... --compare docs/go-construct-census.json
```

It walks `go/parser` + `go/ast` — the language's own front end, the same
packages the compiler's type checker is built beside — and emits sorted,
deterministic JSON. **A double run is byte-identical (verified), and
`--compare` against the committed JSON exits 0 (verified).**

**Every refusal path that CAN fire was RUN, not admired — and the one
that cannot is labelled as such rather than counted.** Measured exit
codes: a missing path refuses **2**; a directory with no `.go` file
refuses **2**; a source that does not PARSE refuses **3** (`go/parser`,
exactly like clang, returns a partial tree alongside its error, and a
census of a partial tree is a plausible-looking wrong answer); an
agreeing `--compare` exits **0** and a differing one exits **5**.

**The zero-nodes guard (exit 4) is UNREACHABLE today, and the charter
says so rather than claiming a fifth run.** It is the direct port of the
defect `docs/c-tier-charter.md` §1.1 records — the C instrument censused
a program that does not compile and exited 0 — but the Go analogue
cannot currently fire: `ast.Inspect` over a successfully parsed file
always visits at least the `File` and its package `Ident`, so the node
count is never zero. It is kept as a defensive invariant precisely
because **the thing that made it reachable in C was a source FILTER** —
clang's sticky `loc.file`, without which the census measured libc's
headers rather than the corpus. The moment this instrument grows any
comparable filter, the guard becomes live. Recording an unreachable
branch as "a refusal path we ran" would have been exactly the small
overclaim this repository treats as a defect.

**Two `go run` traps were found by running them, and together they are
why the documented invocation is a BUILD.** They are recorded here
because either one would have silently destroyed the exit-code
convention this project runs on:

1. **`go run` does not propagate the program's exit code.** Measured: a
   program that calls `os.Exit(3)` makes `go run` print `exit status 3`
   on stderr and itself exit **1**. The built binary exits 3. This
   instrument carries its entire refusal taxonomy in its exit code, so
   under `go run` all of "no such path", "does not parse", "zero nodes"
   and "`--compare` differs" collapse to 1 — and the project's standing
   invariant that **3 and 4 are never agreement** would be silently
   unenforceable.
2. **`go run a.go b.go` treats both files as SOURCES of one package.**
   Since this instrument's arguments are themselves `.go` paths, the
   invocation is ambiguous unless a non-`.go` flag comes first.

`harness/go/census.sh` does the build and forwards the exit code. Like
its C sibling, the instrument is **deliberately NOT wired into
`tools/ci.sh`**: it requires a Go toolchain that a stock runner does not
have, so a gate would be a permanent SKIP pretending to be a check. When
the lane owns a corpus in-tree, `maybe <name> <required-file> <cmd>` is
where it belongs.

**The pin.** Everything below is measured against `go version go1.25.6
darwin/arm64`, and the instrument stamps the toolchain **FAMILY**
(`go1.25`), never the point release — the same correction
`docs/backlog.md` records twice for clang.

### 1.2 Document one — the Go Programming Language Specification

Both documents ship **inside the Go distribution**, at
`$GOROOT/doc/go_spec.html` and `$GOROOT/doc/go_mem.html`. That is where
this census took them, and §1.4 explains why that choice is
load-bearing rather than convenient.

The spec carries its version in a metadata comment. Verbatim:

> `"Subtitle": "Language version go1.25 (Aug 12, 2025)"`

**Measured structure: 19 `h2` sections, 108 `h3`, 34 `h4` — 161
headings, 39,149 words, 223,652 bytes of extracted text.**

| # | section | words | # | section | words |
| ---: | --- | ---: | ---: | --- | ---: |
| 1 | Introduction | 76 | 11 | **Expressions** | **12,694** |
| 2 | Notation | 239 | 12 | Statements | 5,867 |
| 3 | Source code representation | 288 | 13 | Built-in functions | 2,745 |
| 4 | Lexical elements | 2,103 | 14 | Packages | 704 |
| 5 | Constants | 482 | 15 | Program initialization and execution | 1,158 |
| 6 | Variables | 297 | 16 | Errors | 53 |
| 7 | Types | 4,215 | 17 | Run-time panics | 69 |
| 8 | Properties of types and values | 1,561 | 18 | System considerations | 944 |
| 9 | Blocks | 113 | 19 | **Appendix** | 1,147 |
| 10 | Declarations and scope | 4,041 | | | |

Two structural facts a mirroring plan must not miss. **Expressions alone
is 32.4% of the document** — the tier's centre of gravity is expression
evaluation, not statements and not concurrency. And **section 19 is the
spec's own per-version change log**, ten version headings covering Go
1.9 through Go 1.24; the spec self-documents its version deltas, which
is a gift to §3 and to the family-architecture lane.

**The grammar: 166 EBNF productions**, in 62 blocks marked
`<pre class="ebnf">`. The count is the number of lines matching an
LHS-name-then-`=` at column 0 across those blocks; the 18 remaining
non-blank lines were each inspected and are wrapped alternation tails,
not missed productions. **All 166 LHS names are distinct** — a repeated
LHS would have signalled either a split production or a counting error,
and there are none, which independently validates the method. Excluded
by design: the 29 `<pre class="grammar">` blocks, which are
non-normative listings (the operator-precedence table, the keyword
list), plus the 8-production meta-grammar of the EBNF notation itself.

**The hedge census, and it is the finding that reshapes the whole
refusal taxonomy:**

| phrase | count | | phrase | count |
| --- | ---: | --- | --- | ---: |
| implementation restriction(s) | 12 | | may vary | 3 |
| implementation-specific | 6 | | not guaranteed / no guarantee | 2 |
| implementation-dependent | 3 | | pseudo-random | 1 |
| implementation-defined | 2 | | arbitrary / arbitrarily | 18 |
| unspecified | 4 | | nondeterministic | 0 |
| not specified | 7 | | **undefined** | **0** |

**"undefined" appears zero times in the Go specification.** Verified
twice, independently: a section-wise census returned 0, and a raw
case-insensitive grep over the unprocessed HTML also returned 0. The
contrast was measured on the same instrument's terms: the C23 draft uses
"undefined" **284** times, and **Annex J.2 enumerates exactly 221
numbered undefined-behavior circumstances** (1–221, contiguous, no
gaps).

The 12 "implementation restriction" hedges are worth naming separately,
because their SHAPE is different: they are permissions for an
implementation to **reject** a program, not permissions to misbehave
while running one. That is a categorically different obligation from C's
UB and it lands in a different refusal class (§2.5).

### 1.3 Document two — the Go Memory Model

Verbatim from its metadata comment:

> `"Subtitle": "Version of June 6, 2022"`

This is the post-2022 happens-before/DRF formulation, and the census
confirms it on five independent grounds rather than by the date alone:
the document explicitly grounds itself in *"the approach presented by
Hans-J. Boehm and Sarita V. Adve in 'Foundations of the C++ Concurrency
Memory Model', published in PLDI 2008"*; it carries two whole sections
the older text lacked (the formal "Memory Model" development and
"Implementation Restrictions for Programs Containing Data Races"); the
three-relation vocabulary is present by name (`synchronized before` ×19,
`happens before` ×12, `sequenced before` ×6, `DRF-SC` ×3); and the
per-primitive rules are phrased in terms of *synchronized before*, which
is the post-2022 phrasing. **The published document still carries the
same June 6, 2022 date today** — it has not been revised since, which
makes it an unusually stable mirroring target.

**Measured: 7 `h2` sections, 11 `h3`, 3,847 words.** The spec is
**10.18×** its size.

| § | section | words | | § | section | words |
| --- | --- | ---: | --- | --- | --- | ---: |
| 1 | Introduction (+ Advice, Informal Overview) | 378 | | 4.4 | **Channel communication** | **441** |
| 2 | **Memory Model** | **760** | | 4.5 | Locks | 200 |
| 3 | Implementation Restrictions … Data Races | 323 | | 4.6 | Once | 129 |
| 4 | Synchronization (container) | 0 | | 4.7 | Atomic Values | 76 |
| 4.1 | Initialization | 57 | | 4.8 | Finalizers | 38 |
| 4.2 | Goroutine creation | 57 | | 4.9 | Additional Mechanisms | 47 |
| 4.3 | Goroutine destruction | 99 | | 5 | Incorrect synchronization | 383 |
| | | | | 6 | **Incorrect compilation** | **780** |
| | | | | 7 | Conclusion | 41 |

**A structural gift for a mirroring project: the document marks its
normative rules in the markup.** There are exactly **11
`<p class="rule">` paragraphs**, each one an ordering rule. But the
index is **useful and incomplete**, and the charter records the gap
rather than relying on it: Goroutine destruction, Atomic Values and
Finalizers all state normative content in *plain* paragraphs and carry
no `class="rule"`. A mirror that enumerated only the marked 11 would
silently drop three obligations.

**The three relations**, all defined by name:

* **sequenced before** — *"the partial order requirements set out by the
  Go language specification for Go's control flow constructs as well as
  the order of evaluation for expressions."* **This is a delegation to
  the other document**, and it is the precise reason the two are
  co-equal: the memory model cannot be mirrored without mirroring the
  spec's "Order of evaluation" section, which is itself the section
  carrying four of the spec's seven "not specified" hedges.
* **synchronized before** — a partial order on synchronizing operations
  derived from the read-from map `W`.
* **happens before** — *"the transitive closure of the union of the
  sequenced before and synchronized before relations."*

Three numbered **Requirements** govern executions; two **data race**
definitions (read-write and write-write) are given separately; and
**DRF-SC** is stated as a theorem with its proof delegated: *"The proof
is the same as Section 7 of Boehm and Adve's paper cited above."*

**Operation classification, which a mirror must get exactly right:**
read-like is *"read, atomic read, mutex lock, and channel receive"*;
write-like is *"write, atomic write, mutex unlock, channel send, and
channel close"*; compare-and-swap is both. So **channel close is
write-like**, and **mutex lock is read-like while unlock is
write-like**.

**The four channel rules — the tier's whole concurrency core**, verbatim:

1. *"A send on a channel is synchronized before the completion of the
   corresponding receive from that channel."*
2. *"The closing of a channel is synchronized before a receive that
   returns a zero value because the channel is closed."*
3. *"A receive from an unbuffered channel is synchronized before the
   completion of the corresponding send on that channel."*
4. *"The kth receive from a channel with capacity C is synchronized
   before the completion of the k+Cth send on that channel."*

Rules 1 and 3 are duals, and 3 is what makes an unbuffered channel a
rendezvous rather than a one-way edge. **Rule 4 subsumes both** — the
document says so, and at C=0 it degenerates to the rendezvous. Rule 2's
scope is narrow and exact: the edge exists only to receives that observe
*closure*, not to receives that drain buffered values.

**Two obligations that are easy to miss and both are liveness-shaped:**

* **Goroutine exit synchronizes with nothing.** *"The exit of a
  goroutine is not guaranteed to be synchronized before any event in the
  program."* With the consequence spelled out in the document itself:
  *"In fact, an aggressive compiler might delete the entire go
  statement."*
* **Unsynchronized spin loops need not terminate.** *"there is no
  guarantee that the write to done will ever be observed by main, since
  there are no synchronization events between the two threads. The loop
  in main is not guaranteed to finish."*

**"Incorrect compilation" is the longest section in the document (780
words), and it is the one with no C analogue.** It binds *implementations*,
not programs: *"a compiler must not introduce writes that do not exist in
the original program, it must not allow a single read to observe multiple
values, and it must not allow a single write to write multiple values."*
Six constraints follow, including a flat prohibition on assuming loops
terminate and on assuming called functions return — and the section
closes by naming the stakes: *"Note that all these optimizations are
permitted in C/C++ compilers: a Go compiler sharing a back end with a
C/C++ compiler must take care to disable optimizations that are invalid
for Go."*

**One scoping fact with immediate consequences for rung 0.** §4.9
"Additional Mechanisms" **delegates `sync.Cond`, `sync.Map`, `sync.Pool`
and `sync.WaitGroup` to their package documentation** and states no rule
for them. They are outside the memory model. This charter's driver
fixture was rewritten because of that measurement (§7.1).

### 1.4 Citation and license — verified per document, and the two copies differ

The family law is cite-and-paraphrase, and the licenses were checked
rather than assumed. **The result is that the same text carries two
different licenses depending on which copy you take**, which is exactly
the kind of trap `docs/c23-goal.md` §2 records for c-testsuite.

| artifact | license | how verified |
| --- | --- | --- |
| spec + memory model, **as shipped in the source distribution** | **BSD-3-Clause** | neither file carries any notice — grepped both for `licen`/`copyright`/`creative commons`, zero hits — so both are covered by the repository's root `LICENSE`, read locally |
| spec + memory model, **as published on the website** | **CC-BY-4.0** | the site's Copyright page, body text extracted: *"Except as noted, the contents of this site are licensed under the Creative Commons Attribution 4.0 License, and code is licensed under a BSD license."* |
| Go source repository code | **BSD-3-Clause** + a separate patent grant | `LICENSE` (1,453 bytes, opens *"Copyright 2009 The Go Authors."*, three clauses) and `PATENTS` (1,303 bytes, heading *"Additional IP Rights Grant (Patents)"*) |
| Go blog posts | CC-BY-4.0 as published; BSD-3-Clause in the website repo | same dual situation, checked the same two ways |

**Ruling: take the in-tree copies.** From the source distribution both
documents are unambiguously BSD-3-Clause under a single well-understood
instrument; scraping the website copy would import CC-BY-4.0 attribution
obligations for no gain. This census did exactly that, so the attribution
line for derived Lean artifacts is **BSD-3-Clause, "Copyright 2009 The Go
Authors"**, and the separate patent grant is noted because BSD-3-Clause
alone does not describe Go's IP posture.

A packaging note worth recording so the next lane does not repeat the
search: **there is no `LICENSE` file inside `$GOROOT` itself** in a
Homebrew installation — it is relocated one level up to the keg root. In
an upstream source tarball it is at `$GOROOT/LICENSE`.

### 1.5 The size comparison, measured on both ends

| | Go spec | Go memory model | C23 draft (N3220) |
| --- | ---: | ---: | ---: |
| words | 39,149 | 3,847 | **309,405** |
| text bytes | 223,652 | 22,738 | 1,991,949 |
| pages | — (HTML) | — | 759 |

**C23 is 7.90× the Go spec in words, and 7.20× the spec and memory model
combined.** Thomas's "short spec" is correct and now has a number.

One further anchor, because word count is not effort: the Go standard
library's own implementation of what the spec describes —
`src/go/{types,parser,scanner,ast,constant,token}`, non-test files only —
is **35,319 lines**. Roughly 1:1 with the spec's word count in units,
and the closest thing to a measured spec-to-executable-mirror price tag
available locally.

---

## 2 THE CONCURRENCY TAXONOMY

This is the section the workstream exists for. The census sorts Go's
nondeterminism into **four disjoint classes**, and they are disjoint
because each one needs a *different* treatment in the verdict system.
Pooling any two of them would make the scoreboard unreadable — the same
argument `docs/c23-goal.md` §3.1 makes for REFUSE's three causes.

**The headline, measured: the concurrency core of the Go spec is 1,479
words — 3.8% of the document, across six sections — and it carries
exactly ONE hedge between them.** Channel types, Send statements,
Receive operator, Go statements and Close contain **zero** hedges of any
kind. The single hedge is `pseudo-random`, in Select statements. Go's
channel/goroutine surface is fully determinized except for the select
choice, and that is a much smaller nondeterminism budget than the
folklore suggests.

| class | instance | what the spec says | treatment |
| --- | --- | --- | --- |
| **A. ∀-schedule** | goroutine interleaving | nothing — no scheduler is specified at all | correct = correct under *every* schedule (§2.1) |
| **B. specified-random** | `select` among ready cases | *"a uniform pseudo-random selection"* | a **specified distribution**, not a free choice (§2.2) |
| **C. ∀-order, runtime-enforced** | map iteration | *"not specified"* | ∀-order in the model; and the runtime is **narrower than ∀** (§2.3) |
| **D. bounded outcomes** | data races | a value bound + an always-available halt | **not UB**; needs the Ada-style class (§2.4) |

### 2.1 Class A — goroutine scheduling is the ∀-schedule domain

The Go specification **specifies no scheduler**. It says a `go`
statement starts a goroutine, that argument evaluation *"happens in the
calling goroutine"*, and that *"when that function invocation returns,
the program exits. It does not wait for other (non-`main`) goroutines to
complete."* Beyond that, interleaving is unconstrained.

**This is `docs/c-semantics-design.md` §4.4's ruling, generalized.** The
C tier faced the same shape at Annex J.1's unspecified evaluation order
and ruled: *fix a canonical order as the EXECUTION order, and require a
static census that the order is unobservable; refuse where the census
cannot show it.* The reasons given there transfer without a word
changed — everything downstream needs a **function**, not a relation: the
outcome type has four constructors, `fuelMono` is a monotonicity
statement about a function, `#py_check` requires kernel-reducible
structural recursion, and the batch protocol emits exactly one output
line per job in job order. **An exploring semantics produces a SET of
outcomes and would change the shape of all five artifacts at once.**

So the Go tier's ruling, stated in the C tier's own terms:

> **Execute under a canonical schedule. Prove the observable
> schedule-INVARIANT, or refuse and name the site.**

The generalization is not free and the charter is explicit about the one
place it costs more than C's. In C the quantified object is an
*evaluation order within one full expression* — a bounded, syntactic,
statically-censusable thing, which is why the C lane could measure "1169
full expressions, 73 candidates, 20 left for the may-alias check". **A
schedule is not syntactically bounded.** There is no finite list of
schedules to quantify over and no expression to point at. What replaces
the syntactic census is the memory model itself: DRF-SC says a
data-race-free program's outcomes are exactly the sequentially
consistent interleavings, so *for race-free programs* the ∀-schedule
obligation reduces to an argument about SC interleavings — and for
programs whose observable is invariant under commutation (§7.1's
fixture), to nothing at all. **The census that Go needs in place of C's
may-alias check is a RACE-FREEDOM census.** That is the single largest
piece of work this charter identifies and it is not priced here.

### 2.2 Class B — `select` is SPECIFIED-random, which is not the same as free

The spec's exact sentence:

> *"If one or more of the communications can proceed, a single one that
> can proceed is chosen via a uniform pseudo-random selection."*

Three words in that sentence each do work, and a model that blurs any of
them is wrong:

* **"uniform"** — the *distribution* is specified. This is not "some
  choice"; it is a named measure.
* **"pseudo-random"** — so a deterministic-but-fair round-robin
  scheduler does **not** satisfy the spec. This is stronger than
  "implementation-defined" and stronger than "arbitrary", both of which
  the spec uses elsewhere and deliberately did not use here.
* **"if one or more … can proceed"** — the choice is only among the
  *ready* cases. Readiness is fully determined; only the tie-break is
  not.

And the nondeterminism is tightly fenced. Everything else in a `select`
is determinized before the choice happens: the channel operands and
send values are *"evaluated exactly once, in source order, upon entering
the 'select' statement"*, and *"any side effects in that evaluation will
occur irrespective of which (if any) communication operation is selected
to proceed."*

**How should the verdict system treat a specified distribution? This is
a genuine open question and the charter does not settle it** — it is
§9's decision 2. The three candidate treatments, with what each costs:

1. **Treat it as class A** (∀-choice): correct = correct under every
   ready case. **Sound, and it throws away information** — it cannot
   distinguish an implementation that always picks the first ready case
   (which the spec forbids) from a conforming one. It is also the
   cheapest, and it composes with §2.1 for free.
2. **Model the distribution**, and score statistically. This is the only
   treatment that can *detect* a non-uniform implementation, and it
   breaks the project's deterministic batch protocol: one output line
   per job stops being well-defined.
3. **Parameterize on a choice oracle** — the schedule parameter of §6.2
   carries the select choices too, and uniformity becomes a *side
   condition* stated about the oracle rather than a property the
   interpreter samples.

**The charter's own reading, offered as a recommendation and not a
ruling: (3), degenerating to (1) for verdicts.** It keeps the
interpreter a function, it keeps the specified distribution *stated*
rather than silently weakened to "arbitrary", and it makes uniformity a
theorem-shaped obligation on the oracle instead of a statistical test
this project has no machinery for. The honest cost of (3) is that the
tier will never *catch* a non-uniform `select` implementation, and the
charter says so rather than implying coverage it does not have.

**Measured, so the shape of the obligation is known before it is
built:** across the standard library's 458 `select` statements, **387
have exactly two cases**, 39 have three, 15 have four, 4 have five, 2
have six, and **10 have zero** (`select {}`, which the spec notes blocks
forever). 190 carry a `default`. So the uniform choice is over a set of
size 2 in 84% of real occurrences, and the tail is short.

### 2.3 Class C — map iteration, where the runtime is NARROWER than the spec

The spec's exact sentence:

> *"The iteration order over maps is not specified and is not guaranteed
> to be the same from one iteration to the next."*

Read the wording precisely: **"not specified"**, not "undefined", and
with **no mention of randomization**. An implementation returning
insertion order forever would conform.

**Then it was measured, because the folklore says Go "randomizes" map
order and folklore is not a datum.** 20,000 iterations of the same live
map, for maps of 8, 40 and 200 keys, repeated across three process runs:

```
n=8    trials=20000  distinct orders=8    non-rotations=0
n=40   trials=20000  distinct orders=40   non-rotations=0
n=200  trials=20000  distinct orders=200  non-rotations=0
```

**The runtime randomizes, but it produces a uniform random ROTATION of a
per-process base permutation — not a uniform draw from all n!
permutations.** For an n-element map the observable order set has
**exactly n members**, each with probability 1/n. For n=8 that is 8 of
40,320 possible permutations: **0.02% of the permutation space.** The
8-key distribution was flat (counts 2469…2549 against an expected 2500),
and the base permutation differed between processes, consistent with a
per-process hash seed.

**This is the horizontal datum the brief asked for, and it points BOTH
ways, which is what makes it worth having:**

* The spec is **weaker** than the runtime: it permits a constant order;
  the runtime does not deliver one.
* The runtime is **weaker than it looks**: it is not a uniform shuffle.

So a model that axiomatized *"any permutation"* would be **sound but
loose**, and a model that axiomatized *"uniform over permutations"*
would be **unsound against the measured implementation**. The
spec-faithful choice is ∀-order — an arbitrary order satisfying the
spec's insertion/removal clauses — with the rotation structure recorded
as an **implementation observation, never a guarantee**. Keeping that
distinction visible is precisely what the spec-mirroring discipline is
for, and this is the cleanest example of it the family has yet produced.

The spec's two further clauses are part of the obligation and are easy
to drop: *"If a map entry that has not yet been reached is removed
during iteration, the corresponding iteration value will not be
produced. If a map entry is created during iteration, that entry may be
produced during the iteration or may be skipped."*

### 2.4 Class D — DATA RACES ARE NOT UNDEFINED BEHAVIOR

The brief asked whether Go's races map to the UB-refused class or need
the Ada-style bounded-outcomes class. **Measured answer: bounded
outcomes — and the bound is SIZE-STRATIFIED, which is the part that
would be easy to get wrong in either direction.**

The memory model names C++ and declines it, in its own words:

> *"These implementation constraints make Go more like Java or
> JavaScript, in that most races have a limited number of outcomes, and
> less like C and C++, where the meaning of any program with a race is
> entirely undefined, and the compiler may do anything at all."*

**The bound, for word-sized-or-smaller locations**, verbatim:

> *"A read r of a memory location x holding a value that is not larger
> than a machine word must observe some write w such that r does not
> happen before w and there is no write w' such that w happens before w'
> and w' happens before r. That is, each read must observe a value
> written by a preceding or concurrent write."*

and immediately after:

> *"Additionally, observation of acausal and 'out of thin air' writes is
> disallowed."*

The OOTA prohibition is **stronger than the C++ model Go otherwise
follows**, where out-of-thin-air is discouraged but not cleanly
prohibited.

**The always-available alternative**, and its modality matters:

> *"Any implementation can, upon detecting a data race, report the race
> and halt execution of the program. Implementations using
> ThreadSanitizer (accessed with 'go build -race') do exactly this."*

Note **"can" / "may", never "must"**. Race-detect-and-halt is a
*permitted* implementation behavior, not an obligation, so a faithful
model treats it as a nondeterministic choice available at every racy
step — never as guaranteed detection.

**And the sharp edge, which the charter refuses to soften**, verbatim:

> *"When the values depend on the consistency of internal (pointer,
> length) or (pointer, type) pairs, as can be the case for interface
> values, maps, slices, and strings in most Go implementations, such
> races can in turn lead to arbitrary memory corruption."*

So the honest three-way model is:

| location size | outcome set for a racy read |
| --- | --- |
| ≤ one machine word | `{halt-with-race-report}` ∪ `{bounded set of actually-written values}`, no OOTA |
| > one machine word (arrays, structs, complex, interface, map, slice, string) | `{halt-with-race-report}` ∪ `{per-word interleavings in unspecified order, possibly memory-UNSAFE}` |

**A Lean mirror that claimed "Go races are always memory-safe" would be
wrong against the text**, and this charter records that before anyone
builds one. Only the multiword case resembles C's escape hatch, and even
there the document says larger reads are *"encouraged but not required"*
to meet the word-sized semantics — a preference, not a licence to do
anything at all.

### 2.5 What this does to the refusal taxonomy

`docs/c23-goal.md` §3.1 fixes three disjoint causes of REFUSE: (1)
out-of-tier construct, (2) UB refused loudly, (3) unmodeled library.
**Cause (2) has no Go instance.** There is no undefined behavior in the
Go specification to refuse — zero occurrences of the word, and the
race case is bounded rather than undefined.

That is a real structural difference from the C tier and it cuts both
ways, so both are stated:

* **Cheaper**: the C tier arms eleven UB classes at v0, two of which no
  sanitizer on the pinned host can detect. The Go tier arms **none**.
* **Not cheaper**: what replaces UB is *bounded nondeterminism*, and a
  bounded set is harder to score against than a refusal. A refusal is one
  outcome and a verdict; a bounded set requires the verdict system to ask
  "was the oracle's observed outcome IN the model's set?" — a different
  question from "did they agree", and one the batch protocol does not
  currently ask.

**Both of the things this needs already exist at the family level, and
the charter CITES them rather than inventing parallel machinery.** An
earlier draft of this section proposed a fourth REFUSE cause and a new
verdict `ADMITS`; both were superseded while this document was being
written, and the superseding versions are better. `docs/family-architecture.md`
§5.2 already carries **cause 4, `order-dependence`** — *"the language
admits several orders and the model cannot show the observable invariant
under all of them"* — which is precisely the schedule-dependence of §2.1,
arrived at from C's 20 residual may-alias sites and Python's hash-order
refusals. Nothing new is needed here.

And §5.1 carries the membership rule, which is the better answer to the
bounded-set problem than a new verdict name:

> **At a site where the language enumerates several permitted outcomes,
> MATCH is MEMBERSHIP in that set, not equality with one oracle's
> observable. Two conforming implementations may disagree there and both
> be right.**

The verdict vocabulary is therefore **unchanged** — the permitted set is
a *per-site datum* the tier carries, and equality is the degenerate
singleton case, so every existing site stays correct. That ruling names
this tier explicitly, and the charter records the sentence rather than
paraphrasing it: *"It is exactly what Go's racy programs need: Go bounds
what a racy program may observe instead of surrendering to UB the way C
does, so a racy Go program is a membership site and not a refusal."*

**The contrast in one line, which is the whole of §2.4 compressed:**

> **racy C = REFUSE(`undefined`). racy Go = a MEMBERSHIP site.**

Two things this charter still owes on top of that, both Go-specific and
neither a change to the contract. First, §2.4 measured that Go's
permitted set is **size-stratified**, so the per-site datum is not one
set but a function of the location's width — and above one machine word
the set includes outcomes that are not memory-safe. Second, the
always-available *"report the race and halt"* alternative is a member of
every racy site's permitted set, which is what keeps `-race` (§4.4) a
conforming implementation rather than a contradiction.

### 2.6 The §4.3 mapping slot, FILLED for Go

`docs/family-architecture.md` §4.3 makes the behavior-classes → refusal
mapping *"the founding lanes' first deliverable."* Go's row:

| the spec's behavior classes | mapping |
| --- | --- |
| **no `undefined` class at all** (0 occurrences, §1.2) | **cause 2 is EMPTY, and that should be GATED** — a Go tier emitting `undefined` has a bug, in the same way §4.3 prescribes for WebAssembly. This is the family's second near-empty cause-2 bucket and it is empty for a different reason: Wasm's is by design, Go's is because the memory model deliberately bounds its worst case instead of surrendering it. |
| **data races** (memory model §3) | **MEMBERSHIP sites** (§5.1), *not* refusals — size-stratified, with `halt-with-race-report` always in the set. |
| **`select` among ready cases** — a specified *uniform pseudo-random* choice | cause 4's shape, but with a **specified distribution** rather than a free order — §2.2 recommends carrying it on the schedule parameter and scoring under ∀-choice. The distribution is *stated* and deliberately not *sampled*. |
| **map iteration order** — "not specified" | cause 4 exactly: ∀-order, refuse where the observable is not invariant. §2.3 records that the runtime is strictly narrower than the spec, and that the model must follow the **spec**. |
| **goroutine scheduling** — unspecified, no scheduler defined | cause 4 at its largest, and the ∀-parameter design of §3.6 verbatim. §2.1 states the one place Go costs more than C: a schedule is not syntactically bounded, so a **race-freedom census** replaces C's may-alias census. |
| **"implementation restriction"** ×12 | **not a refusal at all** — these are permissions to *reject* a program, so they land in the frontend, the same place C's constraint violations land. |
| **"implementation-specific" / "-defined" / "-dependent"** ×11 | the PROFILE, exactly as C's row has it. Go's version of the profile is smaller and mostly about `unsafe` and numeric conversion. |
| **run-time panics** | an ORDINARY OUTCOME, not a refusal — `Run.exn`'s shape, the same ruling Ada's row took for its run-time errors. |

---

## 3 THE VERSIONING EXEMPLAR — Go 1.21 → 1.22, and it settles a family question

Handed to the family-architecture lane as the copies-vs-deltas test
case, written so their layout decision can consume it directly.

### 3.1 The delta, exactly

It landed in the Go repository as *"doc: document new iteration variable
semantics in spec"* (Robert Griesemer, 2023-12-18). Extracting
`doc/go_spec.html` at tags `go1.21.0` and `go1.22.0` and diffing gives
**a one-clause swap in each of two productions and nothing else**:

**"For statements with `for` clause"** — go1.21, deleted:

> *"Variables declared by the init statement are re-used in each
> iteration."*

go1.22, added:

> *"Each iteration has its own separate declared variable (or variables)
> [Go 1.22]. The variable used by the first iteration is declared by the
> init statement. The variable used by each subsequent iteration is
> declared implicitly before executing the post statement and
> initialized to the value of the previous iteration's variable at that
> moment."*

**"For statements with `range` clause"** — go1.21: *"…their scope is the
block of the 'for' statement; they are re-used in each iteration."* →
go1.22: *"…their scope is the block of the 'for' statement and each
iteration has its own new variables [Go 1.22]."*

The spec's own appendix records it in one line, which is §1.2's
observation paying off immediately: *"In a 'for' statement, each
iteration has its own set of iteration variables rather than sharing the
same variables in each iteration."*

**Scope, tested rather than assumed.** Affected: 3-clause `for` whose
init declares with `:=`, and `range` loops declaring with `:=`. **Not
affected: pre-declared variables in either form** — `var j int; for j =
0; j < 3; j++` gives `[3 3 3]` under *both* versions. Not a GODEBUG:
`$GOROOT/doc/godebug.md` has zero occurrences of "loopvar", so unlike
`panicnil` there is no runtime knob and no `//go:debug` escape.

### 3.2 The money datum — one compiler, one binary, two semantics

The version is selected **per file**. The authoritative statement is in
the "Go Toolchains" document: *"The `go` line for each module sets the
language version the compiler enforces … The language version can be
changed on a per-file basis by using a build constraint."* Local `go
help buildconstraint` states the operative rule. The override works in
**both directions** — verified, including the upgrade direction its prose
header does not mention.

Same source bytes, two modules differing only in the `go` line:

```
=== go 1.21 ===                    === go 1.22 ===
3-clause closures: [3 3 3]         3-clause closures: [0 1 2]
range &v:          [30 30 30]      range &v:          [10 20 30]
spec example:      6 6 6           spec example:      1 3 5
pre-declared j:    [3 3 3]         pre-declared j:    [3 3 3]
```

The cleanest proof is storage identity: collecting `&i` across
iterations and counting distinct pointers gives **1 distinct address
under go1.21 and 3 under go1.22**.

**And then the result that decides the family's layout question.** One
package, `go.mod` saying `go 1.21`, two files with byte-identical loop
bodies — `old_121.go` carrying `//go:build go1.21` and `new_122.go`
carrying `//go:build go1.22`:

```
file built as go1.21: [3 3 3]
file built as go1.22: [0 1 2]
```

`go build -x` shows this is **one compiler invocation**:
`compile … -lang=go1.21 … ./main.go ./new_122.go ./old_121.go`. The
per-file version is resolved *inside the type checker* from each file's
build constraint — it is not a per-invocation flag. **Both semantics are
live within a single compilation unit.**

### 3.3 What this hands the architecture lane

**A COPY architecture is not merely inelegant here — it is incorrect.**
Two whole spec-mirrors, one per version, cannot express a single program
whose files disagree, because there is no single model in which such a
program has a meaning. That is a correctness failure, not an ergonomic
one, and it is demonstrated by an executable rather than argued.

**A pure DELTA/patch representation is also wrong**, for a different
reason: it makes the base version privileged and the patch
un-typecheckable on its own, and it misrepresents the relationship. The
two semantics are *siblings*, not base-and-amendment.

**What the evidence recommends: one model, with the loop rule factored
over a version parameter, and version resolution modeled as an attribute
carried on each FILE** — defaulting from the module, overridable by build
constraint, in both directions. That mirrors the real compiler's own
architecture.

The delta is **local in the abstract syntax and non-local in the
semantic domain**, and the distinction is the transferable lesson.
Exactly two productions change; no new syntax, no typing-rule change,
nothing touching assignment, closures, `go` or `defer`. But the ripple
runs through the **store**: under go1.21 the loop's variables are
allocated once and the body binds them to fixed locations; under go1.22
each iteration allocates fresh ones. Everything that can observe
*location identity* therefore changes downstream although its own rule
is untouched — closure capture, address-of, `defer`, goroutine spawn,
and map keys over `*T`. A definitional interpreter changes in exactly
one place and every other rule is reused verbatim.

**The subtle part, recorded because a model can pass the famous tests
and still be wrong**: the go1.22 rule must (a) allocate fresh locations
per iteration, (b) initialize them from the *previous* iteration's
values read at the moment the post statement runs, and (c) copy back out
so the post statement advances. **(c) is what preserves `[1 3 5]` — the
spec's own worked example — across both versions.** An implementation
that freshens bindings without the copy-out passes every closure-capture
test and silently corrupts ordinary counting loops.

**The acceptance test the architecture lane should be held to:** the
model must evaluate the two-file coexistence package and produce
`[3 3 3]` and `[0 1 2]` from two byte-identical function bodies. If the
architecture cannot express that program, it is wrong regardless of how
faithful either individual version-mirror is.

**Two further data points, both measured, both useful to that lane.**
The Go project's own compatibility numbers: new semantics caused test
failures in about **1 in 8,000 test packages**; the `loopclosure` vet
check flagged **1 in 400**, of which **~5% were genuinely broken** and
95% were tests that merely began testing what they intended; **only one**
failing loop was outside test code. And **the tooling is
version-parameterized too** — the same source under `go vet` reports
`loop variable v captured by func literal` at `go 1.21` and is silent at
`go 1.22`, flagging only the `go1.21`-tagged file in a mixed package. If
the lane models static checks as well as evaluation, version must be
threaded through the analysis layer on the same per-file basis.

**A gotcha worth carrying**, because it silently produces the wrong
answer: `go run prog.go` in file-list mode **ignores the module's `go`
line** and falls back to the toolchain version. Use `go run .`, or the
experiment fails without saying so.

---

## 4 PRECEDENT POSITIONING

**A naming note taken deliberately rather than drifted into: every paper
cited here says Coq; every current repository says Rocq** (Rocq Prover
9.0.0 shipped 2025-03-12). This charter uses each source's own word and
does not silently normalize, because a reader chasing a citation needs
the name the artifact actually carries.

### 4.1 The nearest prior art, and its scale

**Goose** — the Go-to-Coq translator from MIT's PDOS group — is the
closest thing to a Go tier that exists, and it anchors a family of
verified-systems results built on the **Perennial** separation logic
(itself built on Iris). The measured scale, which is the part most worth
having:

| artifact | Go | proof | ratio |
| --- | ---: | ---: | ---: |
| Perennial itself (SOSP 2019) | — | 8,930 lines Coq | — |
| the Goose translator | 1,790 lines Go (≈4,000 by 2022) | — | — |
| Mailboat (SOSP 2019) | 159 | 3,360 | **21×** |
| Grove (SOSP 2023) | 2,435 | 28,077 (+1,597 Perennial extensions) | **12×** |
| vMVCC | 827 | 11,117 | **13×** |

Effort, as reported: **two people, five months** for Perennial plus the
translator; **one person, two weeks** for Mailboat. The band is 12×–21×
proof-to-code, and it is the most directly transferable number in this
section — `docs/c-tier-charter.md` §3 prices the C tier's endgames in
sessions, and this is the same quantity measured on Go by someone else.

Two results worth recording because they cut against the usual story
about verification cost: **Mailboat runs 81% faster than GoMail, the
*unverified* Go mail server it replaces**. And GoJournal reaches ≥90% of
Linux's performance — **on RAM disk and fast NVMe; on a slower SATA SSD
the largefile benchmark drops under 20% of ext4**, recovering only with
unstable writes enabled. The caveat is quoted because omitting it is how
performance claims become folklore.

**Two attribution corrections the census turned up, recorded so this
charter does not propagate them.** The Grove paper **does not name
Goose** — a search of both the camera-ready and the extended version
returns zero occurrences; it says only that Grove is *"implemented by
extending Perennial"* and *"inherits reasoning principles for concurrent
Go code from Perennial."* The Goose connection is a reasonable inference
from the repositories, not a claim the paper makes, and it should be
cited that way. And **Argosy (PLDI 2019) uses no Goose at all** — it
predates it, is entirely sequential, and gets executable code by Coq
extraction to Haskell plus a trusted Haskell interpreter. It is best read
as the predecessor Perennial was built to replace.

Repository status, because it bears on whether this is a live baseline:
**`goose-lang/goose` is archived and read-only** (last push April 2026);
development continues inside the Perennial repository, with a
**v0.10.0 "new goose"** release dated 2025-11-30.

### 4.2 What Goose actually is, and the four facts that position it

**Mechanically**, GooseLang is a deep embedding in Coq/Rocq of an
untyped, effectful lambda calculus with mutable references and
concurrency — in the source's own words, *"an adaptation of HeapLang with
extensions to model Go, including support for a customizable 'FFI' for
new primitive operations and crash semantics."* Go source goes through
**`go/ast` + `go/types`** — the real front end, the same choice §7.3
recommends — to a GooseLang term emitted as a Coq definition, which Coq
type-checks and Iris/Perennial then reasons about.

The governing design rule is **model Go features as GooseLang *code*, not
as primitives**, and the sharpest instance is worth recording because it
is the opposite of what a spec-mirror does: **`chan T` is not a primitive
at all** — it is a generic Go struct (a ring buffer plus four sync flags)
translated like any other Go code. `select` is the one construct that
needed new syntax, and its semantics nondeterministically permutes the
non-default clauses, tries them in order, and **retries the whole
statement** if none is ready: a busy-retry loop rather than a blocking
wait, with **no fairness and no liveness guarantee**.

And the relationship runs the *other* way from a mirror's: *"an arbitrary
GooseLang program is much more general than translated Go programs — for
example, GooseLang has support for pointer arithmetic."* **GooseLang is a
superset in expressiveness, not a model of Go.**

**The subset — and the published numbers are badly out of date, which is
the single most important correction in this section.** Through the 2022
thesis, Goose rejected interfaces, channels, `defer`, closures, signed
integers, `sync/atomic`, non-`uint64` map keys, and *recursion* (files
had to be topologically ordered, which is why the corpus contains
filenames like `0constants.go`). **"New goose" (v0.10.0, 2025-11-30)
accepts** `defer` — including defers queued in a loop, the hard dynamic
case — `select`, send statements, type switches, interfaces, generics,
closures, type assertions, and both `panic` **and** `recover`. It carries
models for ~25 standard-library packages and its CI translates etcd,
etcd/raft, grpc and zap. **Anyone citing the thesis's subset today is
citing a five-year-old artifact.**

Still rejected, by direct inspection of the translator's dispatch:
**labeled statements and `goto`** — there is no `ast.LabeledStmt` case at
all, so no labeled `break`/`continue` — plus complex numbers, `reflect`,
`uintptr`, anonymous structs, method expressions and unnamed type
parameters. **Garbage collection has never been modeled in any version**:
GooseLang allocates and has no deallocation primitive, so the heap only
grows and nothing can be said about exhaustion or finalizers.

**The trust story: the translator is TRUSTED, and there has never been a
faithfulness proof.** Stated three independent times — the README (*"The
translator and semantics are trusted; you can view the process as giving
a semantics to Go"*), the 2022 thesis (*"Goose is a trusted component in
the entire verification process"*), and GoJournal's assumption list. The
mitigation is a genuine fail-safe asymmetry, and the thesis puts it
well: any Goose bug causing a *translation failure, a Coq type error, or
modeled UB* is automatically **sound**, so *"the most important bugs are
those where the translation is well-defined but its behavior differs from
that of Go."* Working against it, the current pipeline has explicit TCB
escape hatches — a per-package filter marks declarations `trusted`
(substituting hand-written Coq), and a flag **emits `Admitted`
proofs**; `sync`, `sync/atomic`, `time`, `runtime`, `fmt`, `log` and the
FFI are all hand-written trusted models.

**Differential testing EXISTS, and the charter must not claim otherwise.**
Gibson's *"Waddle: A proven interpreter and test framework for a subset
of the Go semantics"* (MEng, MIT, May 2020) built a GooseLang interpreter
in Coq, proved it matches the semantics, and ran each test **both
natively under real `gc` and through the interpreter**. It found a dozen
real bugs — `<` and `<=` compiling identically; an equality comparing a
value to itself and always returning true; untyped-constant arithmetic
done at 64 bits instead of Go's infinite precision; missing
short-circuiting; three operator-precedence divergences; struct-literal
fields evaluated in declaration order rather than literal order.

Its limits are instructive rather than embarrassing: ~50 tests; the
theorem `interpret_ok` is **soundness only and fuel-bounded**, and the
thesis is admirably blunt that *"an interpreter that always fails would
satisfy the `interpret_ok` property"*; completeness is unprovable because
*"the interpreter does not implement concurrency, and uses a
deterministic subset."* The interpreter directory was maintained through
February 2025 and **deleted in January 2026**, replaced by proof-based
tests covering roughly 12 of 30 files.

**And the answer to the question that decides the comparison: Goose has
never been run against Go's `test/` directory or any conformance suite.
Verified, not assumed.**

**The memory model — Goose assumes sequential consistency, and says so.**
Thesis §7.5.1, verbatim:

> *"GooseLang disallows concurrent reads and writes to the same location
> by making such racy access undefined behavior. … **Go's own memory
> model documentation specifies even weaker guarantees. Rather than
> attempt to formalize Go's rules, the semantics side-steps the issue and
> makes any races undefined**, which works for our intended use cases
> since the verified code always synchronize concurrent access with
> locks."*

The mechanism is visible in the source: each heap cell carries a mode
(`Writing` or `Reading n`), a read increments the reader count, a write
requires zero readers, and any overlap steps to `undefined` — stuck,
which adequacy rules out. **No store buffer, no happens-before relation,
no release/acquire, no memory-order parameter anywhere.**

**This is the charter's single most decision-relevant comparison, and it
runs exactly opposite to the intuition.** §2.4 measured that Go's memory
model *deliberately declines* C-style UB for racy programs. **Goose puts
it back.** GooseLang is therefore **not a faithful model of the Go
specification on racy programs — it is strictly more restrictive** than
the document it models. That is sound and entirely legitimate for its
purpose, and it is a defect for a spec-mirror. The step from "SC model,
no UB" to real Go on x86-TSO or ARM is **a paper argument resting on Go's
documented DRF-SC guarantee, not a mechanized theorem.**

Four further admitted divergences, each of which is Goose choosing
convenience where the spec is silent or inconvenient — and each of which
a spec-mirror would have to get right instead: **function application
evaluates right-to-left, the opposite of Go** (called *"one extant bug"*
and still carrying a `BUG` comment in the source); **map iteration is
deterministic where Go randomizes** (§2.3); slice capacity is left
nondeterministic *"because the Go language reference isn't specific"*;
and `sync.Cond.Wait` is modeled weaker than Go's guarantee.

### 4.2.1 The positioning, with the claim the census REFUTED stated first

**A claim this charter was about to make is false, and the census caught
it.** "Goose cannot be differentially tested the way an interpreter can"
is **wrong** — Waddle did exactly that and found real bugs. It is struck,
and it does not appear in this document as a claim.

**The real asymmetry is threefold and structural**, and the first item is
the one to lead with:

1. **Goose's corpus is bounded by the TRANSLATOR; a spec-mirror's is
   bounded by the LANGUAGE.** A program Goose declines to translate
   cannot be a test case at all. Every feature it declines to model is
   one it need not be right about — which is excellent engineering for
   Goose and precisely the freedom a conformance claim gives up.
2. **Goose's model is a RELATION, not a function.** Executing it requires
   building *and proving* a separate interpreter — sound-only, never
   complete, over a deterministic sequential fragment. This is the state
   of the art rather than a Goose failing; JSRef's theorem has the same
   shape and the same caveat.
3. **The economics do not reward fidelity testing.** Waddle was built,
   ran for six years, and was removed in the rewrite. A project whose
   deliverable is per-program proofs will always under-invest in
   language-level fidelity, because fidelity testing makes no theorem
   stronger.

**What each side can state that the other cannot.** Goose: *"this
specific program refines this specification, under arbitrary interleaving
and arbitrary crashes, machine-checked."* A definitional interpreter
gives no separation logic, no ownership, no invariants, no ghost state,
no crash weakest-preconditions — **executing and proving are different
activities.** A spec-mirror: *"for all programs p, the model of p agrees
with the reference toolchain"* — a universally quantified claim about the
**language**, on a corpus it did not choose. Goose's theorems are always
existential in the program. Only a spec-mirror hosts language-level
meta-theorems, and **only a spec-mirror can find bugs in the
specification.**

**What Goose gets free that this lane would build:** Iris plus Perennial
is roughly 25,000–46,000 lines of Coq of reasoning infrastructure before
one Go program is verified. The charter's advice to itself is
correspondingly modest: **do not rebuild Perennial; do steal the front
end**, which §7.3 independently arrived at.

**The complementarity is concrete and nobody has formulated it for Go:**
*"for all p in the accepted subset, `GooseLang(translate(p))` and
`SpecModel(p)` agree"* is a **translation-validation** statement that
needs both artifacts, and it is exactly what Goose currently discharges
by trust plus ~50 tests.

### 4.2.2 THE ACTUAL PRECEDENT is JSCert, not Goose

The founding brief named Goose, and Goose is the nearest *Go* work. But
the nearest work to **this architecture** is JavaScript's, and it matches
so closely that the charter adopts its vocabulary:

> Bodin, Charguéraud, Filaretti, Gardner, Maffeis, Naudžiūnienė,
> Schmitt and Smith, *"A Trusted Mechanised JavaScript Specification"*,
> POPL 2014.

Their trust chain **is** this lane's design, one link at a time:
ES5 ←*eyeball*→ JSCert ←*correctness proof*→ JSRef ←*running tests*→
Test262. Their term for spec-mirroring is **"eyeball closeness"**:
*"We designed JSCert to follow the structure of the ES5 English standard
as much as possible … one line of ES5 pseudo-code corresponds to one or
two rules in JSCert."* JSRef is proved **sound only** — *"because of the
looseness of ES5, our interpreter cannot be proved complete"* — extracted
to OCaml, and run on Test262 at **1,796 of 2,782** core-language tests.

**Three transferable results, and the third is the one that justifies the
whole approach.** They reported bugs in browsers; they reported bugs in
Test262 *itself*; and they **declined to specify `for-in` at all —
because in trying to, they discovered ES5 and ES6 were broken, and filed
a spec bug.** That last is the capability §4.2.1 claims a spec-mirror has
and a translator does not, demonstrated rather than argued, by a
different project in a different language.

Two adjacent precedents this repository should read as siblings rather
than competitors, one of which the C lane already cites: Ellison and
Roşu, *"An Executable Formal Semantics of C with Applications"* (POPL
2012 — the K semantics, **99.2% of 776 GCC torture tests**), and Memarian
et al., *"Into the depths of C: elaborating the de facto standards"*
(PLDI 2016 — Cerberus, which `docs/c-tier-architecture.md` §3.2 already
positions against).

### 4.3 The rest of the landscape, briefly

* **Model checking Go's happens-before.** Gabet and Yoshida (ECOOP 2020)
  encode Go's happens-before relation into µ-calculus for mCRL2. This is
  the closest anything comes to mechanizing the memory model — and it is
  model checking of *behavioural types*, not a mechanized semantics.
* **Static deadlock detection**, a decade-long line (Gong, Godel, Godel2,
  Gomela) out of the session-types community. The honest measurement:
  on an independent 78-program benchmark these tools **abort on 74% of
  real-world inputs**, variously requiring finite control or failing on
  goroutines spawned in loops.
* **And the result that actually shipped.** Saioc, Lee, Møller and
  Chabbi, *"Dynamic Partial Deadlock Detection and Recovery via Garbage
  Collection"* (ASPLOS 2025). The insight is that **memory reachability
  soundly over-approximates goroutine liveness**: a goroutine blocked on
  a primitive unreachable from any runnable goroutine can never be
  signalled, so it has leaked. Implemented inside the GC mark phase at
  negligible overhead, and **upstreamed** — an experimental
  `goroutineleak` profile in `runtime/pprof` in Go 1.26, graduating to a
  regular profile in Go 1.27. **Any argument for a static or
  definitional treatment of Go concurrency now has to be made against
  this baseline, not against `go vet`.**
* **Parametric concurrency.** Saioc, Lange and Møller (OOPSLA 2024) give
  the first credible attack on *parametric* channel-based communication —
  symbolic *n* goroutines — by encoding into Dafny. Everything before it
  was bounded.
* **LTL model checking.** Go2Pins (SPIN 2021; extended in STTT 25, 2023)
  checks LTL properties of Go via the PINS interface to Spot and LTSmin,
  notable for **black-box transitions**, which abstract untranslatable
  runtime code rather than failing on it — a refusal discipline with a
  different shape from this project's.
* **A search term in the founding brief that must not be followed.**
  *"Verifying message-passing programs with dependent behavioural types"*
  (PLDI 2019) is **Scala/Dotty (Effpi)**, not Go. It is not Go prior art.

### 4.4 The race detector is the only Go concurrency oracle, and it is dynamic

This matters directly, because §5.5 finds no memory-model suite and the
race detector is what a lane would reach for instead.

**Cite it correctly**: Go's detector is ThreadSanitizer **v3** (v2 on
`windows/amd64` and `openbsd/amd64`), upgraded in Go 1.19 — 1.5–2×
faster, half the memory, and it removed the old 8,128-simultaneous-
goroutine cap that used to abort race-enabled runs. The operative
reference is Serebryany, Potapenko, Iskhodzhanov and Vyukov, *"Dynamic
Race Detection with LLVM Compiler"* (RV 2011, LNCS 7186, pp. 110–114).
**The WBIA 2009 paper is TSan v1, a hybrid happens-before + lockset
algorithm, and is NOT what Go runs** — v2/v3 dropped the lockset
component and is **pure happens-before with vector clocks**.

**Three limits, and together they say the oracle cannot certify
absence:**

1. **It is dynamic** — it reports races only on executions it actually
   observes. One sampled schedule is one sampled schedule.
2. **Pure happens-before means a schedule that happens to ORDER two
   conflicting accesses hides the race entirely.** Zero false positives
   was bought with recall, and this is exactly the case the abandoned
   lockset component would have caught.
3. **Shadow state is evicted.** Four shadow words per 8-byte granule by
   default; when they fill, *"a random Shadow Word is evicted"*, so
   races against evicted history on hot locations are silently missed.
   The documentation separately concedes *"there is tiny probability to
   miss a data race"* from the lock-free shadow update itself.

**So `-race` is a falsifier, never a certificate** — the same standing
this project already gives BMC in the SV lane (`docs/litreview/SYNTHESIS.md`
§3.5: kernel proofs over model checking, BMC as falsifier only). §7.1's
30 clean `-race` runs of the driver are evidence of *no observed race*,
which is what the charter claims and nothing more.

### 4.5 THE GAP — stated with its honest half first

**The honest half.** A spec-mirroring Go tier adds *less than one might
hope* on deadlock and liveness. That ground is well worked, and the state
of the art on goroutine leaks is now **inside the Go runtime** (§4.3), at
negligible overhead, shipping to every user in Go 1.27. A definitional
interpreter will not beat a GC-integrated dynamic analysis at finding
leaked goroutines in real programs, and the charter should never imply
otherwise.

**The gap that is real, and it is narrow and clean:**

> **There is no formalization of the Go memory model in any proof
> assistant, and no herd7/`.cat` model of it.**

That is the cleanest hole in the landscape, and it is the one **every
Go verification tool currently fills with an assumption**. §4.2 found the
strongest possible evidence for this, from the most serious project in
the field, in its own words: Goose *"side-steps the issue and makes any
races undefined"* rather than *"attempt to formalize Go's rules"* — and
in doing so **reintroduces exactly the C-style undefined behavior that
Go's memory model was written to refuse** (§2.4). Go2Pins and the
session-type line likewise reason about concurrent Go while taking the
memory model on trust.

§5.5 measured the corresponding hole on the testing side — `test/`
contains zero memory-model tests — so the document is **unformalized
*and* untested**, and those two facts are the same fact seen twice.

There is a concrete, named thing a mechanized memory model would buy
someone other than this lane: **Perennial's step from "SC model, no UB"
to real Go on x86-TSO or ARM is currently a paper argument resting on
Go's documented DRF-SC guarantee.** A mechanized model would let that
step be *proved*. That is a smaller and more honest claim than "we would
verify Go", and it is the one the evidence supports.

A spec-mirroring tier is the shape of artifact that would close it,
because the memory model is a *specification document with 11 marked
rules and three named relations* (§1.3) — which is precisely what a
spec-mirror is for, and precisely what a translation-for-verification
tool has no reason to build.

---

## 5 THE CORPUS CENSUS — there is no official suite, and what that means

### 5.1 The situation, named against its two siblings

**Go has no official conformance suite.** The de-facto corpus is the Go
repository's top-level `test/` directory, driven by the toolchain's own
runner. That places Go in the same position as C —
`docs/c23-goal.md` opens with *"There is no official ISO conformance
suite"* — and in the **opposite** position from the two lanes that have
one: Wasm ships an official spec test suite, and Ada has ACATS. The
consequence is the one `docs/c23-goal.md` already worked out and it
transfers verbatim: **a high score means "agrees with what this project
tests", never "conforms to the specification."**

Go's version of the problem is *milder* than C's in one respect and
*worse* in another, and both are measured below. Milder: C's proxy
corpora are four different projects' regression histories under four
licenses, one of them copyleft; Go's is **one corpus, one license, one
runner**. Worse: Go's corpus is far more tightly coupled to the *compiler
implementation* than C's is (§5.3).

### 5.2 What is there — measured against go1.25.6

The corpus ships inside the distribution at `$GOROOT/test`. **3,397
files, 7,569,635 bytes, 316 subdirectories** — of which 289 are `.dir/`
support-package trees.

**But the count that matters is 2,617, not 3,284.** The runner does not
walk the tree: `src/cmd/internal/testdir/testdir_test.go` hard-codes the
scanned directories and reads each **non-recursively**. So **2,617 files
are registered test cases** and 667 further `.go` files are support code
pulled in by a parent `*dir` test. A census that counted `.go` files
would overstate the corpus by 25%.

**The directive histogram**, extracted with the runner's own rule (which
is not "first line" — `//go:build` and `// +build` lines are skipped
first):

| directive | n | | directive | n |
| --- | ---: | --- | --- | ---: |
| `run` | 1,023 | | `runoutput` | 22 |
| `errorcheck` | 660 | | `runindir` | 10 |
| `compile` | 501 | | `skip` | 9 |
| `compiledir` | 124 | | `errorcheckandrundir` | 5 |
| `rundir` | 116 | | `errorcheckwithauto` | 5 |
| `asmcheck` | 71 | | `buildrundir` | 4 |
| `build` | 32 | | `errorcheckoutput` | 4 |
| `errorcheckdir` | 25 | | `builddir` | 3 |
| | | | `buildrun` | 2 |

**17 legal directives**, and the authoritative list is not prose — it is
the validation switch in the runner source. `test/run.go` no longer
exists and `test/README.md` does not enumerate them. Directive coverage
is **2,616 of 2,617 = 99.96%**; the single exception is a support file
the runner registers and then skips on its own build constraint.

239 tests (9.13%) carry arguments; 102 distinct flag strings. Language-
level flags are rare — `-lang=go1.12` … `go1.22` across 11 files total —
and the long tail is `-d=ssa/<pass>/debug=N` and `-gcflags=…`.

### 5.3 The verdict mapping, and the finding that decides the goal

| oracle class | directives | n | % |
| --- | --- | ---: | ---: |
| compile-only (pass = exit 0) | `compile`, `compiledir`, `build`, `builddir` | 660 | 25.2 |
| **execute + compare output** | `run`, `rundir`, `runindir`, `buildrun`, `buildrundir` | **1,155** | **44.1** |
| two-stage execute | `runoutput` | 22 | 0.8 |
| **compare compiler DIAGNOSTIC TEXT** | `errorcheck` family | **694** | **26.5** |
| hybrid | `errorcheckandrundir` | 5 | 0.2 |
| **generated ASSEMBLY vs regexps** | `asmcheck` | **71** | **2.7** |
| not run | `skip` | 9 | 0.3 |

**Where the expected output lives, and the answer is unusually cheap.**
Expected stdout is a sibling `.out` file — *and if it is absent the
output must be empty*. Measured: **97 `.out` files exist**, and of the
1,182 execution-oracle tests **1,085 (91.8%) must produce no output at
all**. The dominant idiom is self-checking: of 937 `run` tests expecting
empty output, **556 call `panic(...)`**. So the practical verdict for a
`run` case is *exit 0 with nothing printed*, which is the same
"scoreable with ZERO output modeling" result `docs/c23-goal.md` §1.2
found for GCC's torture suite — arrived at independently, by a different
mechanism.

**And the finding that must shape the goal statement: `errorcheck` is a
far stronger obligation than it looks, and most of it is not about the
language.** It does not assert "this program is ill-formed". It asserts
the **exact diagnostic text**, per source line, against a regexp, with
`LINE±n` substitution, failing in *both* directions — an unexpected
diagnostic fails, and a missing one fails. Measured across the corpus:
**5,772 `// ERROR` annotation lines carrying 6,382 expected-diagnostic
regexps** in 698 files. Splitting them by whether the test passes a
diagnostic-dumping flag:

| bucket | files | regexps |
| --- | ---: | ---: |
| language-level (type / syntax / declaration errors) | 591 | 2,551 |
| **compiler-internal** (`-m` escape analysis, `-live` liveness maps, `-d=ssa/*`) | **108** | **3,511** |

**55% of every `// ERROR` regexp in the corpus is gc optimizer-internal
output, not language semantics.** The heaviest files are `escape2.go` and
`escape2n.go` at 401 regexps each and `prove.go` at 289 — escape-analysis
and SSA-prove dumps. Matching those would mean reimplementing
`cmd/compile`'s optimizer *wording*.

**The ruling this forces**, and it is the Go analogue of
`docs/c23-goal.md` §3.1's rule that REFUSE's causes must not be pooled:
the `errorcheck` family is scored on **the coarse bit only** — did the
model reject the program? — and the charter must say plainly that this is
**a weaker predicate than the corpus itself checks**. Scoring the text
is not a rung; it is a different project.

**The honest split:**

| | n | % of 2,617 |
| --- | ---: | ---: |
| usable as LANGUAGE SEMANTICS conformance | **2,426** | **92.7** |
| toolchain / compiler internals (`asmcheck` 71, internal-diagnostic `errorcheck` 108, `dwarf` 2) | 181 | 6.9 |
| `skip` + build-ignored | 10 | 0.4 |

Structurally: 2,330 single-file, 287 multi-file. **80 registered files do
not parse** — deliberately malformed syntax-error tests, which is a
category and not a failure, exactly as `docs/c23-goal.md` §1.5 records
for dg/lit tests.

### 5.4 The honest scale statement

Two filters, both measured by AST inspection rather than grep.

**A sequential interpreter with an execute-and-diff oracle, today:**

```
all registered cases                                       2617
  directive == `run`                                       1023
  no go-stmt / chan / send / recv / select                  897
  no sync or sync/atomic                                    888
  no unsafe                                                 835
  no reflect                                                786
  no runtime*                                               711
  no cgo                                                    707
  no flags or args on the directive                         694
```

**Tier A = 694 = 26.5% of the corpus.** Tightening the import surface:
**456 import nothing at all**; **570 import only `fmt`**; 643 import only
a seven-package set. 624 of the 694 expect empty output. Dropping
generics (128 of the 694 use type parameters) takes the no-import tier to
377.

**With accept/reject verdicts added**, `compile`/`build`/plain
`errorcheck` open up: **1,643 cases = 62.8%** become reachable — but only
under §5.3's coarse-bit ruling.

**What the filter misses, every one of which makes the true number
SMALLER**, recorded because a scale statement that only lists its
successes is not honest:

1. **`fmt` is not free.** 176 Tier-A files import it, output is compared
   exactly, and `fmt.Println` over arbitrary values needs Go's verb
   semantics byte-for-byte. This is the `printf` problem
   `docs/c23-goal.md` §1.3 identified for C, in Go clothing.
2. **Runtime semantics are invisible to an import list** — GC timing,
   finalizers, scheduling, stack growth, map-iteration randomization
   (§2.3), `int` width. `abi/`'s 33 Tier-A cases are *specifically*
   about register-ABI call/return behavior.
3. **`panic`/`recover` in 373 of the 694**, several asserting on runtime
   error *strings* — the diagnostic-text obligation smuggled into a
   `run` test.
4. **`fixedbugs/` is adversarial by construction**: 428 of the 694 are
   minimized compiler-bug reproducers, clustering on exactly the corners
   a clean definitional interpreter gets wrong. Coverage-by-count will
   read *low* early and then jump.
5. **Empty-output tests are weak in one direction** — an interpreter that
   no-ops passes many of the 624. The 556 embedded `panic`s are what give
   them teeth, and only if evaluation is faithful.

### 5.5 The concurrency corpus — and it is the section's worst news

| | n | % of 2,617 |
| --- | ---: | ---: |
| files with a `go` statement | 96 (306 occurrences) | |
| files with `select` | 70 (242 occurrences) | |
| files with channels | 204 | |
| files importing `sync` / `sync/atomic` | 35 | |
| **union — concurrency-touching** | **250** | **9.6** |

The dense ones are worth naming as future fixtures: `test/chan/select3.go`
(17 selects), `test/ken/chan.go` (26 goroutines), `test/chan/powser1.go`
and `powser2.go` (16 goroutines each, concurrent power series),
`test/chan/nonblock.go` (8 goroutines, 12 selects, 21 channel types).

**And then: `test/` contains ZERO memory-model tests.** Grepping the
whole corpus for "memory model" or "happens before" returns exactly two
hits, both incidental comments. **The Go Memory Model exists only as
prose.** There is no executable conformance suite for it anywhere in the
tree.

The nearest executable proxy lives elsewhere — `src/runtime/race/testdata/`,
**25 files, 372 `func Test`** — and it is not a substitute: those tests
assert **that ThreadSanitizer reports a race**, i.e. they test the
detector's instrumentation, not the model. They require cgo and a
platform `.syso` blob.

**So the charter must state this plainly: for the concurrency tier — the
part of Go this workstream was chartered for — there is nothing to score
against. The lane would be building the oracle, not borrowing one.** That
is a genuine cost, it is the single biggest scoping fact in this
document, and it is §9's first decision.

### 5.6 License, verified per file — and the recommendation is FETCH

The repository license is **BSD-3-Clause**: `LICENSE`, 1,453 bytes,
opening *"Copyright 2009 The Go Authors."*, with the non-endorsement
third clause that distinguishes it from BSD-2-Clause. A separate
`PATENTS` file — *"Additional IP Rights Grant (Patents)"* — carries a
royalty-free patent grant with a defensive-termination clause. BSD-3
is silent on patents, so a redistributor should ship both.

**Per-file, every file read rather than sampled**, across all 3,284
`.go` files in `test/`:

| | n | % |
| --- | ---: | ---: |
| full canonical 3-line Go Authors BSD header | 3,155 | 96.07 |
| same grant, reflowed or missing a trailing period | 45 | 1.37 |
| **carrying the Go Authors grant** | **3,200** | **97.44** |
| no license header at all | 84 | 2.56 |
| **non-"Go Authors" copyright line** | **0** | **0.00** |

The 84 header-less files are generated or fragmentary support code and
carry no *other* licence. A third-party scan of every file in `test/` for
Apache, MIT, GPL, LGPL, MPL, SPDX identifiers, public-domain and CC
notices found **none**. **`test/` is uniformly and exclusively Go Authors
BSD-3-Clause** — which is a materially better position than
`docs/c23-goal.md` §2 found for c-testsuite, where a top-level MIT
concealed 69 LGPL-2.1 cases and vendoring would have redistributed
copyleft under a wrong notice. **That trap does not exist here**, and
saying so is worth as much as finding one would have been.

For contrast, and as a boundary worth recording: `src/` contains **19**
distinct `LICENSE` files including vendored Apache-2.0 code. **None of it
is under `test/`.**

**The licence permits vendoring outright. Recommend fetching anyway**, and
the decisive reason is not size:

* Size is not the argument, though it is favourable: 7,569,635 bytes
  uncompressed (~18 MB on disk), **1,142,679 bytes** as a gzipped tar.
* **The corpus is version-coupled to the toolchain.** 6,382 diagnostic
  regexps written against one specific `cmd/compile`, plus
  `-lang=go1.12…go1.21` and `-goexperiment` flags, mean a pinned `test/`
  tree only means anything beside its own runner. **A vendored copy rots
  silently into a claim about a compiler that is no longer present.**

**Pin by content hash, not by commit.** The distribution is built from
the official `go1.25.6` source tarball, SHA256
`58cbf771e44d76de6f56d19e33b77d745a1e489340922875e46585b975c2b059`. It is
not a git checkout, so there is no commit to cite — the version identity
*is* the digest. If a hermetic CI slice is ever needed, the no-import and
`fmt`-only tiers are 456 and 570 files at a 608-byte median, well under
1 MB, plus `LICENSE` and `PATENTS`.

### 5.7 The secondary corpus, and why it stays secondary

The standard library's own tests: **1,691 `_test.go` files, 16,229,744
bytes — 2.14× the whole of `test/` — carrying 8,793 `func Test`**, 1,848
benchmarks, 982 examples, 51 fuzz targets. Licence-clean (0 vendored
`_test.go`, no third-party copyright).

Four reasons it is secondary, and the third is disqualifying:

1. **Not standalone.** Every entry point is `func TestX(t *testing.T)`
   and runs only under a working `go test`: package resolution, build
   tags, `testdata/`, `TestMain`, subtests, `t.Parallel`. There is no
   per-file directive and no golden-output convention. **The driver is
   the toolchain.**
2. **It tests libraries, not the language.** Passing `crypto/tls` says
   nothing about whether `defer`/`recover` ordering is right.
3. **The oracle is circular.** The pass criterion is imperative Go
   (`if got != want { t.Errorf(...) }`), so *running it requires already
   having a working Go implementation.*
4. **Scale is a liability** — 16.2 MB and 8,793 entangled entry points
   against 2,617 self-describing single-purpose files.

**Use `test/` as primary. Reach for the stdlib tests only as a later
stress tier, and only through `go test` as an external oracle.**

### 5.8 A THIRD corpus, found late, and it is organized around the SPEC

The census above treated `test/` as the only candidate because it is the
one the folklore names. It is not the only one, and the alternative is a
materially better fit for a spec-mirroring project. Verified locally:

**`$GOROOT/src/internal/types/testdata/` — 346 `.go` files**, the type
checker's own corpus: `fixedbugs/` 249, `check/` 77, `examples/` 8, and
**`spec/` 12**.

`test/` is organized around *compiler regressions* — §5.4 measured that
428 of the 694 reachable cases are minimized bug reproducers. **This
corpus is organized around the specification**, and the `spec/`
directory says so in its filenames: `assignability.go`,
`comparability.go`, `comparisons.go`, `conversions.go`, `receivers.go`,
`range.go` — each named for a spec section rather than an issue number.

**And it independently corroborates §3's whole thesis**, which is why it
earns a subsection rather than a footnote. Five of the twelve `spec/`
files carry a **language version in the filename**:
`comparable1.19.go`, `typeAliases1.8.go`, `typeAliases1.22.go`,
`typeAliases1.23a.go`, `typeAliases1.23b.go`. **The Go project versions
its own conformance tests per language version, in the corpus layout.**
§3.3 argued from an executable that per-version semantics must coexist
inside one model; here is the Go project having reached the same
conclusion about its own test corpus, by a different route.

The honest limit: this corpus is **static semantics only** — it exercises
the type checker, so it scores accept/reject and diagnostic text, never
behavior. It is a complement to `test/`'s 1,023 `run` cases, not a
replacement. But for the accept/reject half of §5.4's 1,643 it is the
better-shaped corpus, and it was missed by the first pass.

### 5.9 Precedent for consuming this corpus — two, and both are directly usable

Neither had to be invented, and the charter records them so the lane does
not re-derive either:

* **A third party already adapts `test/` to a different compiler.** Go's
  `test/` directory is mirrored into GCC's tree explicitly *"so that the
  same tests as the gc Go compiler can be run"*, and the adapter is a
  DejaGNU script, `go-test.exp`. It mechanically rewrites
  `// ERROR "string"` into `// { dg-error {string} }`, **relaxes
  multiple same-line errors from all-must-match to any-may-match**, and
  carries an explicit skip list with candid reasons (`safe/` — "gccgo
  does not support safe mode"; `init1.go` — "GC runs during init, which
  for gccgo it currently does not"). **That file is the template for any
  non-gc consumer of this corpus**, and its error-matching relaxation is
  precisely §5.3's coarse-bit ruling, already implemented by someone
  else against the same obstacle.
* **An interpreter already runs a `$GOROOT/test` slice against a STUBBED
  standard library.** `x/tools/go/ssa/interp` carries a `TestGorootTest`
  that runs **64 programs drawn from `$GOROOT/test`** against a
  deliberately stubbed stdlib, because — in its own words — *"the
  interpreter requires intrinsics for assembly functions and many
  low-level runtime routines, [and] is inherently not robust to
  evolutionary change in the standard library."* **That is the answer to
  §5.4's objection 1** — how an interpreter that cannot run `fmt` still
  gets a real conformance signal — and it is a shipped design, not a
  proposal. A second self-contained corpus exists in yaegi's 985-file
  `_test/` tree.

**Independent oracle families, counted correctly: three, not four.**
`gccgo` and `gollvm` share the `gofrontend` front end and are therefore
**not** independent of each other. The genuinely independent
implementations are **gc**, **gofrontend**, and **TinyGo**; the
interpreters `yaegi`, `gomacro` and `ixgo` are further oracles, and
GopherJS is interesting specifically as an independent *scheduler*.
Caveats that bound their usefulness: gccgo is effectively frozen at Go
1.18 with **no generics**, and gollvm has no race-detector support.

---

## 6 THE ARCHITECTURE DECISION — the schedule enters on day one

### 6.1 The decision

**Own semantic model. Shared world DISCIPLINE. Sibling of
`LeanModels/C/` and `LeanModels/Python/`, client of neither.** The C
tier's §2.1 reasoning transfers wholesale and the census re-confirms it
for Go's own reasons: Go's integers are fixed-width like C's (so
Python's unbounded `RVal.int` will not do), Go has pointers and
addressable locals (so Python's address-free `REnv` will not do), and Go
has a *garbage-collected* heap with no free (so C's allocator model does
not transfer either).

**`Run σ α`'s four constructors are re-confirmed against the Go census
and they fit unchanged — including for races.** An earlier draft claimed
a bounded-outcome result forced a fifth shape; `docs/family-architecture.md`
§5.1 settles it the other way and settles it better. The permitted set is
a **per-site datum** carried by the scoreboard, not a new inhabitant of
the outcome type: the model still returns *one* observable, and the
verdict system asks whether that observable is *permitted* rather than
whether it is *equal*. So the outcome vocabulary is untouched, and the
open question is the smaller one §5.1 leaves open for everyone — whether
the site carries its permitted set explicitly or the scoreboard consults
a tier-supplied predicate (§9.3).

### 6.2 THE SEQUENCING RULE, and how concurrency avoids being a retrofit

The C tier's discipline says the sequential core comes first, and it is
right here too: **§1.2 measured that Expressions is 32.4% of the Go spec
and the entire concurrency core is 3.8%.** A tier that built goroutines
before expressions would be building the small end first.

**But the schedule parameter enters the design on day one even though
rung 1 is sequential, and this is the charter's one non-negotiable
structural commitment.** The mechanism, stated concretely enough to be
checkable:

> **The evaluation judgment is `Run σ α` with `σ = GoWorld`, and
> `GoWorld` carries a `sched : Schedule` field from the first commit —
> even while `Schedule` is a one-element type and no rule reads it.**

Three reasons this is the right shape rather than premature generality,
each grounded in something already measured:

1. **`sequenced before` is defined by delegation to the spec's "Order of
   evaluation" section (§1.3).** So the *sequential* semantics is
   already a component of the concurrent one, by the memory model's own
   construction. Building the sequential core is building the first
   relation of three, not building something that will be replaced.
2. **The C tier measured what retrofitting costs.**
   `docs/c-tier-charter.md` §3.3 records that R6 — concurrency — *"is
   the one rung that is not a widening: it replaces a state function
   with a memory-ORDER relation, which would change the interpreter's
   TYPE and break `fuelMono`, `#py_check` kernel-reducibility and the
   one-line-per-job batch protocol at once."* **That is the retrofit
   this charter exists to avoid.** Carrying `sched` in `σ` from the
   start means the type never changes; only the inhabitants of
   `Schedule` grow.
3. **It costs almost nothing to carry and everything to add later.** A
   phantom field on a state record is invisible to every sequential
   rule. Widening `Schedule` from one element to many changes no
   signature.

The same parameter carries the class-B select choices (§2.2's
recommendation 3) and the class-C map orders (§2.3), which is why it is
one parameter and not three: all three classes are *choices resolved
outside the program text*, and the model should have exactly one place
where such choices live.

**What this does NOT commit to** is a memory-order relation. The
`Schedule` parameter is a *choice oracle*, not a happens-before graph.
Whether the tier eventually needs the full relational memory model —
which is the thing that would break `fuelMono` — is an endgame question
(§9), and the sequential-first plan deliberately does not answer it. The
commitment is only that the *place* for the answer exists on day one.

---

## 7 THE DRIVER ARTIFACT

### 7.1 Rung 0 — `Examples/go/pipeline/pipeline.go`, and why it was rewritten

The brief allowed either writing a minimal driver or finding one. **Both
were done: the survey ran first, and it is what says the driver had to
be written.**

**The read-only survey of Thomas's repositories**, measured across every
`.go` file outside `vendor/`:

| repo | .go files | bytes | with `go` stmt | with `chan` | with `select` |
| --- | ---: | ---: | ---: | ---: | ---: |
| harbor | 1,562 | 6,609,299 | 47 | 26 | 20 |
| evals | 552 | 6,329,219 | 76 | 54 | 55 |
| quasar | 57 | 498,152 | 2 | 4 | 1 |
| SWE-smith / verification / instructor | 7 | 37,206 | 0 | 0 | 1 |

**64 files carry both a `go` statement and a channel.** So real
concurrent Go is present and this is not a hypothetical corpus. But
measured against rung-0 requirements it does not yield a fixture: the
smallest stdlib-only file with both is `harbor/src/lib/gtask/pool.go` at
**1,846 bytes** — a genuinely nice artifact (goroutines, a `select` with
`default`, a stop-channel, `close`, `WaitGroup`, `Mutex`, `defer`) but a
*package*, not a program, and it pulls `context`, `sync` and `time`. The
smallest `package main` carrying both is **3,558 bytes with 16 external
imports**. A rung-0 fixture that dragged in `context` and 16 modules
would be measuring the library, not the language.

**So the driver was written**: 112 lines, **one import (`fmt`)**, 228
AST nodes, **28 distinct node kinds**.

Its concurrency profile, from the committed census: 3 `go` statements, 3
sends, 2 receive expressions, 6 channel types (3 bidirectional, 2
send-only, 1 receive-only), 1 `select` with 2 cases and a `default`, 2
`close` calls, 3 `make` calls, and a `range` over a channel.

**The design property that makes it a fixture rather than a demo** is
the split between its two observables. `sum` and `count` are invariant
under every schedule — each job contributes its square exactly once and
addition commutes — while the arrival order and the per-worker job split
are not. **Measured over 30 runs: 6 distinct per-worker job splits, one
of them `[51 49 0 0]` — two workers ran and two were starved outright —
while `count` and `sum` were identical in all 30.** That starved split is
the fixture earning its keep: the schedule space it ranges over is wide
enough to include degenerate cases, and the observable does not move. So
the program has a *deterministic observable in
spite of a nondeterministic execution*, which is exactly what makes it
differentially testable: a model quantifying over schedules can be
checked against a toolchain that samples one. A fixture whose only
observable were arrival order could not be.

**Verified, and the numbers are the whole claim:** 300 consecutive runs,
plus a `GOMAXPROCS` sweep over 1, 2, 4, 8 and 16 at 40 runs each, plus
30 runs under `go build -race` — **530 runs, byte-identical output every
time, zero race reports.** The observable `sum 338350` matches the
closed form for the sum of squares to 100.

**It was rewritten once, and the reason is a census finding rather than
taste.** The first version used `sync.WaitGroup` for the join, which is
what idiomatic Go does. §1.3 measured that the memory model's §4.9
**explicitly delegates `sync.WaitGroup`, `sync.Cond`, `sync.Map` and
`sync.Pool` to their package documentation and states no rule for
them**. A rung-0 fixture must depend only on guarantees the memory model
itself makes, or the first thing the tier models is a library contract
rather than the language. The join is now a counted receive on an
unbuffered channel — covered by channel rules 1, 3 and 4 — and the
fixture's only import is `fmt`.

### 7.2 The vocabulary curve — the census's headline

`harness/go/census.sh` was run on three corpora at three scales:

| corpus | files | lines | nodes | **distinct node kinds** |
| --- | ---: | ---: | ---: | ---: |
| the rung-0 driver | 1 | 112 | 228 | **28** |
| `src/sync` | 35 | 9,949 | 43,908 | 50 |
| **the whole standard library** | **5,419** | **1,980,087** | **8,255,321** | **52** |

And the ceiling, taken from `go/ast` itself: **`go/ast` declares exactly
56 node types** (counted as the types implementing `Pos()`). The whole
standard library exercises **52**. The four it never exercises are
`BadExpr`, `BadStmt`, `BadDecl` — the parse-error placeholders, which
this instrument refuses on rather than censusing — and the deprecated
`Package`.

**This is a categorically stronger statement than the C tier could
make.** `docs/c-tier-charter.md` §1.4 had to *argue* that its 45-kind
vocabulary was stable, by re-censusing across an engine release and
finding no new kinds. **Go's vocabulary is closed by construction**:
`go/ast` is a fixed, exhaustive, closed set of types with no extension
point, the standard library saturates it to within four error nodes, and
there is no long tail to discover. A v0 scoped to those 52 kinds is not
a bet at all.

**The driver covers 28 of the 52 — 54%** — and every kind it uses is in
the stdlib set (the driver contains nothing exotic). The 21 kinds in the
stdlib set but not the driver are the ordinary sequential remainder:
`ArrayType BranchStmt CaseClause CompositeLit Ellipsis EmptyStmt IfStmt
IndexExpr IndexListExpr InterfaceType KeyValueExpr LabeledStmt MapType
ParenExpr ReturnStmt SliceExpr StructType SwitchStmt TypeAssertExpr
TypeSpec TypeSwitchStmt`. **That list is the sequential inch ladder,
derived rather than proposed** — and it is 21 items long, not 21 rungs,
because several are one construct (`SwitchStmt`+`CaseClause`,
`TypeSwitchStmt`+`TypeAssertExpr`).

For scale, the standard library's own concurrency density, per thousand
lines: `defer` 2.48, channel types 0.86, receive expressions 0.84,
`go` statements 0.54, sends 0.50, `select` 0.23.

### 7.3 The frontend recommendation

**Recommendation: a Go extractor program using `go/ast` and `go/types`,
emitting the envelope. Not tree-sitter.** Four measured reasons:

1. **`go/ast` IS the vocabulary** (§7.2). A tree-sitter grammar is a
   *second* description of Go's syntax that must be kept in agreement
   with the real one; `go/ast` cannot disagree with the compiler because
   the compiler's own type checker is built on the sibling package.
2. **`go/types` is not optional and tree-sitter cannot supply it.** The
   census hit this directly: the instrument reports what a `range`
   ranges *over* only syntactically, because **what a `range` means
   depends on the type of its operand** — array, slice, map, string,
   channel, integer, or iterator function are seven different rules on
   the same production. §2.3's map-order obligation and §2.1's channel
   rules cannot even be *stated* without types.
3. **It already runs.** `harness/go/construct_census.go` is 499 lines of
   exactly this shape, landed and green, so the frontend path is
   demonstrated rather than proposed.
4. **The C lane's own precedent points the same way** — it uses clang's
   JSON AST rather than a re-implementation, for the same reason.

The cost is honest and stated: **the extractor is a Go program, so the
lane acquires a Go toolchain dependency** — which is why §1.1 keeps the
instrument out of `tools/ci.sh` behind `maybe`. Precedent exists:
`extractors/veriloga/` already depends on a Rust crate.

**The envelope's version field is the C lane's `profile_id`, generalized
— and Go makes it PER FILE.** `docs/c-envelope-schema.md` §2 makes
`profile_id` first-class because the profile is an input to the AST. In
Go the language version is an input to the *semantics* (§3), and it is
selected per file, so the envelope must carry `lang_version` **on every
file record, not once per unit**. The census instrument already records
it per file. This is the single place where the Go envelope must be
structurally different from C's, and §3.2's one-binary-two-semantics run
is why.

---

## 8 THE FIRST MILESTONE — planned, not started

**M1: the driver is INGESTED.** Source → envelope → Lean AST literal →
`#guard`. No semantics, no memory model, no interpreter, no schedule.
The shared prefix of every endgame, exactly as `docs/c-tier-charter.md`
§4 planned M1 for C.

The inches, in dependency order. Each separately green and separately
landable; the triad stays green at every one; none touches
`lakefile.toml`, `LeanModels.lean` or `lean-toolchain`.

1. **The census instrument and this charter — LANDED.**
   `harness/go/construct_census.go`, `harness/go/census.sh`,
   `docs/go-construct-census.json`, `Examples/go/pipeline/pipeline.go`,
   `docs/go-charter.md`, and the backlog entry.
2. **`docs/go-envelope-schema.md`** — schema `go-0.1`, mirroring
   `docs/c-envelope-schema.md`. Its vocabulary tables **derived from
   `docs/go-construct-census.json`**, never chosen, with a check that
   the listed kinds and the censused kinds cannot drift. `lang_version`
   per file (§7.3). Spans, the `Unsupported` leaf, the determinism
   contract, and the cache key `(source, extractor, lang_version)`.
3. **`extractors/go/extract.go`** — same contract as the other four
   lanes: never fails on valid Go; anything outside the pinned
   vocabulary becomes an `Unsupported` leaf naming the `go/ast` type;
   double-run byte-identical; hard errors exit non-zero and say why.
   Anchored: the C extractor is ~1,900 lines and SV's 2,495, but
   `go/ast` does the hard work, so the low end.
4. **`LeanModels/Go/Ast.lean` + `Json.lean`** — the deep-embedded AST
   for the 52 kinds and the elaboration-time ingester. **No semantics:
   this inch produces a Lean TERM and nothing evaluates it.**
5. **The driver round-tripped, with its `#guard`s.** The structural
   guards are already fixed *in advance* by the committed census, which
   is the point of landing it first: 28 node kinds, 3 `go` statements, 3
   sends, 6 channel types split 3/2/1 by direction, 1 `select` with 2
   cases and a `default`, 2 `close` calls, exactly one import. Every one
   of those is a fact the census independently knows, and each must be
   shown **non-vacuous** by flipping it and watching Lean report the
   failing expression.

**What M1 deliberately does not decide:** the endgame; whether `Run`
gains a fifth outcome shape for bounded sets (§9's decision 3); and anything about
schedules beyond §6.2's commitment that `GoWorld` carries the field.

---

## 9 DECISION POINTS — Thomas's, listed explicitly

Six, and the first is the one everything else hangs on. The charter
**recommends no endgame**, exactly as `docs/c-tier-charter.md` §3 did.

### 9.1 THE GOAL — and the census found a genuine tension in the charter itself

Thomas chartered this lane for concurrency: *"a common language for
concurrency, which is itself interesting to formalize."* §5.5 measured
that **there is no executable memory-model conformance suite anywhere in
the Go tree** — the model exists only as prose, `test/` contains zero
memory-model tests, and the nearest proxy asserts what ThreadSanitizer
reports rather than what the model permits.

So the borrowable oracle and the chartered subject **are not the same
thing**, and this charter will not paper over that. Three endgames, each
priced in what it needs and what it cannot buy:

| | **(a) sequential conformance** | **(b) the memory model, mechanized** | **(c) the versioning exemplar** |
| --- | --- | --- | --- |
| product | a definitional interpreter for Go's sequential core, differentially tested | the first executable artifact for the Go Memory Model — the three relations, the 11 marked rules plus the 3 unmarked ones, DRF-SC | one model, per-file language version, §3.3's coexistence acceptance test passing |
| oracle | **exists**: 694 `test/` cases today, 1,643 with accept/reject (§5.4), plus the 346-file spec-organized type-checker corpus (§5.8) and two shipped consumption precedents (§5.9) | **does not exist — the lane builds it** (§5.5) | the two-module runs of §3.2, already recorded |
| vocabulary | 52 closed AST kinds (§7.2); the 21-item sequential ladder is derived, not proposed | adds no syntax; adds a relation | adds one version parameter |
| buys | a second closed-vocabulary language tier, and the cheapest one the project has seen — no UB to arm (§2.5) | the thing Thomas chartered, and an artifact with no precedent — plus one concrete debt someone else would collect: Perennial's step from "SC model, no UB" to real Go currently rests on a paper DRF-SC argument (§4.5) | the family's copies-vs-deltas question, settled by an executable |
| does **not** buy | **anything about concurrency** — 250 of 2,617 cases (9.6%) touch it and they are excluded from Tier A by construction | a score, because there is nothing to score against | a language tier; it is one rule deep |
| the unpriced risk | `fmt`'s verb semantics byte-for-byte (§5.4), and `fixedbugs/` is adversarial | **the race-freedom census of §2.1 — the largest single piece of work this charter identifies, and it is not priced here** | none material; it is small |

All three share the same prefix — **the census (landed), the envelope
schema, the extractor, the ingester** — which is why §8 could plan M1
before the choice is made. **The choice binds at M2.**

One further honest note the table cannot carry: (a) and (b) are not
alternatives in sequence. §6.2 commits the schedule parameter on day
one precisely so that choosing (a) first does not foreclose (b) — that
commitment is the charter's answer to the C tier's measured warning
that concurrency is *"the one rung that is not a widening."*

### 9.2 How should the verdict system treat `select`'s specified randomness?

§2.2 measured that `select` is the **only** hedge in Go's entire
concurrency surface, and that the spec specifies a *distribution*
(*"uniform pseudo-random"*), not a free choice. Three treatments, priced
in §2.2. The charter's reading is **(3), degenerating to (1) for
verdicts** — parameterize on a choice oracle, state uniformity as a side
condition on the oracle, and score under ∀-choice. **The honest cost,
stated rather than buried: the tier will never *detect* a non-uniform
`select` implementation.** If catching that matters, treatment (2) is the
only one that can, and it breaks the one-line-per-job batch protocol.

### 9.3 How does a membership site carry its permitted set?

**This decision shrank while the charter was being written, and the
charter records that rather than hiding it.** The draft question was
"does `Run σ α` gain a fifth shape for bounded outcomes?"
`docs/family-architecture.md` §5.1 answers **no** — MATCH becomes
membership, the permitted set is a per-site datum, and the outcome type
is untouched (§6.1).

What is left is §5.1's own open fork, which it explicitly leaves to
Thomas: **the site carries its permitted set explicitly, or the
scoreboard consults a predicate the tier supplies.** Go pushes on that
choice harder than Ada does, and §2.4 is why: Go's permitted set is
**size-stratified** — one shape at or below a machine word, a strictly
wider one above it — so an explicit set is not a constant but a function
of the location's width, while a predicate absorbs the stratification
naturally. The charter notes the asymmetry and does not resolve it.

**It does not gate M1** — the ingester tier does not mention `Run` at
all, exactly as `docs/c-tier-charter.md` §2.4 measured for C. It becomes
a gate at M2.

### 9.4 Vendored versus fetched corpus

**Recommendation: fetch, pinned by the source-tarball SHA256** (§5.6).
The licence permits vendoring outright — `test/` is uniformly Go Authors
BSD-3-Clause with **zero** third-party notices, which is a materially
cleaner position than the C lane found — so this is a judgement, not a
constraint. The decisive argument is not size (1.1 MB compressed) but
**version-coupling**: 6,382 diagnostic regexps written against one
`cmd/compile` mean a vendored tree rots silently into a claim about a
compiler that is no longer present.

### 9.5 The Go toolchain dependency

§7.3 recommends a `go/ast` + `go/types` extractor, which makes a Go
toolchain a build dependency of the lane. Precedent exists —
`extractors/veriloga/` already depends on a Rust crate — and the
instrument is kept out of `tools/ci.sh` behind `maybe` for exactly this
reason (§1.1). **Confirm the dependency is acceptable**, because the
alternative (tree-sitter) cannot supply `go/types`, and §7.3 measured
that `range` alone has seven type-dependent meanings on one production.

### 9.6 Which documents does the tier promise to mirror?

The two of §1 are co-equal and both are in. But §1.3 measured that the
memory model **delegates `sync.WaitGroup`, `sync.Cond`, `sync.Map` and
`sync.Pool` to their package documentation** and states no rule for them.
That is a third tier of documents. §7.1 kept rung 0 clear of it by
rewriting the driver's join as a counted channel receive. **Whether the
lane ever chases the `sync` package's own contracts is a scope question,
not a technical one**, and it should be answered before someone models
`WaitGroup` by accident.

---

## 10 WHAT LANDED WITH THIS CHARTER

* `harness/go/construct_census.go` — the instrument, with `--compare`,
  every reachable exit path RUN (0/2/3/5), the unreachable zero-nodes
  guard labelled rather than counted, and the two `go run` traps
  recorded.
* `harness/go/census.sh` — the build-then-run wrapper that exists
  because `go run` swallows exit codes.
* `docs/go-construct-census.json` — the rung-0 corpus, machine-readable,
  double-run byte-identical.
* `Examples/go/pipeline/pipeline.go` — the rung-0 driver, verified over
  530 runs.
* `docs/go-charter.md` — this document.
* `docs/backlog.md` — the record.

**This charter carries no Lean**, and changes only `docs/backlog.md`
among existing files. But "it cannot break anything" is an argument, not
a measurement, so the triad was run.
