# The FAMILY architecture: versioned language surfaces

**Status: the family's founding charter.** Thomas chartered the repository
as a FAMILY of VERSIONED language surfaces on 2026-08-22: spec-mirrored
where a spec exists (C per edition, SystemVerilog per edition, and three
tiers founding now — WebAssembly, ECMAScript, Ada), reference-interpreter-
extracted where none does (Python per CPython minor). A user chooses the
proof target by naming a language and a version.

This document exists so that the lanes lay down the same structure — three
of them **founding** a tier from nothing (WebAssembly, ECMAScript, Ada) and
three **consolidating** one that already exists and works (SystemVerilog,
RISC-V, Verilog-A). §1.2 records which is which, because mistaking the
second for the first prices a rebuild of working code. It **constrains**;
the lanes implement. It carries **no Lean restructuring** of its own: every
ruling below is a rule the lane that next touches the code obeys.

**Everything decision-relevant here was measured.** Two instruments landed
with this charter (§11) and their outputs are cited inline; nothing is
quoted from memory, and §2's central question — copies, deltas, or
parameters — is decided by numbers rather than by taste.

**Three recorded beliefs were corrected by measurement**, which is the
best argument for the instruments existing at all:

* the C tier's own ISO citations are three-of-five an edition out of date
  (§2.5) — found by the clause instrument, in the lane founding the
  versioned layout;
* `Std.Do`'s triple/WP stack and the `mvcgen` tactic are **already present
  on the pinned toolchain** (§3.4), so the "a bump would touch every lane"
  caveat is retired rather than carried;
* **Lean's `Float` is kernel-reducible on the pinned toolchain** (§3.5),
  which is the premise three tier documents defer floats on. Core ships
  1856 lines of width-parametric IEEE 754 model, and it reduces.

---

## 0 THE DOCTRINE, and what is being unified

### 0.1 Three principles, and they govern every tier

Thomas, on what this family is for:

> *We are not saying it'll be easy to prove correctness of arbitrary
> threaded C programs. It might be really really hard or undecidable. But
> we want to make it possible to DEFINE correctness, and it's the burden of
> the prover to find a proof. We can give some tools, tactics and so on,
> but ultimately if it's too hard to prove, the program should probably be
> rewritten.*

Everything below follows from that, and the three principles are the form
it takes in this repository.

**I. THE DEFINITION IS NEVER WEAKENED FOR PROVABILITY.** The semantics'
one job is a **sound and complete definition of correctness** — ∀ schedule,
∀ evaluation order, ∀ resolution of every nondeterminism the language
admits. **Definitional completeness outranks proof convenience, always.**
If the honest definition quantifies over a space no tactic can search, the
definition still quantifies over it. Undecidability of the general problem
is **accepted at the definition layer** and is not an argument against the
definition; a semantics that narrowed its ∀ to what the current library can
discharge would be measuring the library and calling it the language. This
is the same law the tiers already obey when they REFUSE rather than invent
a rule (§4.2), stated at the level that governs all of them.

**II. THE TRUST BOUNDARY, and it is drawn tightly.** Two strata, and only
one of them is trusted:

| stratum | contents | property |
| --- | --- | --- |
| **the DEFINITION** — trusted, kept **minimal** | the interpreter, the spec citations, the verdict system | soundness and completeness are its obligations; every addition is a liability and is argued for |
| **the LIBRARY** — trusted **never**, growable **forever** | tactics, mover/commutativity lemmas, `Spec`/`@[spec]` collections, `mvcgen` integrations, altitude lemmas | **incomplete by design.** Its incompleteness is expected, published, and never hidden |

A library lemma cannot make a wrong program right, because nothing in the
library is believed — it only ever produces a proof the kernel rechecks
against the definition. That asymmetry is what lets the library grow
without bound and without review anxiety, and it is why the library's gaps
are reported as gaps rather than papered over. **This is exactly why §3.6's
proof-burden tiers — bounded-fixture exhaustion, mover lemmas, ownership
reasoning — are a LIBRARY section and not part of the semantics.** They are
three ways to find a proof of a statement whose meaning was already fixed
without reference to them.

**And the same boundary, drawn through THEOREM STATEMENTS, has a measured
price** — §8 step 9: of 949 theorems in the flagship estate, the **65%**
whose statements do not mention the interpreter recompile unchanged under a
definition swap. A lane that separates its spec half from its interpreter
half is drawing this principle's line one level down, and it is worth two
thirds of a re-founding.

The library grows **by demand**, and §5.6 gives that clause its selection
rule: the demand comes from **one theorem-worthy exemplar per tier**,
because a library gap is invisible to anything that never asks the library
for a proof — and suite scoring never does.

#### II(a) DECISION PROCEDURES — a graded policy, not a ban

Thomas's ruling: he is *not principally against* `bv_decide` and
`native_decide`. The objections are **performance** — 64- and 128-bit goals
blow up — and **informativeness**: *"a symbolic proof works for all bit
widths."* So the family **supports** these operations and **discourages
overusing** them, which is a preference ladder rather than a prohibition.

**THE PREFERENCE LADDER.**

| rung | when | why it is preferred |
| --- | --- | --- |
| **1. width-parametric SYMBOLIC proof** | the fact is true at every width | it **mirrors the spec's own generality** — the standard says "for an N-bit type", and so does the proof |
| **2. kernel `decide`** | small, fixed widths; **the inductive BASE CASE** of a width-parametric argument; any goal genuinely finite and cheap | stays inside the kernel; no extra axiom, no external oracle. Thomas: *decide can be useful for the inductive base case, but width-parametric theorems are usually desired* |
| **3. `bv_decide` / `native_decide`** | cost/benefit favors them — the symbolic proof is out of reach or disproportionate | fastest to obtain; carries the largest trust and information cost |

**Rung 1 is the spec-mirror principle applied to PROOFS**, which is why it
heads the ladder rather than merely being tidy. A tier that mirrors a
clause quantified over widths, and then proves it one width at a time, has
silently narrowed the claim its own §5.5 manifest says it makes. Both rungs
are live on the pinned toolchain and the contrast is one line each: `∀ w,
∀ x : BitVec w, x + 0#w = x` closes symbolically for **every** width, while
`bv_decide` closes the same fact at width 8 **only**.

**PERMITTED USES CARRY THEIR RECEIPT, AT THE USE SITE.** Any rung-3 use
carries (a) its `#print axioms` line and (b) a **one-line justification**
naming why rungs 1 and 2 were not taken. Both live **at the theorem**,
never in a project-wide setting: **the trust boundary is per-theorem and
visible, never ambient.** A reader auditing one theorem must be able to see
its full trust cost without leaving the file — which is principle II's
whole point, applied to the one place the library can widen what the kernel
is asked to believe.

**AND THE RECEIPT ITSELF CAN LIE — measured, with the mode pinned.**
`#print axioms` on a declaration whose **STATEMENT** failed to elaborate
prints

    'foo' does not depend on any axioms

— **the cleanest possible line, meaning the opposite of what it says.**
Reproduced on the pinned toolchain: a theorem whose statement is ill-typed
prints exactly that **even when its proof is literally `sorry`**, because
the declaration was recovered before the proof was ever checked against it.

The mode matters, so it is recorded rather than generalized. Measured, four
failure modes:

| failure | `#print axioms` says |
| --- | --- |
| unsolved goals | `[sorryAx]` — honest |
| body type error | `[sorryAx]` — honest |
| explicit `sorry` | `[sorryAx]` — honest |
| **error in the STATEMENT** | **`does not depend on any axioms`** — lies |

Three of four are honest, and **the one that lies is the most dangerous
case**: a mis-elaborated *statement* means the theorem does not say what
its author thinks, and the axiom line arrives to reassure them. So:

> **An axiom print is meaningful ONLY from a zero-error elaboration.**

**AND ROW 1 HAS NOW FIRED ON ITS OWN AUTHOR, live.**
`applyBuiltin_mono does not depend on any axioms` printed **beside a
heartbeat-timeout error in the same run** — the clean line and the failure
side by side, exactly as this row predicts, in the lane that recorded the
row. The law is not hard to believe; it is hard to *remember at the moment
the line scrolls past*, which is why it needs a machine.

**There is now a mechanical guard, so the rule upgrades:**

> **Quote `tools/check.sh --axioms`'s VERDICT LINE. A bare `#print axioms`
> is not evidence.**

That moves the check from a discipline a reader must apply to an artifact a
lane must produce — §9's whole thesis, applied to the one law most likely
to be violated by the person who wrote it.
> Every quoted axiom line is paired with the file's clean-elaboration
> status, or it is not evidence.

This is the first of three instances of §5.4a's provenance law, and the
one that reads cleanest when it lies.

This is the §5.4 instrument contract applied to the receipts themselves —
*every refusal path RUN, not admired* — and it generalizes past this
policy: any triad line, coverage count or `#guard` batch quoted from a file
that did not elaborate cleanly is quoting the error recovery, not the
tree.

**THE HISTORICAL CONTRACT STANDS AS RECORDED FACT.** `AGENTS.md` states
*"Never `sorry`, `admit`, or `native_decide` — anywhere, ever"*, and the
tree honors it: **zero real uses**, verified — all twelve occurrences of
the identifier are prose *recording its absence*. That contract is the
existing estate's and it is not weakened retroactively; **this policy
governs NEW work.** Where the two meet — a new theorem in an existing
file — the file's contract wins, because a file that advertises "no
`native_decide` appears anywhere in this tier" must stay true or stop
saying so. `AGENTS.md`'s line is owned by whoever maintains it, and
reconciling it with this ladder is that owner's edit, flagged here rather
than made silently.

**THE ALIGNMENT WORTH NAMING: SoftFloat's layer 2 IS this preference
embodied.** §3.5.1 specifies it as `round mode (exactRational …)` over a
**width-parametric** `Format` — one statement covering `binary32` and
`binary64` — rather than as per-width bit algorithms. That design was
chosen before this policy was written, which is the useful kind of
corroboration: the ladder is describing what the family already does when
it is thinking clearly.

**THE CROSSOVER TABLE HAS LANDED** — `docs/lean-structures-census.md`, and
the ladder is now an ordering *with prices* rather than an ordering alone:

| rung | measured |
| --- | --- |
| **1. symbolic, width-parametric** | **6–18 lines**, 2–3 iterations, covers **all widths**, clean axioms |
| **2. kernel `decide`** | dies around **10⁵ cases** |
| **3. `bv_decide`** | 128-bit De Morgan in **11 s** — but **TIMES OUT** on 12-bit multiplier commutativity |

**Thomas's informativeness argument is confirmed by measurement, not just
endorsed.** The parametric proof forced out a **`w = 1` edge case that no
fixed-width run could surface** (`intMin 1 = 1#1`, breaking a side
condition that holds for every `1 < w`). Rung 3 cannot find that class of
bug *in principle*: it answers about the width you asked, and the width you
did not think to ask about is exactly where the bug was. That is a
correctness argument for rung 1, not merely an elegance one.

**AND RUNG 3 IS NOT UNIFORM — the trust cost splits, verified here.**
`bv_decide` closes some goals by **normalization** and others through the
**SAT backend**, and only the second carries an axiom:

```
-- (illustrative — probes against the pinned toolchain, not tree files)
bvA (x : BitVec 8) : x + 0#8 = x                  -- normalizer
  depends on axioms: [propext]
bvB (x y : BitVec 8) : (x &&& y) = (y &&& x)      -- SAT backend
  depends on axioms: [propext, Classical.choice, Quot.sound,
                     bvB._native.bv_decide.ax_1_5]
```

Core's `nativeEqTrue` docstring names that mechanism as the basis for
**both** `native_decide` and `bv_decide` — **same mechanism, different
axiom name**. So "we use `bv_decide`, not `native_decide`" is **not** a
statement about trust; the receipts rule (above) is what distinguishes
them, and it distinguishes them per-theorem because the *same tactic* lands
on either side of the line depending on the goal.

**The fairness caveat, recorded because the distinction is real.** What
`bv_decide` evaluates is a **verified LRAT certificate checker** with a
soundness theorem — materially smaller and better-understood than bare
`native_decide` evaluating an arbitrary `Decidable` instance. The two are
the same *mechanism* and not the same *risk*, and a lane choosing rung 3
should say which of the two it means.

**III. HARDNESS IS A SIGNAL TO THE PROGRAM, not to the definition.** When a
proof will not come, the framework owes the user a next step, and there are
exactly two — both constructive, neither touching the definition:

* **(a) A counterexample is found.** Search turns up a breaking schedule,
  order or resolution, and it lands as a **kernel-checked witness** —
  §3.6's counterexample-as-artifact, a finite concrete schedule replayed by
  `#guard`. The verdict is not "unproven"; it is **the program is wrong**,
  here is the run. Fix the program.
* **(b) No witness is found AND the proof resists the library.** Then the
  program's correctness is, in the precise sense this repository can
  measure, **unarguable** — and that is information about the program.
  **Rewrite toward provability.** The discipline that says "use mutexes and
  `memory_order_seq_cst`, not hand-rolled relaxed atomics", or "structure
  your concurrency", has always been cultural advice backed by folklore.
  **This framework turns it into a formal pressure**: the DRF-SC fence
  (§3.6, piece 3) is the standard's own clause, so a program that stays
  inside it is one the tooling can actually reason about, and a program
  that leaves it has left on purpose and pays for it.

Neither exit ever weakens the definition, and a third exit — narrowing the
∀ until the theorem goes through — is **not available**. That is the whole
doctrine: the definition is the contract, the library is the help, and the
program is the variable.

### 0.2 What is being unified, and what is not

Seven language lanes exist today. Measured (`.lean` lines under
`LeanModels/`):

| lane | lines | authority | outcome type | source spans |
| --- | ---: | --- | --- | --- |
| Python | 32331 | CPython 3.9 (extraction) | **`Core.SemM`** (definition); `Run σ α` legacy, under the erosion contract | `LeanModels.Span` |
| Spice | 23366 | ngspice (extraction) | none — contracts | `Circuit.Spice.SourceSpan` |
| SystemVerilog | 8166 | IEEE 1800 (spec) + pyslang | `Sv.Res α` | none |
| Circuit | 4309 | physical law | none — enclosures | `Circuit.Spice.SourceSpan` |
| RISC-V | 2041 | RISC-V ISA (spec) | none — step relation | none |
| C | 934 | ISO/IEC 9899 (spec) + clang | `CRes α` (value layer) | `LeanModels.Span` |
| Verilog-A | 606 | OpenVAF (extraction) | none | `VerilogA.Span` |
| **Core** | **13** | — | — | — |

**`LeanModels/Core/` is 13 lines of 71 766 — 0.018% of the model tree.**
It contains one structure. That number is the honest starting point for
every claim about a "shared substrate" and it is why §3 is written the way
it is: the substrate is today an *aspiration with one instance*, and this
document's job is to make it a gated boundary instead of an accident.

**What is NOT unified, deliberately:** the Circuit and Spice lanes — the
second-largest body of Lean in the tree — do not use `Run` and are not
asked to. They model continuous state by enclosure and contract, which is
a different architecture and a correct one for their subject (§7.3).

---

## 1 THE LAYOUT CONVENTION

### 1.1 The rule

    LeanModels/<Lang>/                 -- version-NEUTRAL: what every claimed edition shares
    LeanModels/<Lang>/<Ver>/           -- version-SCOPED: what an edition decides for itself

`<Lang>` is the language's directory tag; `<Ver>` is its **edition token**.
Both come from the registry (§1.2), which is a table and not a derivation
rule, because a mangling clever enough for C and Python breaks on the
fourth language.

An edition token obeys four laws:

1. **It is a valid Lean identifier** beginning with a letter. This is not
   style: `LeanModels/Python/3.12/` is not a module name.
2. **It is self-identifying out of context.** `LeanModels/C/V23/Value.lean`
   in a stack trace tells a reader nothing; `LeanModels/C/C23/Value.lean`
   tells them everything. The stutter in `LeanModels.C.C23` is accepted as
   the price of that, and it is a good price.
3. **It names an edition a reader can hold** — a published document, or a
   released interpreter's minor line. Never a point release, a patch
   level, or a build. The C envelope already applies this rule to the
   compiler (`apple-clang-17`, the FAMILY); the Python envelope does not
   (§1.5), and the correction is overdue.
4. **It never renames.** The token appears in every envelope, every module
   path and every citation, so a rename is a tree-wide re-extraction. The
   backlog prices that event twice; do not create a third.

### 1.2 The registry

Rows marked **PROPOSED** are the founding lane's to measure and ratify;
the lane's first landed artifact is its census, and the census is what
turns the row from proposed into recorded (§8).

**`state` distinguishes the two jobs a lane can have**, and getting it
wrong mis-prices the work: *founding* builds a tier from nothing;
*consolidation* takes an existing body of Lean and gives it the family's
structure. Three of the rows below are consolidation and were nearly
mislabelled.

| language | `<Lang>` | authority | edition tokens | oracle | corpus | state |
| --- | --- | --- | --- | --- | --- | --- |
| C | `C` | spec-mirror — ISO/IEC 9899 | `C23` (now), `C17` (if claimed) | clang, pinned family + profile | `ctwin/sunfish.c`; c-testsuite; gcc torture | active — M2 |
| Python | `Python` | extraction — CPython | `Py39` (now) | CPython 3.9, pinned family | `Examples/python/**`; the stdlib sweep | active — **definition is the MONADIC interpreter**; the deep interpreter is the legacy layer under §3.4(c)'s erosion contract |
| SystemVerilog | `Sv` | spec-mirror — IEEE 1800 | `SV2017`, `SV2023` — **PROPOSED** | pyslang frontend; a simulator | **public `sv-tests`** (see below) | **CONSOLIDATION** — **8 562 lines, 106 declarations** (96 `theorem`/`lemma` + 10 `example`) **as measured at `00fe2dc`**; dormant but verified working |
| WebAssembly | `Wasm` | spec-mirror — W3C core **+ official suite** | **PROPOSED** | the reference interpreter **and the `.wast` runner** | the official `.wast` suite | founding |
| ECMAScript | `Es` | spec-mirror — ECMA-262 **+ official suite** | **PROPOSED** | an engine **and test262's harness** | test262 | founding — blocked on SoftFloat (§3.5.3) |
| Ada | `Ada` | spec-mirror — ISO/IEC 8652 **+ official suite** | **`Ada2022`** (spec head) **and `Ada2012`** (suite edition) — RATIFIED | a GNAT toolchain **and the ACATS grader** | **ACATS 4.2**, 4 188 tests | founding — **version pair FORCED** |
| RISC-V | `Rv` | spec-mirror — RISC-V ISA | **PROPOSED** | the ISA oracle | `harness/rv` | consolidation — 2 041 lines |
| Verilog-A | `VerilogA` | extraction — OpenVAF | — | OpenVAF | `Examples/verilog-a` | consolidation — 606 lines |
| SPICE | `Spice`/`Circuit` | extraction — ngspice | — | ngspice | `Examples/spice` | **in-tree LIVE / roster STAFFED 2026-08-24** — 27 675 lines, **22 `sorry`**, dormant since July, separate architecture (§6.1) |

The last three carry no edition token today. That is allowed and it is
what §1.4 rules on: **a language earns version directories when its tier
claims an edition, not before.**

**AND THIS COLUMN CONFLATED TWO DIFFERENT FACTS, which the analog tier's
staffing exposed (2026-08-24).** *"Active"* was read as one property and is two:

> **A tier can be ACTIVE IN THE TREE and DEAD IN THE ROSTER.** Code that builds,
> is imported and carries theorems is **in-tree live**; whether a lane is
> **working it** is a staffing fact, and the two move independently.

The SPICE row said **active** and was true of the **code** — 27 675 lines,
building — and false of the **staffing**: **dormant since July, 22 `sorry`s**,
nobody on it. **Both halves were honest readings of one word**, which is the
whole defect: a reader planning work needs *"is anyone on this?"*, and a reader
pricing a dependency needs *"does it build?"* — **the column answered whichever
question the reader brought.**

**The rows now carry both**, and the general rule for this registry:

> **A STATUS COLUMN NAMES WHAT IT MEASURES.** *In-tree* and *rostered* are
> separate facts; a single word that can be true of either is a word that will
> be read as both.


**AND THE FIFTH AUTHOR-BLINDNESS CASE IS THE COORDINATOR'S, ON THIS EXACT LAW,
ONE LEVEL UP** (2026-08-24, self-filed). Thomas was told **"all fourteen lanes
are live"** while **13 of 14 agents were parked and the queue was empty.**

> **"LIVE" answered whichever question the reader brought** — the coordinator
> meant *has recoverable state and a named rung*; Thomas read *is executing*.

**The same conflation as the analog roster row** (*active-in-tree* versus
*staffed*), **applied by the role that wrote the law, to the fleet.** And the
honest form is the one this register keeps arriving at — **stop compressing
independent facts into one word:**

> **"N lanes with assigned rungs; M executing; K building."**

**Three numbers, because there are three facts**, and every pair of them can
differ: a lane can hold a rung and not be running, run without building, and
build without holding a rung anyone has read. *A single word covering three
states is not a summary, it is a choice made on the reader's behalf without
telling them.*

**FIVE CASES IN FOUR DAYS NOW**, and they no longer read as coincidence: the
heading guard convicting §9.5a's author; the enforcing lane minting
owner-namespace ids; **this document's §9.0 requirement producing three
malformed headings**; a lane violating a law inside the commit that landed it;
and now **the coordinating role committing the unit defect it had just
circulated.** *Writing a law is the moment of maximum confidence and minimum
habit* — and **the role that dispatches laws writes more of them than anyone,
so it is the most exposed, not the least.**

This is the unit family (§5.4a) arriving in a table's **vocabulary** rather than
in a count — and it has the same tell: **the word looked like a property of the
tier, and it was a property of a question.**

**ADA IS THE FIRST TIER TO DECLARE TWO EDITION TOKENS AT FOUNDING, and it
did not choose to.** The ARM is **Ada 2022**; the official suite's baseline
is **ACATS 4.2**, which states in its own modification list that it covers
**Ada 2012**, and no 5.x exists. So the suite is two editions behind the
standard, and **a "conforms to Ada 2022" claim can never be scored against
the official corpus** — any Ada-2022-only feature is outside it by
construction. The version sibling this document asks for is therefore
forced: `Ada2012` is what can be scored, `Ada2022` is the spec-side head.

That is **the exact inverse of the C tier's shape**, where the standard
moved and the suites followed. Here the *suite* is the pinned artifact and
the *spec* is the moving one — and the family's layout convention has to
work in both directions, which §1.1's four laws do without amendment
(`LeanModels/Ada/Ada2012/` says exactly what it is). Ada is also the
validation of §1.4's "pay the directory level early" ruling: a tier that
must carry two editions from its first commit has no cheap moment to add
the level later.

**The SV row was corrected twice, and both corrections generalize.**

*The corpus.* This document first named **sv-tests-2** as the SV corpus,
copying `docs/sv-corpus-coverage.md`. It cannot stand: that corpus sits in
a clone with **no license**, 21 631 files, and an **embedded IEEE 1800-2023
PDF** — 9.4 MB of vendored IEEE text, against this repository's own
no-vendoring law (§2.1, §11) — and its provenance names a private
organization, which the no-private-hostnames rule covers. The clean anchor
is the **public `sv-tests`**: uniform ISC, per-file SPDX, `tests/**` only
(`generated/` reaches GPL ivtest), and **already clause-mirrored** — 326
clause tags against a 482-clause LRM dictionary, which is a coverage-by-
clause manifest (§5.5) that already exists and did not have to be built.
**Whether sv-tests-2 may be used at all is an open Thomas decision** and
nothing should depend on it meanwhile.

Two family rules fall out. **A corpus's LICENSE and PROVENANCE are part of
its registry row, not a detail discovered later** — the C tier learned this
when reading 219 `.otag` files split c-testsuite into ISC and LGPL halves,
and the founding checklist (§8) now carries it at step 0. And **a corpus
that vendors the standard it tests against is disqualified by our own
law**, however convenient it is.

*The consolidation order.* The SV lane is §2.4's pattern applied a second
time, and it should run in the pattern's order: **census the IEEE
1800-2017 → 2023 delta FIRST**, then let the numbers place the files. The
expectation, recorded before the measurement so it can be wrong, is a
**thick trunk** with 2023's additions in a thin `SV2023/` that does not
disturb it — the same shape C measured at 933 trunk lines of 934.

*The maturity.* The SV tier is **not greenfield**: `LeanModels/Sv/` is
**8 166 lines** (measured) with a differential harness recorded green
against Icarus, dormant rather than absent. Labelling it "founding" would
have priced a rebuild of work that exists and passes.

**Its theorem count is SETTLED at 98, and adopted because it was
REPRODUCED.** The SV charter states the rule — `theorem`/`lemma`
declarations plus `example`s — and under that rule this document counts
**93 + 5 = 98 exactly**. The earlier disagreement was never about the tree:
93 was the same measurement under a narrower rule that omitted the five
`example`s. A number is adopted here when a second rule reproduces it, not
when a neighbour asserts it.

**AND THE ROW NOW CARRIES ITS STATE STAMP, because it drifted — this
document violating its own provenance law.** *"Settled at 98"* was true at
`8f4fd65` (8 166 lines, 93 + 5) and is false at `00fe2dc` (**8 562 lines,
96 + 10 = 106**). A derivable number written without the revision it was
derived at is **a measurement with its state stripped off** (§5.4a), and
the fix is the stamp rather than the refresh: **a stamped stale number is
readable; an unstamped current one rots silently.** The counts belong in a
`--check` mode so the registry **drifts loudly** rather than being
re-noticed by an audit.

**FIVE STANDING VIOLATIONS, not one — this row was understated and is
corrected.** It previously named a single file, which is exactly the
error §5.4a warns about: **the instance that was noticed reported as the
population.** The one-grep answer
(`grep -rl '/Users/ahle\|/home/thomas-ahle' docs/`) finds live private
paths in **five** documents:

| file | what it is |
| --- | --- |
| `docs/sv-construct-census.json:5` | **the worst of the five** — `"corpus_path"`, a **committed machine-readable provenance field**, not prose |
| `docs/sv-charter.md:189` | a `DEFAULT_CORPUS` constant |
| `docs/sv-corpus-coverage.md:5` | the corpus path originally flagged |
| `docs/litreview/area-c-isa-models.md:9,213` | checkout paths |
| `docs/howto/add-a-spec-to-existing-code.md:159` | a working directory inside quoted output |

**The census JSON is the one that matters most**, because a provenance
field is *read by tools and copied forward*, where prose is only read by
people. **A repo-wide private-path grep belongs in `tools/check.sh`** so
the redaction is complete by construction rather than by whoever
last looked — which is this document's own §9 thesis applied to a rule it
was content to state in prose.

### 1.3 The version-neutral boundary, stated per language

The neutral layer is the **measured INTERSECTION** of the editions the
tier claims. It is not "the oldest edition" and it is not "the part that
felt general". It is a claim with an instrument behind it, and when the
claim stops holding the construct moves down.

This is the trunk of §2.4's **thin siblings over a thick shared trunk**,
and the placement rule is that section's first clause: **a file moves into
a sibling only when a measurement convicts it.** The default is the trunk,
and the burden of proof is on the sibling.

**C — measured.** `LeanModels/C/{Ast,Json,Load}.lean` are version-neutral,
and the evidence is `docs/c-construct-census.json`: **zero of the 45 AST
node kinds the tier ingests is post-C99.** The censused vocabulary is
`BinaryOperator`, `CompoundStmt`, `DeclStmt`, `ForStmt`, … — the C89/C99
core, with no `_BitInt`, no `GenericSelectionExpr`, no `StaticAssertDecl`,
no attribute node. A C17 surface would ingest the same 45 kinds through
the same ingester.

`LeanModels/C/Value.lean` is version-SCOPED, and the evidence is **one or
two lines, and the line is `IntTy.minVal`.**

C23 §6.2.6.2p2 fixes the sign bit's value: *if the sign bit is one, it has
value −(2^(N−1))* — a single stated value, which is two's complement. C17
§6.2.6.2p2 instead offers **three** representations — sign-and-magnitude,
two's complement, ones' complement — and says *"which of these applies is
implementation-defined."* So `INT_MIN` is `-(2^31)` in C23 and one of two
values in C17, and **`minVal` is the definition that differs.** The
confirming change-history note is §6.2.6.2p6 NOTE 2, which names the
representation and records that prior editions allowed others; the
**normative** mandate is p2, and the distinction matters here for the same
reason it matters in §3.6 — a NOTE is informative, and a tier that cited
one as normative would be overclaiming.

The auditable trace is in Annex J: **C17's implementation-defined integers
list has FIVE entries and C23's has FOUR**, and the deleted one is exactly
*"whether signed integer types are represented using sign and magnitude,
two's complement, or ones' complement …"* (C17 J.3.5; C23's list is J.3.6,
itself renumbered and item-numbered per §2.1).

**CORRECTION — this section previously cited `convert` and §6.3.1.3, and
that was wrong.** §6.3.1.3p3 is **word-for-word identical** in C17 and
C23 — *"either the result is implementation-defined or an
implementation-defined signal is raised"* — and **C23 J.3.6 item (3) still
lists it** as implementation-defined. Out-of-range unsigned→signed
conversion is therefore **not** C23-mandated; it is profile-pinned
(`uint_to_int_wraps`) in every edition, which is where `docs/c-profile.md`
already had it. The error was inherited from the tree's own prose and then
appeared to be confirmed by this charter's instrument, which reported
clause 6.3.1.3 as *changed* at ratio 0.989 — but that change is `_Bool` →
`bool` in p1 and a footnote renumbering, not p3. **A similarity ratio says
a clause MOVED; it never says WHAT moved.** That is the precise failure
mode §5.5's clause manifest exists to prevent, and it caught the author of
§5.5. Found and corrected by the C M2 lane; verified here against both
drafts before being propagated.

**The conclusion survives the evidence swap**, which is why it is worth
stating twice: 933 of 934 lines are common to both editions, and the
version-scoped part of the C value tier is one definition — just a
different one.

**Python — measured.** The AST tier, the ingester, the interpreter and the
whole proof layer are neutral across 3.9→3.14 on everything the corpus
reaches (§2.3): 1458 rows, **100.00% value-identical**. What is version-
scoped is the **error-message surface**, and it is scoped more deeply than
a string table: `PyErr` encodes zero-division as *two* nullary
constructors because CPython 3.9 has exactly two texts; 3.11 and 3.12
split it *three* ways. A 3.11 surface needs a different constructor
ARITY. So `PyErr` and `errMessage` are version-scoped; `Semantics.lean`,
`Runtime.lean` and the VC layer are neutral.

**Every other lane: state the boundary before writing the second
edition's first line.** The boundary is cheap to draw while the scoped
part is small and expensive afterwards, which is the same argument that
put C's effective types in at zero sites.

### 1.4 The C lane's `LeanModels/C/C23/` — RATIFIED, with one refinement

The C lane is adopting `LeanModels/C/C23/`. **Ratified**, for three
reasons, and refined in one.

*Ratified because the naming IS the claim.* A tier that models C23 and
says only `LeanModels/C/` claims all of C. §2.1 measures that C23 and C17
share 21.4% of their substantive clause text; a directory that declines to
say which one it means is making a claim it cannot support.

*Ratified because the level is free now and costly later.* Adding it after
M2 is a rename of every module in the lane, and law 4 above exists because
the backlog prices that event twice.

*Ratified because `C23/` fills up fast.* It holds one file today. M2's
inches 2–5 — memory model, expression semantics, statements, calls — are
all rules an edition decides, so within the priced ~15–20 sessions
`C23/` holds most of the tier.

**REFINEMENT: only the version-scoped files move.** `Ast.lean`,
`Json.lean` and `Load.lean` stay at `LeanModels/C/`, because the census
measured their vocabulary neutral (§1.3) and moving them would assert an
edition-dependence that does not exist. `Value.lean` moves to
`LeanModels/C/C23/`. The C lane implements; this document does not.

**IMPLEMENTED, and independently confirmed.** The C M2 lane has taken this
layout, and in doing so verified §2.1's renumbering result and this
section's split from their own reading of the drafts rather than from this
document. Two lanes reaching the same clause facts by different routes is
the only kind of confirmation worth having — and the same exchange
corrected §1.3's evidence, which is the other kind.

### 1.5 `language_version` becomes a first-class envelope field

**Measured defect: no envelope in the family carries the language version
as a field.** Read off the tree:

| lane | where the language version lives today | verdict |
| --- | --- | --- |
| Python | `frontend.version: "3.9.19"` | the INTERPRETER's point release, conflated with the language edition |
| C | `profile_flags[0] == "-std=c23"` | a substring of a flag list; an ingester must string-parse to ask "which C?" |
| SystemVerilog | nowhere | the lane cites IEEE 1800-**2017** for operator semantics (`docs/sv-design-m0.md`) and censuses the IEEE 1800-**2023** conformance corpus (`docs/sv-corpus-coverage.md`) |

The SV row is the failure mode in the wild: one lane, two editions, no
field that says so, and nothing that could have noticed.

**Ruling.** Every envelope gains

    "language_version": "<the registry's edition token>"

as a first-class top-level field, next to `language`. Its value is the
same string that names the directory, so path, envelope and citation
cannot drift. The ingester REFUSES a mismatch, exactly as
`load_c_program` already refuses a `profile_id` mismatch — an envelope
from another edition is a different program.

`frontend.version` keeps its own job and its own correction: it is the
FRONTEND's family (`apple-clang-17`, `cpython-3.9`), never a point
release. That rule is recorded twice in `docs/backlog.md` and cost 53
files of re-extraction the second time; the Python envelope still carries
`3.9.19` and should carry the family.

Schema versions (`0.1`, `sv-0.1`, `c-0.1`) are unaffected. They version
the ENVELOPE FORMAT and are orthogonal to the language edition; conflating
the two is the mistake this field prevents.

### 1.6 The other four surfaces

The convention is not only about `LeanModels/`. Four more directories
carry the family pattern, and the rules differ because their subjects do.

* **`extractors/<lang>/extract.py` — ONE extractor per language, never per
  edition.** The frontend is a single tool that takes an edition switch:
  clang takes `-std=`, CPython is the binary you invoke. `extractors/c/
  extract.py` already hard-codes `PROFILE_FLAGS = ["-std=c23", …]`; that
  constant becomes a parameter, and the extractor stamps the resulting
  `language_version` into the envelope.
* **`Examples/<lang>/<name>/` — the corpus is NOT versioned by path.** The
  same `.c` extracts under two editions; the envelope's
  `language_version` says which one this artifact is. A second edition's
  envelope of the same source sits beside the first under a name that
  carries the token.
* **`docs/<lang>-*.md` — keep the existing convention** (`c-*`, `sv-*`,
  `spice-*`, `rv-*`). Add `<lang>-<ver>-*.md` only for a document that is
  genuinely edition-specific; a census of a corpus is, a design of a
  memory model usually is not.
* **`harness/<lang>_<subject>_census.py` — instruments live in
  `harness/`.** One exception exists and is a defect to fix when the SV
  lane is next open: `extractors/sv/census.py` is an instrument living in
  the extractor tree. Extractors extract; instruments measure.

---

## 2 COPIES, DELTAS, OR PARAMETERS — decided by measurement

Two censuses landed with this charter, one per authority style. They
disagree about the *documents* and agree about the *models*, and that
disagreement is the whole architecture.

### 2.1 The C17 → C23 clause census

`clause_delta.py`, run on the two public working drafts (N2310 for C17,
N3220 for C23). **No ISO text is reproduced anywhere in this repository**
— the instrument emits clause numbers, clause TITLES and similarity
ratios, and nothing else.

*Method, because the first answer it gave was wrong.* Matching clauses by
NUMBER measures the renumbering, not the change: C23 shifted 6.5.4 onward
by one, so C17's `6.5.7 Bitwise shift operators` is C23's `6.5.8`, and
C17's `5.1.2.3 Program execution` is C23's `5.1.2.4 Program semantics`.
Both were verified by direct grep of the drafts, independently of the
parser. The instrument therefore matches on the **ancestor-title path**,
with a rescue pass by (top-level number, own title) for clauses whose
PARENT was retitled. Two PDF renderings never produce byte-identical text,
so identity is reported at a ratio threshold of 0.995 with exact equality
reported separately as a floor; clauses whose body is a heading over
subclauses are flagged `thin` and excluded from ratio statistics. The
instrument refuses loudly on a missing input, a zero-clause parse, or an
implausible count, and its output is byte-identical on a re-run.

**Headline.**

| quantity | value |
| --- | ---: |
| body clauses located — C17 (N2310) | 996 |
| body clauses located — C23 (N3220) | 1267 |
| matched across the two editions | 933 |
| …of which substantive (excluding heading-only `thin` rows) | 679 |
| **identical, ratio ≥ 0.995** | **145 of 679 — 21.4%** |
| changed | 534 |
| added in C23 | 334 |
| removed | 63 |
| **renumbered — same clause, different number** | **612 of 933 — 65.6%** |

Similarity buckets over all matched rows: ≥0.995 — 282; 0.95–0.995 — 145;
0.80–0.95 — 148; <0.80 — 358. Normalizing away cross-references and
footnote numbers, which the renumbering moved wholesale, shifts identity
only from 27.9% to 31.0% of matched rows: **the churn is real edits, not
citation drift.**

**By subtree — the language clauses the C tier models.**

| subtree | total | identical | changed | added | removed |
| --- | ---: | ---: | ---: | ---: | ---: |
| 5.1.2.3 program execution (sequencing) | 6 | 2 | 2 | 1 | 1 |
| 6.2.1–6.2.4 scope / linkage / storage duration | 6 | 0 | 2 | 2 | 2 |
| 6.2.5 types | 1 | 0 | 1 | 0 | 0 |
| 6.3 conversions | 15 | 4 | 10 | 1 | 0 |
| 6.5 expressions and operators | 34 | 3 | 26 | 4 | 1 |
| 6.6 constant expressions | 1 | 0 | 1 | 0 | 0 |
| 6.7 declarations | 38 | 0 | 19 | 18 | 1 |
| 6.8 statements | 20 | 3 | 13 | 4 | 0 |
| 6.10 preprocessing directives | 26 | 1 | 16 | 8 | 1 |
| J.3 implementation-defined behavior | 16 | 0 | 13 | 2 | 1 |

**Spot-checked, five clauses, before the table was believed.** 6.3.1.3
*Signed and unsigned integers* — ratio **0.989**, a small targeted edit.
**A spot-check that was itself over-read**, and the lesson is recorded in
§1.3: the 0.989 is `_Bool` → `bool` in p1 plus a footnote renumbering, and
this document originally read it as C23's two's-complement mandate. It is
not — p3 is word-for-word identical across the editions. **A ratio locates
a change; only reading the clause identifies it.** 6.2.5
*Types* — **0.245**, large, as predicted. C17 6.5.3 → C23 6.5.4 *Unary
operators* — **0.986**, the near-unchanged control. C17 6.5.7 → C23 6.5.8
*Bitwise shift operators* — **0.310**. `7.13.2.1 The longjmp function` —
**0.776**, matched by the title rescue because its parent was retitled;
without the rescue pass the instrument reported it REMOVED, which is the
defect the rescue pass exists to fix and it was found by spot-checking.

**Annex J.2 — the refusal taxonomy's own delta.** The enumerated
undefined-behavior list runs **211 items in C17 and 221 in C23**. Matched
modulo the trailing clause citation (which the renumbering moved): **171
identical, 40 only in C17, 50 only in C23.** So 77% of C23's UB list is
carried over, and a fifth of it is new. One presentational change is
load-bearing for a tier whose refusal causes are J.2-shaped: **C23
NUMBERED the items** — `(1)`, `(2)`, … — where C17's are unnumbered
bullets. A C23 refusal can cite a UB item by number; a C17 refusal cannot.

### 2.2 The C model's own delta — and it is one line

Against 21.4% clause-level identity, the tier that mirrors those clauses
measures:

* **0 of 45** ingested AST node kinds are edition-specific (§1.3).
* **1 of 11** value-layer definitions is edition-sensitive — `IntTy.minVal`,
  because C23 §6.2.6.2p2 fixes the sign bit's value where C17 §6.2.6.2p2
  left the choice among three representations implementation-defined
  (§1.3, which also records the wrong answer this bullet used to give).
* **933 of 934** lines of `LeanModels/C/` are common to C17 and C23.

**These two measurements are not in conflict and confusing them is the
error this section exists to prevent.** The standard changed enormously;
the modeled fragment did not. C23's edits landed in declarations (6.7: 18
new subclauses, 0 identical), preprocessing (6.10: 8 new, 1 identical) and
the library — and the tier models a 45-kind C89-era vocabulary that C23
left almost alone. **The delta that prices the architecture is the delta
over the CLAIMED CLAUSES, never the delta over the document**, and it can
only be known by an instrument that knows which clauses are claimed. That
instrument is the clause manifest (§5.5), and this measurement is the
reason it is not optional.

### 2.3 The CPython 3.9 → 3.12 census

Two instruments, on the two surfaces the repo already gates.

**Behavior — the differential corpus, run under four interpreters.** 1458
rows (1394 expanded `cases.json` calls plus the 65 whole-program scripts)
executed under CPython 3.9.19 / 3.11.11 / 3.12.8 / 3.14.5, deterministic
across two full runs (identical output sha256), one ERROR row reported and
not dropped (a corpus function that returns the real wall clock, and is
therefore nondeterministic under every interpreter).

| | measurable | value-identical | message-identical |
| --- | ---: | ---: | ---: |
| 3.9 → 3.12 | 1458 | **1458 — 100.00%** | 1427 — 97.87% |
| 3.9 → 3.14 | 1458 | **1458 — 100.00%** | 1399 — 95.95% |

**Not one value semantic changed.** Zero rows changed a returned value, an
exception class, a stdout byte or an exit code at any step. All 59 deltas
are exception MESSAGE TEXT, in eight named buckets — zero-division
rewordings 17, builtin-message rewordings 10, qualified callable names 9,
unbound-variable rewordings 9, unhashable rewordings 8, attribute-error
suffixes 3, recursion-limit messages 2, and one "Did you mean:" suffix.

**Grammar — the `ast` module, per version.** The instrument re-derives
`docs/completeness.md` §2's counts on 3.9 exactly (25 statements, 27
expressions, 13 binary, 4 unary, 10 comparison, 2 boolean operators),
which is its validation.

| sort | 3.9 | 3.11 | 3.12 | 3.14 |
| --- | ---: | ---: | ---: | ---: |
| `stmt` | 25 | 27 | 28 | 28 |
| `expr` | 27 | 27 | 27 | 29 |
| `operator` / `unaryop` / `cmpop` / `boolop` | 13/4/10/2 | 13/4/10/2 | 13/4/10/2 | 13/4/10/2 |
| `pattern` | 0 | 8 | 8 | 8 |
| `type_param` | 0 | 0 | 3 | 3 |

Cumulative 3.9 → 3.12: **+17 node classes, −0, 3 field changes**; of the
113 classes present in both, **110 have byte-identical `_fields` — 97.3%**.
The three that moved each gained one optional field
(`FunctionDef`/`AsyncFunctionDef`/`ClassDef` gained `type_params`). **The
entire operator grammar is frozen across all four versions**, and the
expression grammar is frozen from 3.9 to 3.12.

**Corpus reach, stated honestly.** 121 corpus files touch 72 of the 81
census productions — 88.9%. So 100.00% value-identity is evidence about
*that* 89%, exercised 1458 times. It says nothing about `async`, `with`,
dict/set comprehensions, or — necessarily — about `match`, `TryStar`,
`TypeAlias` and t-strings, which cannot be evidenced by a corpus written
for 3.9.

**The finding that decides §2.4.** `PyErr` encodes zero-division as two
nullary constructors, with a docstring arguing that the split costs the
spec surface nothing — true, because CPython 3.9 has exactly two texts.
Measured: **3.11 and 3.12 split it three ways**, and 3.14 collapses it to
two rewritten ones. A 3.11 surface therefore needs a different
**constructor arity**, not a different string.

### 2.4 THE RULING: THIN SIBLINGS OVER A THICK SHARED TRUNK

**Mechanism: the measured INTERSECTION lives once, in the version-neutral
layer; everything an edition decides lives WHOLE in that edition's own
directory. Editions are siblings. Neither is the base of the other, and
no definition takes a version parameter.**

**MEAS-28 HAS A GATE NOW: `tools/dupes.sh`.** This is the one law in the tree
that literally asks for a tool, and it had none —
`docs/duplication-audit.md` measured the census contract implemented **14
times** by hand, every ten landings, and by hand is what the law forbids. The
instrument reports two channels, because each misses what the other catches:
**CONTRACTS** (curated shapes — a `git_rev` helper, a `--compare` path) and
**repeated `def` NAMES** (mechanical, so it finds what the curated list
forgot). First run, 2026-08-23, over 39 Python files: `--compare` **15**,
`census` **15**, `double-run` **10**, `self-test` **10**, `git_rev` **8**.

The two channels earn their keep on that last row: the contract channel finds
**8** files running `git rev-parse`, the name channel finds **3** called
`def git_rev` — so **five implement the contract under another name**, which
is precisely the duplication a name-based rule misses and a contract-based one
catches.

A duplicate is not automatically a violation: §9.2 consolidates **by touch**,
so a contract with no shared helper landed is `DUPLICATED` (work available)
and one whose helper exists unused is `VIOLATION` (work refused). And the
honesty clause is in the tool's header: **it cannot see semantic duplication
under different spellings**, so every count is a floor.

**AND ONE CLASS OF DUPLICATE IS FOUND BY THE COMPILER, NOT BY AN INSTRUMENT**
(Go §G23, `9a6d6ad`). `bitLenSpec` existed **twice** — in `Packages.lean` and in
the example's local copy — and **Lean's ambiguity error found it.**

> **A DUPLICATED SPECIFICATION IS FOUND BY THE NAMESPACE, NOT BY REVIEW.**

**Worth recording because it is the cheap corner of MEAS-28's problem.**
`dupes.sh` exists because most duplication is **invisible to the language**:
different names, different files, same contract. But a duplicate that shares a
**name in a shared namespace** is caught by the elaborator for free — so the
instrument's real subject is *duplication the compiler cannot see*, and a lane
should not build a census for the half that reports itself.

**AND THE REPAIR DID MORE THAN DEDUPLICATE: it made a proved theorem
LOAD-BEARING.** With one definition, **`Len64`'s model IS definitionally what
§G15 proved** — the package model and the proved spec are now the same object
rather than two objects a lemma relates.

> **The best outcome of removing a duplicate is not tidiness; it is that a
> theorem stops being ABOUT the model and starts being TRUE OF it.**

**AND THE CONSTRUCTIVE DUAL, from Ada inch 2: WHERE DUPLICATION IS TEMPTING, PIN
BY `rfl`.** The statement layer's `applyArith` is tied to inch 1's ops by **five
`rfl` pins** —

> **so it is not a second implementation that agrees.**

**The distinction is the whole of it.** Two definitions that **agree** are two
definitions, and agreement is a fact that must be **re-established every time
either moves**. Two definitions tied by `rfl` are **one definition wearing two
names**, and the tie is checked by the elaborator on every build **at no
recurring cost.**

**So MEAS-28's rule has a second discharge.** Duplication is retired either by
**removing one copy** — the usual reading — or by **pinning the copies together
definitionally**, which is available exactly when the second copy exists for a
presentational reason the tier actually needs. **A lane that cannot delete the
duplicate can still refuse to let it drift.**



**AND THE GATE HAS PRODUCED ITS FIRST CONSOLIDATION: `tools/leanlex.sh`, the
Lean lexing primitives ONCE** (`12386db`). Four tools had grown — or were about
to grow — the same comment walker, and the 2026-08-23 audit found **three
separate defects that all reduce to "this matcher does not know what a
comment is"**. The primitive now has one home (`lean_code_lines`,
`lean_decl_blocks`, `lean_names_both`), sourced rather than executed.

**Counted precisely, because MEAS-28's own scoreboard is what this is about,
and the dispatch that reached this lane over-stated it.** *Four private copies
retired* is not what happened and would make the gate's next count wrong:

* **two copies were never grown** — `substrate.sh` needed a third and a fourth
  and sourced the shared file instead. **That is the consolidation.**
* **two copies are still live** — `sites.sh`'s `code_hits` and `triad.sh`'s
  `code_mentions`, the latter's own comment naming itself *"third copy of the
  comment walker in this tree"*. They retire **BY TOUCH** (§9.2), which is this
  document's own rule and not a shortfall.

**So the honest figure is two avoided and two owed**, and the reason to state
it that way is MEAS-28: a duplication law policed by an instrument is worth
exactly as much as the count it publishes, and a lane that reports the
consolidation it *intends* rather than the one it *made* has put a wrong number
into the gate's own ledger — §5.4a's published-number trap, one level up from
where it was measured.

**The pattern has a name so that tiers apply it uniformly: THIN SIBLINGS
OVER A THICK SHARED TRUNK.** The trunk is `LeanModels/<Lang>/`; the
siblings are `LeanModels/<Lang>/<Ver>/`, and they should be **small** —
if a sibling is thick, either the editions really do differ that much
(measure and prove it) or the census was not run. Three clauses make it
operational.

**STMT-59 AND STMT-60 HAVE A GATE: `tools/editions.sh`.** First run,
2026-08-23 — and it convicts this section's own tier. **`LeanModels/C/C23/` is
2213 lines against a 732-line trunk: a ratio of 3.02**, which is the inverse of
*thin siblings over a thick shared trunk*, and **no census names its files**
(a C construct census exists; §2.4(1) asks for a measurement convicting the
FILE). STMT-60 is clean: **zero violations**, with Go's
`perIterationLoopVars (v : LangVersion) : Bool` correctly reported as **clause
(4)'s legitimate case** — a predicate classifying per-file version DATA, not a
semantics parameterised by edition. The discriminator is the RETURN type, and
the tool prints the list so a lane disputes the list rather than the verdict.

**STMT-61 is measurable but has nothing to measure.** Clause (2) says theorems
prove once on the trunk; a duplicate-statement finder across trunk and sibling
would report **zero forever**, because the C trunk holds **0 theorems** and its
C23 sibling holds **7**. The failure mode in this tree is not *"proved twice"*
— it is **"proved only in the sibling"**, so the theorem split is reported as a
column (`7/0`) rather than built as a comparison that cannot fire.

**(1) CENSUS-GATED PLACEMENT. A file enters a sibling directory only when a
MEASUREMENT convicts it of edition-sensitivity — never prophylactically.**
The C tier supplies *both* halves of the precedent, and the failed half is
the more instructive one. This document originally convicted `convert` of
being C23-mandated; had that been acted on, a file would have moved into
`C23/` **for nothing**, since §6.3.1.3p3 is word-for-word identical across
the editions (§1.3). The verified conviction — `IntTy.minVal`, on C23
§6.2.6.2p2 — moves **exactly one definition**, and **933 of 934 lines stay
in the trunk**. Prophylactic siblings are how a thick trunk silently
becomes two thin ones.

**(1a) AND THE COMPANION MEASUREMENT FOR THE OPPOSITE MOVE — PLACING TWO THINGS
SIDE BY SIDE.** Clause (1) prices *separating*; this prices *joining*, and the
unit is the same one lanes forget: **the import closure**. From the fuelMono
lane (**LANDED**, `6b91a8d`, on master — the conditional stamp this paragraph
carried is discharged):

> **A SHARED NAME IS WORTH AN IMPORT; IT IS NOT WORTH RELOCATING THE TRUNK'S
> ELABORATION COST. Check whose CLOSURE a file sits in before deciding two
> things belong side by side.**

Measured: the instances landed in `Outcome` §8 rather than beside `FlatLe`,
because the tidier-looking placement **dragged `Std.Do` into 65 `Examples`
closures**. Nothing would have failed — every one of those files would still
build — and that is the whole hazard: **a placement decision made on naming
grounds pays in elaboration time across every downstream file, and the bill
arrives on lanes that never made the decision.**

The practical form is a grep, not a judgment call: **before moving a
definition next to a name it shares, list who imports the destination** and
ask whether the destination's own imports belong in all of those closures. It
is MEAS-1 (*census before pricing*) applied to a decision that does not look
like it has a price.

**(2) THEOREMS PROVE ONCE ON THE TRUNK** and serve every edition that
imports it. A sibling carries a theorem only when the FACT it states is
edition-decided. This is where the pattern pays: the expensive artifact in
this repository is not the definition but the proof estate, and a trunk
theorem is proved once for all editions rather than re-proved per sibling.

**THE MEASURED COST OF GETTING THIS SPLIT WRONG — three independent
re-derivations of one payload.** A trunk that is POORER than its adopters
need does not stay poor: **each adopter rebuilds the missing payload
locally, in string form, plus a parser to recover it.** Measured, three
tiers, none of them talking to each other:

| tier | what it rebuilt |
| --- | --- |
| **C** | the refusal snapshot (`Option Mem`) |
| **ES** | the refusal cause (`EsRefusal`) |
| **Go** | **its own four-class `RefusalCause`** — whose tag is **byte-identical to Core's `className`** — flattened with the clause into a **prose prefix for a scoreboard to parse back out** |

**Three is the family's own evidence bar** (§9.3 ratified the span field
names on exactly this standard), and what it convicts here is not the
tiers: it is **the trunk**. Go's version is the sharpest, because it
re-derives a name Core *already has* and then **encodes structure into a
string so a consumer can decode it** — a round trip that exists only
because the typed field does not.

> **A thin sibling is cheap. A trunk too poor for its siblings is not — it
> is paid for N times, in string-building and re-parsing, by lanes that
> never see each other's version.**

**RESOLVED — Go retired its local type, and reading the cause as DATA
bought something a string could not.** With `Core`'s payload landed, Go
dropped its own `RefusalCause` and its gate became
`(r.toCore π).isUndefined = false`, proved by `cases r <;> rfl` against
**`Core.isUndefined` — a predicate lifted from ES.** The division that
emerged is the one this section argued for:

> **The lane contributes the NARROWER TYPE; the PREDICATE is everyone's.**

And the payoff is concrete rather than aesthetic: **two guard shapes a
string could not express** — a **cited clause that is checkable**, and
**`isUndefined` per refusal**. That retires the three-re-derivations entry
as a diagnosis and settles it as a result: the string encodings were not
merely inelegant duplication, they were **lossy**, and the loss is
recoverable only by carrying the cause as data.

**AND THE EXACT COUNTERPOINT, which is why the diagnosis is the trunk's
PAYLOAD and not its CLASSES.** SV's own §2.4 taxonomy predicted it would
need a class for scheduling nondeterminism — and found
**`RefusalCause.orderDependence` already in `Core`**, arrived from ES, Go
and Python **without SV asking**. So:

* the **classes** were reached independently **from four directions** and
  agreed — §9.3's convergence standard, at its strongest showing yet;
* the **payload** was re-derived independently **three times** and each
  tier built a different string encoding.

**Convergence validated the taxonomy at the same time re-derivation
convicted the type.** That is a useful pair to hold: §5.2's four classes
were right while `Core`'s `Loud` was wrong, and a lane reading only the
three re-derivations might have concluded the whole design needed
revisiting. It did not — **one field did.**

That is the direct cost of the gap §3.4 records, and it is why the fix
belongs in `Core` rather than in any adopter.

**(3) THE ONE HONEST FORK — stated as a boundary so nobody engineers around
it.** When a shared DATATYPE changes SHAPE between editions, the type and
its consumers **must** fork. The measured instance is `PyErr`: 3.9 encodes
zero-division as two nullary constructors, 3.11 splits it three ways, and
that is a change of ARITY, not of a value. No sharing mechanism is sound
there — a delta layer cannot override a constructor list, and a version
parameter would infect every consumer's type. **Duplication is correct
exactly where no sharing mechanism is sound**, and this is that place. A
clever workaround at this boundary is a bug being introduced, not avoided.

**What was refuted stays refuted.** This is not base+delta layering
readmitted under a friendlier name, and it is not version-parameterization.
**The sharing comes from TRUNK PLACEMENT — from where a file lives — not
from a mechanism that relates two files.** Nothing inherits, nothing
overrides, nothing takes an edition argument; a sibling that needs a trunk
definition imports it, and that is the whole of the coupling.

**(4) THE EDITION PARAMETER'S GRANULARITY IS LANGUAGE-DECIDED, and Go
proves it is not a modelling choice.** The clauses above answer *which
surface a reader reads*. They silently assume the edition is a property of
the BUILD. For Go it is a property of the **FILE**, and the Go charter
demonstrates the consequence with an executable rather than an argument:

* Go's language version is set per module by the `go` line and **overridden
  per file** by a `//go:build go1.N` constraint — in **both** directions,
  verified.
* One package, `go.mod` saying `go 1.21`, two files with **byte-identical
  loop bodies** tagged `go1.21` and `go1.22`, prints **`[3 3 3]`** and
  **`[0 1 2]`** — the Go 1.22 loop-variable change — from **ONE compiler
  invocation** (`compile … -lang=go1.21 … ./main.go ./new_122.go
  ./old_121.go`). The per-file version is resolved *inside the type
  checker*, not by a per-invocation flag. The cleanest witness is storage
  identity: **1 distinct address** for `&i` across iterations under
  go1.21, **3** under go1.22.

> **A single Go build is a MIXED-EDITION object.**

**AND THE EXEMPLAR IS NOW REALIZED, NOT PLANNED — the charter's acceptance
test is DISCHARGED.** Go inch 2 built it: **one walker, one world field
different.**

* `runUnder go1.21 loopVarProbe = some 1`;
* `runUnder go1.22 loopVarProbe = some 3`;
* the observable is **POINTER IDENTITY** — and it is **the same number the
  real toolchain gave** (1 distinct address under go1.21, 3 under go1.22),
  so the model reproduces the measurement rather than a story about it.

**This is the whole family-versioning thesis in one artifact**: the edition
is a **datum in the world**, not a directory; the walker is **shared**, not
copied; and the delta is **one field**. §2.4's thin-siblings ruling and
clause (4)'s edition-as-data both discharge here at once.

**AND THE NON-VACUITY PAIR IS THE STANDARD, not a nicety.** The claim is
gated in **BOTH directions**: **go1.21 claiming 3 fails**, and **the
counting loop breaking under 1.22 fails.** The reason both are needed is a
named trap the lane hit:

> **Freshening without copy-back passes every closure test and corrupts
> ordinary loops.**

A wrong implementation that satisfies the *interesting* half is exactly
what a one-directional gate certifies. So:

> **Every version-delta claim carries a non-vacuity PAIR — the old
> behaviour must FAIL under the new edition, and the new behaviour must
> FAIL under the old.**

**And the loop-variable set is READ OFF the init's locals, not
hand-listed** — the census discipline (§5.4) applied inside the semantics:
a hand-written list is a second source of truth that drifts from the
construct it describes.

**So for Go a COPY architecture is not inelegant — it is INCORRECT.** Two
whole spec-mirrors, one per edition, cannot express a program whose files
disagree, because there is no single model in which such a program has a
meaning at all. That is a **correctness** failure, and it is the strongest
argument in this document against per-version copies, arriving from a
language none of the earlier censuses covered.

**This does NOT reverse §2.4, and the distinction is worth stating
exactly**, because "Go needs a version parameter" and "§2.4 refuted
version-parameterized definitions" sound like a contradiction and are not.
They answer different questions:

| question | mechanism |
| --- | --- |
| *which SURFACE does this reader read?* | **directories** — thin siblings over a thick trunk |
| *what does THIS FILE mean?* | **data** — the edition is carried by the program |

C's `C17`/`C23` split is the first question: a tier mirrors one document at
a time. Go's `//go:build go1.22` is the second: the edition is part of the
program's own text, so it must appear in the model as a **datum**, exactly
as a C translation unit carries its `profile_id`. A tier can need both —
Go would still take thin siblings if it ever mirrored two spec editions
wholesale, and the loop rule would still be a parameter, because one build
contains both semantics.

**The granularity row, per language, which a founding lane fills at step
0:**

| language | edition selected | by what |
| --- | --- | --- |
| C, Ada | per translation unit | a compiler flag (`-std=`, and Ada's equivalent) |
| ECMAScript | per source text | the parse goal, per the ES charter |
| **Go** | **per FILE** | **a build constraint in the source text** |
| Python | per interpreter | the binary you invoke |

**And the Go delta's shape is the transferable lesson**: it is **local in
the abstract syntax and non-local in the semantic domain.** Exactly two
productions change, with no new syntax and no typing-rule change — yet the
meaning of every closure capturing a loop variable moves. A census that
counted changed *productions* would have called this delta tiny and been
right about the syntax and badly wrong about the work.

**The SV cleanup is the pattern's second application**, and it should be
run in the pattern's order: **census the IEEE 1800-2017 → 2023 delta
first**, on the model of §2.1's clause instrument, and let the numbers place
the files. The expectation — worth recording *before* the measurement so it
can be wrong — is a **thick trunk**, with 2023's additions living in a thin
`SV2023/` that does not disturb it. If the census says otherwise, the
census wins.

The three mechanisms the charter was asked to price, and why each fails
as stated:

**Full per-version copies — refused, by both censuses.** For C it means
933 duplicated lines to carry one line of difference. For Python it means
duplicating `Semantics.lean`, `Runtime.lean` and 45 103 lines of
`Examples/` — the expensive half — to change 59 rows' worth of strings.
Worse than the volume: a bug fixed in one copy and not the other has no
mechanism that notices.

**Base + delta layering — refused, for a reason the Python census
supplies.** Layering privileges one edition as the base, which is false to
the subject (neither C17 nor C23 is derived from the other, and both are
still in use) and rots as editions accumulate: at N=4 nobody can read any
edition's surface without walking three overrides. And it provably cannot
express the delta that was measured — **you cannot override a DATATYPE's
constructor arity from a delta layer.** `PyErr`'s two zero-division
constructors are not a value to shadow; they are the type. Layering breaks
on the first real Python version delta anyone measured.

**Version-parameterized definitions — refused, on readability and on
scale.** `convert (ed : Edition) …` keeps one definition site, but every
theorem about C23 then carries an `ed = .c23` hypothesis, and the reader of
C23's arithmetic reads branches on editions they do not care about. It
also taxes what did not change: you would pay a version parameter on
`evalBinOp` to express that `+` is the same in every Python. At five
editions the arithmetic file is a switch statement.

**Why the ruling is not merely "layering renamed".** The shared layer is
*not an edition*. For Python the intersection is 3.9's semantics with the
message texts factored OUT — which is precisely what makes `PyErr`'s
arity problem dissolve rather than need a special case: the zero-division
constructors are measured NOT to be in the intersection, so they descend
into each edition's own layer and `Py39` states two while `Py311` states
three. The rule produces the right answer without being told about it.
And as editions are added the intersection is RE-MEASURED and may shrink,
pushing a rule down into every edition that has it — duplication that is
bounded by measurement rather than by an ordering chosen years earlier.

**What the reader gets, which was the requirement.** A reader holds one
edition's document and must read that edition's surface, whole. They do —
via the **clause manifest** (§5.5), which is per-edition, generated, and
checked: for edition E, clause X is realized by declaration D in module M,
and M is marked neutral (shared with editions Y, Z) or scoped. The whole
surface is the manifest's transitive closure; the *directory* carries only
the duplication the measurement justifies. A per-edition surface is a
generated VIEW, not a copied tree.

**And the duplication is policed by an instrument, not by discipline.**
The cross-edition gate runs over two manifests and reports, for every
clause both editions claim: identical (the neutral layer's claim holds),
deliberately different (with the change-list citation), or **silently
divergent — a defect**. That is the house census method applied to the
family's own source, and §2.5 is what happens without it.

### 2.5 What the instrument found in the tier that is founding the layout

The C tier models C23, and C23 moved 612 of 933 matched clause numbers
(§2.1). A C17-era number carried into a C23 document is therefore
plausible, silent and wrong — so the citations were checked. Found by
hand first; the hand is now replaced by **`harness/c_citation_check.py`**,
landed with this charter.

| citation | in the tree | C23's actual number | verdict |
| --- | --- | --- | --- |
| `Value.lean:157` — `<<` | "C23 §6.5.7" | **§6.5.8** (§6.5.7 is *Additive operators*) | C17's number, C23's label |
| `Value.lean:141` — truncating `/` | "§6.5.5" | **§6.5.6** (§6.5.5 is *Cast operators*) | C17's number, untagged |
| `c-semantics-design.md` §4.4 — sequencing | "5.1.2.3" | **5.1.2.4** *Program semantics* | C17's number |
| `c-tier-architecture.md` — compound literals | "C23 §6.5.2.5" | **does not exist in C23** | 6.5.2.x was restructured |
| `c-tier-architecture.md` — struct/union members | "C23 §6.5.2.3" | **does not exist in C23** | same |
| `Value.lean:68,178,221` — conversions | "C23 §6.3.1.3" | §6.3.1.3 | correct — and stable, see below |
| `c-semantics-design.md` §6 — `printf` | "C23 §7.23.6.1" | §7.23.6.1 | correct — C17's was 7.21.6.1 |

Nothing in the tree could have caught these: the numbers are plausible,
the titles are not written down beside them, and the drafts are not in the
repository and never will be. This is not a criticism of the C lane — it
is the strongest available argument that clause citations must be
**checked data** rather than prose, which is what §5.5 makes them. **The C
lane's retrofit is in flight and will move these rows**; the table records
the state at the commit that measured it, not a standing accusation.

**AND A PARAGRAPH RANGE IS EDITION-RELATIVE, which the citation checker also
cannot see** (Ada, 2026-08-24). The spec census is pinned at **Ada 2022**, the
tier is **2012**, and **5.2.1 (Target Name Symbols) sits inside "5.1–5.3"** — so
a range copied across the edition boundary silently changes what it contains.

> **A CLAUSE NUMBER RESOLVES; A RANGE ENUMERATES. A range is a claim about which
> clauses EXIST in an edition, and it changes when the edition does.**

**The tier had no 2012 RM to check against, and settled it by CORPUS
MEASUREMENT instead**: **zero `TargetName` nodes in 4 821 ACATS sources** (also
zero `DeclExpr`, `ReduceAttributeRef`, `Parallel*`).

> **The corpus decided an edition question the missing document could not.**

**That is worth recording as a method and not just an outcome.** The obvious
move when a spec edition is unavailable is to defer, and the second-most obvious
is to assume continuity — *"5.1–5.3 surely means the same thing"* — which is the
motivated error, since it is the answer that lets the work proceed. **A corpus
of conforming programs is a third source**: it cannot say what the edition
*permits*, but it can say what the edition's own test suite **exercises**, and a
construct absent from 4 821 sources is not one the range needed to cover.

**The limit belongs with it**: this settles **presence**, never **semantics**.
Zero occurrences answers *"is this construct in scope for the range?"*; it says
nothing about what the range's clauses **mean**, and a lane that stretches it
that far has swapped a missing document for an argument from silence.

**And the same instrument caught this document.** §1.3 originally read the
`§6.3.1.3` row above as evidence that C23 *mandates* two's-complement
conversion. It does not — p3 is identical across the editions and C23
J.3.6 (3) still lists it as implementation-defined. The corrected evidence
and the lesson are in §1.3. **The citation checker cannot catch that class
by itself**, and it says so: it proves a number RESOLVES in the claimed
edition, never that it is the number the author meant. `Value.lean:157`
resolves cleanly to *Additive operators* — only reading the surrounding
line reveals that the author meant shifts. **That gap is exactly the work
the clause manifest does**, and it is why §5.5 pairs a resolved citation
with the declaration it justifies rather than stopping at resolution.

**A fourth exclusion, found by running it.** The C lane's convention
(untagged inside `LeanModels/C/C23/` = C23; a superseded citation carries
its tag; a `docs/*.md` token means an internal reference) leaves one case
undefined, and it is noisy: these documents number their own sections
§1..§7, colliding with the standard's clauses 5, 6 and 7. Untagged `§5.2`,
`§5.4`, `§6.1` in the charter are internal cross-references, and resolving
them as ISO clauses produced four MISSING rows of pure noise — *correct
documentation reported as drift*, the exact failure the exclusions exist
to prevent. The rule the instrument adopts: **inside a `.md` file an
untagged `§` is an internal reference**; a `.lean` file has no section
structure, so untagged is unambiguous there. Untagged `.md` citations are
reported as `unclassified` rather than dropped, because that count — **12
today** — is the size of the convention's blind spot, and tagging them is
how it shrinks.

---

## 3 THE SHARED SUBSTRATE CONTRACT

### 3.1 What is shared today — measured, and it is one struct

* `LeanModels/Core/Basic.lean` is **13 lines** and defines `Span`.
* It is imported by **three** lane files: `Python/Ast.lean`, `C/Ast.lean`,
  `C/Value.lean` (plus the two umbrella modules).
* **`LeanModels/Ada/` imports ZERO `Core` modules** — verified by
  `grep -rl 'import LeanModels.Core' LeanModels/Ada/`, which returns nothing.
  Recorded as an **asset, not a gap**: a tier with an empty Core closure is the
  cleanest available subject for a **transfer argument**, because anything
  proved about it is proved without the shared substrate in scope, and a later
  claim that it *could* adopt Core is a claim about an addition rather than
  about an entanglement. **A zero here is a fact about the TIER**, in exactly
  §5.2's sense — the API cannot be reaching for what it never imports.
* `Run σ α` has **exactly ONE lane consumer: Python** — 15 files under
  `LeanModels/Python/` plus 6 under `Examples/python/`. **SystemVerilog,
  C, RISC-V, Circuit, Spice and Verilog-A are all zero.**

  **CORRECTION, and the error is one this document warns about
  elsewhere.** An earlier revision claimed *"Python (16 files) and
  SystemVerilog (3)"*. The SV three were `grep -rl '\bRun\b'` matching the
  **English word** at the head of a docstring — `/-- Run one comb-phase
  process…` — in files whose actual outcome type is SV's own
  `inductive Res` (`Sv/Semantics.lean:85`). A bare-word grep over a corpus
  that contains prose is not a type census. The C tier's own charter
  records the mirror-image lesson — *grep an operator sort's constructors
  **without** the leading dot* — and this is that trap from the other side.
  Re-derived type-aware (`: Run`, `Run.ok`/`.exn`/`.timeout`/`.unsupported`,
  `Run <Type>`), the SV count is **0** and Python's is **15**.

  **And the right answer was already in this document.** §0.2's inventory
  table records SystemVerilog's outcome type as `Sv.Res α` — correctly —
  three hundred lines above the bullet that called SV a `Run` consumer. The
  failure was not a missing measurement but **two measurements of the same
  fact that were never checked against each other.** That is precisely what
  §5.5's manifest does for clause citations, and it is an argument for
  doing the same to this document's own load-bearing counts.
* Re-derived today, and **grown since §L35 priced the move**: `Run.`
  appears **1282** times (was 1251), `: Run` **160** times (was 143),
  across **31** files (was 24).

**Everything else the C lane "reused" is METHOD, not code** — and the C
charter says so itself. That is not a failure; a method that transfers
entire is the most valuable thing this repository has. But it means the
shared substrate is **one structure — `Span` — with two lane consumers
(Python and C)**, while the outcome type that the whole architecture is
argued around has **one**. A document that spoke of either as an
established platform would be describing something that does not exist.

### 3.2 The list

**LANGUAGE-NEUTRAL — belongs in `LeanModels/Core/` or in the method:**

1. **`Run σ α`** — the four-constructor outcome covenant. State retained
   on `.ok`; `.timeout` is fuel exhaustion and nothing else; `.unsupported`
   is loud and fuel-independent. Measured parametric: `Run CWorld CVal`
   typechecks today.
2. **The ∃-fuel threshold form and `fuelMono`** — *"∃ n, ∀ fuel ≥ n, … =
   .ok …"*, induction on math variables never on fuel, side conditions by
   `omega`.
3. **`Span`** — subject to §3.5.
4. **The census / verdict / instrument METHOD** — census before pricing;
   the instrument lands beside the claim; double-run determinism; every
   refusal path RUN and not admired; no whitelist that silences a mismatch.

   **"Core only, no packages" is a PER-TIER discipline, not a repo-wide
   fact**, and the doc should stop implying otherwise. Measured: **Mathlib
   is a required dependency in `lakefile.toml`** and **26 files import it**
   — 23 under `LeanModels/` plus 3 under `Examples/`. But the breakdown is
   the point — **and every number here counts FILES THAT IMPORT MATHLIB,
   nothing else**: **Spice 11 Mathlib-importing files, Circuit 11,
   Verilog-A 1, and ZERO in Python, C, SystemVerilog and RISC-V.** The analog lanes need real analysis
   (`Mathlib.Data.Real.Basic`, `Analysis.Calculus.Deriv`,
   `MeasureTheory.*`) and take it; the proof tiers claim core-only and
   *are* core-only. So a founding lane states its own dependency posture in
   its charter — "this tier depends on no package" is a claim about that
   tier, checkable per tier, and false if read as a claim about the
   repository.

   **AND THAT SENTENCE HAD TO BE REWORDED, BECAUSE IT WAS READ AS A SORRY
   COUNT (2026-08-24).** *"Spice 11, Circuit 11, Verilog-A 1"* carried its
   unit in the **paragraph** and not in the **sentence**, and a dispatch
   quoting the sentence sent a lane hunting **eleven `sorry`s that do not
   exist**. Measured on the branch: **zero `sorry`, zero `axiom`, zero
   `opaque`, zero `partial`, zero `native_decide` tier-wide** — the only
   `sorry` token in the analog tier is `Surface.lean`'s **guard against**
   one.

   > **A COUNT IN PROSE WITHOUT ITS UNIT BECOMES WHICHEVER COUNT THE READER
   > NEEDS.**

   **This is *a status column names what it measures* (§1.2) one level
   up** — in a sentence rather than a table — and it is worse there,
   because **a sentence travels**. A table row is read in its table; a
   number in prose is **quoted**, and the quotation leaves the paragraph
   that carried the unit behind. **Every number this document states now
   carries its noun in the same sentence**, not merely in its
   neighbourhood.

   **And note which direction the misreading ran**: `11` read as
   incomplete work rather than as dependency, i.e. **toward a problem that
   needed solving.** A reader supplies the unit that makes the number
   actionable, so an unlabelled count is not read neutrally — **it is read
   as whatever would give the reader something to do.**

   **AND THE TWO CLAIMS THAT LOOK LIKE ONE — a lane's own correction.**
   *"Mathlib: no cost"* was **right about DEPENDENCY and wrong about
   APPLICABILITY**, and those are separate facts:

   * **dependency** — importing it costs nothing new; the paragraph above
     is about this, and it is true;
   * **applicability** — its lemmas govern *your* constants. That is a
     claim about **your definitions**, not about the build, and nothing
     above supports it.

   Nothing in this section licenses the second. A tier can pay zero to
   import Mathlib and still find **not one of its lemmas applies**, which
   is exactly what happened next.
5. **The envelope discipline** — `schema_version`, `language`,
   **`language_version`** (§1.5), `frontend` FAMILY, `source_file`,
   `source_sha256`, `Unsupported` leaves for anything outside a pinned
   vocabulary, deterministic output, and a cache key that includes the
   profile.

   **READ THE MODE OUT OF THE ARTEFACT, never out of an ambient setting**,
   and the SV lane's §L67 sharpened this to **three edges** worth copying:
   the **schema version**, the **top module**, and the **source-path
   spelling**. All three are properties of the envelope in hand, and each
   is a place a tool can silently assume instead of asking — a
   configured-elsewhere default, an implied entry point, a path normalized
   one way here and another way there. An envelope that cannot answer
   "which mode am I?" from its own bytes is one whose consumers will
   disagree about it, which is the same failure `language_version`
   (§1.5) fixes for editions and `profile_id` fixes for the C ABI.
6. **The batch protocol** — `jobs.jsonl`, ONE runner process for the whole
   batch, exactly one line per job in job order, a `runner-error` row
   rather than a missing row.
7. **The exit-code convention** 0/1/3/4/5, and the invariant that **3 and
   4 are never agreement**.
8. **Effects as world data, inputs as traces** — stdout is world data;
   clock, stdin, environment and argv are input traces with a loud
   underrun.
9. **The `maybe <name> <required-file> <cmd>` CI helper** — present ⇒ run,
   absent ⇒ SKIP, reported, never silently omitted.
10. **The coverage-by-clause tooling** (§5.5) — neutral SHAPE, per-language
    content.
11. **Component #1 — the monad and its verification-condition generator**
    (§3.4). One `SemM` — `ExceptT ρ (StateT W Halt)`, in that order — one
    `WPMonad` instance, the default `mvcgen`. No language writes a vcgen
    **on the fuel-free fragment**; at the fuel-recursive points each
    language still assembles its own threshold form, which the pilot
    measured and §3.4 states as the bound.
12. **Component #2 — SoftFloat** (§3.5). Layer 1 (executable bit-level
    IEEE 754) is supplied by core Lean on the pinned toolchain; layer 2
    (the round-of-exact spec algebra) is the family's build. Consumed by
    C, Wasm, SV, Python, Go — and **blocking** for ECMAScript.
13. **Component #3 — the concurrency pattern** (§3.6). Schedule as an
    explicit parameter, executable counterexample schedules, the DRF-SC
    fence, three proof-burden tiers. One pattern, one citation per
    language. **The monad carries one process's step; `W` carries the
    concurrency** — a language whose processes suspend defunctionalizes the
    continuation into `W` (§3.6 (1a)), because the stack has no suspension
    case and cannot be given one.

**PER-LANGUAGE — never shared, and the C tier measured why for the first
three:**

1. **Values.** C's integers have widths and a UB boundary across 327
   overflow-capable sites; Python's `RVal.int` is unbounded. One `Int`
   constructor cannot express "unsigned wraps, signed refuses" in adjacent
   operands, which `mix64` and `PACK_VM` require.
2. **Memory.** In C a local has an ADDRESS — 86 `&`-of-automatic and 20
   `&`-of-subobject sites — and `realloc` MOVES the hot table, so
   provenance is structural. Python's locals are bindings with no address
   and its `Addr := Nat` *is* an array index.
3. **The refusal taxonomy's causes.** Python's `.unsupported` is a
   property of the program TEXT and retires; C's UB refusal is a property
   of the RUN and never retires.
4. The AST, the ingester, the extractor, the oracle.

### 3.3 `Heap` is per-language, and the question is answered not deferred

The dispatch asked with a question mark. **The answer is no**, and the
evidence is that the two heaps in the tree disagree about something
fundamental: whether a local has an address. Python's `Heap := Array Obj`
with `Addr := Nat` cannot carry the provenance that says a `realloc`ed
pointer is dead; `Ptr = (Option ObjId, Int)` can. A neutral `Mem`
typeclass could be *invented*, and the charter's own rule forbids it:
share only what is ALREADY parametric, measured. `Run`'s σ was; a heap is
not, and a typeclass with two irreconcilable instances is a decoration.

### 3.4 ONE MONAD, ONE vcgen — the substrate's centerpiece

**The question: does every language need its own `mvcgen`?** The answer is
a SPLIT, measured by the pilot (`docs/mvcgen-pilot.md`, §L61): **no on the
fuel-free fragment, yes at the fuel-recursive points.** This section states
the design; every number in it is the pilot's, and where the pilot refuted
this document it says so.

**AND THE PYTHON TIER'S CURRENT STATE IN ONE SENTENCE, because this is where a
newcomer looks first** (pyc lane, staged on its queued ticket; conditional on
that landing):

> **Executable behaviour is the REBUILD's; proved behaviour is still the
> TRUNK's; the two are held together by the PURE WORKERS they share — which is
> why a capability opening reaches the harnesses instantly and the proof layer
> not at all.**

Read it as a map of where a change lands. A capability added to the rebuild is
visible to every differential harness the moment it exists, because the
harnesses run the executable side; the proof estate does not move until the
shared workers do. **The asymmetry is the design working, not a gap** — but it
is also why *"the rebuild can do it"* is never an argument that the trunk can,
and why a capability audit sweeps trunk, presentation **and** the ingestion
rewrites (`docs/backlog/architecture.md` `2026-08-23-architecture-23`).

**Layer 1 — one monad family, and the layer ORDER is load-bearing.**

```lean
-- (illustrative — the substrate shape; LANDED as LeanModels/Core/Outcome.lean)
abbrev SemM (W : Type) (ρ : Type) := ExceptT ρ (StateT W Halt)
```

**THE TWO-ABBREV SPELLING IS CANON, and the reason is a Lean fact worth
recording so no tier re-derives it: DEFAULT TYPE ARGUMENTS FAIL FOR
MONAD-RETURNING ABBREVS.** Giving the payload parameter a default does not
work — `SemM W ρ Int` binds **`Int` to `π`**, not to the value type,
because the abbrev returns a monad and the next argument lands on the
defaulted slot. So the family spells it as **two** abbrevs, `SemMWith` and
`SemM`, with `rfl`s **pinning the `Unit` instantiation** so the specialised
spelling is provably the general one at the default payload. A tier that
tries the single-abbrev-with-default spelling will get a type error that
does not name the cause.

**This document first wrote `StateT W (ExceptT ρ Halt)`, and that is
REFUTED BY `rfl`.** `StateT` outside `ExceptT` **discards the state on a
raise** — the shapes are `W → Except ρ (α × W)` versus
`W → (Except ρ α × W)`, and only the second keeps `W` on the error branch.
`Run`'s `.exn` RETAINS state, and `PyPost.err` is state-aware for exactly
that reason. The difference is visible in the `PostShape` barrel:
`ρ → ULift Prop` in the wrong order, **`ρ → W → ULift Prop`** in the right
one. **The wrong order cannot state the tier's own error postcondition.**
One line, load-bearing for every tier written against the sketch, and
verified here independently before propagating.

**AND THE SUBSTRATE KEEPS ITS EXPLICIT SPELLING — adopted by SHAPE, not by
spelling.** `Run σ α` could be spelled as core's `EStateM`, and the
isomorphism is available. It is **not taken**: kernel `rfl` measured
**1.4× slower on `EStateM` at fuel 4096**, and kernel reduction is
load-bearing here. **(That reason stands; the ATTESTATION named for it was
wrong — `#guard`/`#py_check` are RUNTIME attestation, not kernel `rfl`.
See §5.4's instrument contract. The 1.4× measurement was on kernel `rfl`
and is unaffected; what needs re-attesting is which artifacts certify
kernel-reducibility.)** So the
family adopts the monad's **shape** (`ExceptT ρ (StateT W Halt)`, its
`WPMonad` instance, its laws) while keeping its own spelling, and records
the iso as available rather than mandatory. A tier with no kernel-reducible
runs to protect may spell it either way.

**THE ORDER LIFTS; THE CONGRUENCES DON'T — ruled, conditional on landing.**
The monotonicity work below raises the question of what of it belongs in
`Core`, and the answer splits cleanly:

* **LIFTS.** The flat order itself —
  `FlatLe (bot : α) (x y : α) : Prop := x = bot ∨ x = y`, with `refl`,
  `bot_le` and `eq_of_ne_bot`. **Every tier's `Res.le` / `PyLe` is an
  instance of it**, so it is one definition and three lemmas serving all
  of them.
* **DOES NOT LIFT.** The `Res` lemmas themselves, and the **bind / ite
  congruences**. `Sv.Res` and `Python.Res` are **DIFFERENT TYPES** —
  Python's carries the `.exn` raise arm — so the congruences are **each
  about a different monad's `bind`.** They stay per-tier.

> **The ORDER lifts; the CONGRUENCES don't.**

**TAKEN AS WRITTEN BY A SECOND TIER, and it decided a scope rather than
settling an argument** (Go, `6a73111`, on master). Go's seam needed
congruences; `Python.Res` carries an **`.exn` arm the Go stack does not have**,
so lifting Python's would have been **the thick-trunk mistake this ruling
exists to prevent**. Core supplied the **order**; the lane wrote its **own
congruences**. A ruling whose first out-of-tier use is a lane *declining* to
reuse something is better evidence than one whose first use is a lane reusing
it — **the ruling's whole content is where the line falls, and only the
refusing case tests the line.**

**AND CORRECTED BY THE C LANE, WITH A MECHANICAL TEST THAT REPLACES THE
JUDGMENT** (C's seam lift, merged). *"The order lifts; the congruences don't"*
is **right about Python's `Res`** — which carries an `.exn` arm nothing else
has — **and WRONG for a second `SemMWith` tier**, whose congruences are about
the same stack and lift fine.

> **The discriminator is whether the PROOF MENTIONS A TIER TYPE.**

> **LIFTED-VS-TIER-BOUND IS DECIDED BY GREP, NOT BY JUDGMENT.**

**Which is the better form of a ruling this document had been stating as a
principle.** *The congruences don't lift* was a **summary of two tiers'
circumstances** that read as a property of congruences; the real property is
**mentions-a-tier-type**, and Python's `Res` congruences have it while a second
`SemMWith` tier's do not. **Same ruling, correct in both directions, and now
checkable by a lane that was not in the conversation.**

**And it is this register's own preference applied to itself**: *where a rule is
at risk of re-collapsing, the durable form is a type, not a reminder* — here the
durable form is **a grep, not a maxim.** A maxim about congruences invites each
lane to decide whether theirs are the lifting kind; **a test on the proof text
does not.**




**STRENGTHENED — the lift now has THREE in-tree instances**, found by the
duplication incident above: **`Sv.Res.le`, `Python.Res.le`, and `PyLe`.**
The ruling was made on two; a third independent instance of the same
two-constructor order is the convergence standard (§9.3) applied to a
definition rather than to a name.

**AND A JUDGMENT THAT FALLS OUT OF THE RETRACT: `PyLe` must NOT be defined
through `toRun`.** `toRun` is the **lossy projection** (§3.4) — it
**erases `RefusalCause` and the snapshot**. An order mediated by it would
therefore **equate refusals with different causes**, which is not a
convenience but a **weakening of the definition**, and §0.1's first
principle forbids exactly that. Define the order on the type that carries
the information; do not route it through the view that drops it.

That is the retract framing paying off in a place it was not written for:
**knowing precisely what `toRun` loses is what makes "do not define
through it" a derivation rather than a preference.**

That is §2.4's trunk/sibling split arriving in the proof layer: the trunk
takes what is genuinely one thing (a two-constructor order on any type
with a bottom), and the siblings keep what is only *shaped* alike. A
congruence lifted here would be the thick-trunk mistake — one lemma
pretending to be about two monads.

**What travels instead is the NAMING**, mirrored across tiers so a reader
moving between them finds the same shelf: `Res.le`, `le_refl`,
`timeout_le`, `le_eq`, `le_bind`, `le_ite`, `<worker>FuelMono`.
**Convention where a definition cannot go** — which is the cheapest form
of sharing and the only one available when the types genuinely differ.

**Stated conditional on landing**: this rides the successor's `fuelMono`
ticket, and because it touches `Core` it owes a **full build** (A14).
Master truth today is that it has not landed.

**AND THE LAYER ORDER PAYS OFF A SECOND TIME — fuel monotonicity becomes
MECHANICAL.** Measured **in scratch** by the successor's `Monadic.fuelMono`
feasibility probe (kernel-checked there; **not yet landed**, and stated as
such). The ∃F collapse's one missing lemma is provable **without touching
the `Kont` knot and without weakening anything** — and the reason is
§3.4's own covenant:

* the **only** `catch` in the fuel-free half is `tryCatch` on
  `ExceptT PyErr` — **the PROGRAM's channel**;
* **nothing observes the `Halt` layer**, so **no arm can branch on a
  timeout**;
* therefore every arm is a **bind / ite / tryCatch composition**, and
  `tryCatch_apply` — *`Loud` passes straight through; the handler is
  reached only from `ρ`* — makes the induction mechanical.

> **The layer order chosen for STATE-RETENTION ON RAISE is what makes FUEL
> MONOTONICITY mechanical.**

**AND THE LAYER ORDER IS NOW MECHANICAL IN A SECOND TIER — Go's `run_bind`,
the covenant in a form a proof can REWRITE with** (`6a73111`). One lemma opens
the stack, and its arms *are* the order restated as rewriting rules: **loud
discards state, panic RETAINS it, only a value continues.** Nothing about that
list is a design decision made at the seam — it is `ExceptT ρ (StateT W Halt)`
read off, arm by arm, in the one place a proof needs it.

> **The covenant made mechanical: the layer order paying for itself in a form a
> proof can rewrite with.**

**This is the SECOND tier in which the speaker split bought a theorem it was not
designed for.** The split — `ρ` is what the program can talk about, `Halt` what
only the model can say (§3.4) — was chosen for **fidelity**, so that a model-level refusal
could not be caught by modelled code. It keeps returning **proof** dividends:
fuel monotonicity became mechanical because of the state-retention order, and
now a stack-opening lemma is three arms long because each speaker has exactly
one behaviour on `bind`. **A distinction drawn for the right reason keeps paying
in currencies it was not drawn in**, which is the strongest available argument
for drawing them on principle rather than on convenience.

**AND THE CONGRUENCE SET HAS SIX SHAPES, not three — three of them CORE's.**
A tier's monotonicity obligations over the substrate are **`bind`, `ite`,
`tryCatch`** (the monad), **`zoomIn`, `zoomOut`** (the **state-zoom
seam**), and **`liftRes`** (the **PURE-WORKER seam**:
`Res.le x y → liftRes x ⊑ liftRes y`).

**`liftRes` earns its own shape for a structural reason, not as a sixth
item on a list:**

> **`liftRes` is the single door the maximal trunk comes through — so it
> is the ONLY place fuel-argument monotonicity is consumed, on either
> side.**

Every pure worker's monotonicity enters the monadic world there and
nowhere else. That makes it the one seam where a missing lemma is not
merely a gap but a **severed connection between the two halves of the
proof**: the trunk's `_mono` results exist and cannot be spent. The two adapters are **`Core`'s own**
(`LeanModels/Core/Outcome.lean`), so **every tier instantiating `SemMWith`
inherits the same two obligations** — and, once `Core` carries the seam
lemmas, inherits their discharge too. Python's `inFrame` / `inWorld` are
instances at **two lines each**.

> **Missing one is not a missing ARM; it is a hole in the SET — and it
> shows up as a goal no amount of arm-work can close.**

That distinction is the practically useful part. A missing *arm* looks like
more of the same work; a missing *shape* looks like an impossible goal, and
a lane will grind arms indefinitely against it. The tell is that
`iterValues_mono` **closed the moment the seam lemmas existed** — no arm
changed. When a monotonicity goal resists work that is succeeding
elsewhere, **check the SET before checking the proof.**

**AMENDED AT THE LANDING: SIX shapes — monad (3) + state-zoom seam (2) +
PURE-WORKER seam (1).** `Monadic.fuelMono` landed and the set was one short.
The sixth is **`liftRes`**: the seam where a `Res`-level fact about a
fuel-taking *shared pure worker* becomes a `⊑` fact about the tier that lifts
it. `PyLe.liftRes : Res.le x y → liftRes x ⊑ₚ liftRes y` is four lines, and it
is the ONLY place the tier's fuel BOUND is consumed — both `K.fuel` sites in
the monadic Python tier (`evalCompareOpH_mono` and `setDedup_mono`) come
through it and nothing else.

> **A tier that REUSES another's pure workers owes a congruence for the DOOR
> they come through, not just for the operations it writes itself.**

That is the general statement, and it generalises to every tier built on a
maximal trunk: the composition operators are the tier's own, but `liftRes` is
where somebody else's theorem enters, and an order with no congruence there
cannot import a single shared proof. The tell is the same as the seam's: a
goal that names a worker this tier never defined.

**AND THE CENSUS THAT SHOULD HAVE COME FIRST: LEAN CORE ALREADY HAD THE
ORDER.** `Lean.Order.FlatOrder b` (`Init/Internal/Order/Basic.lean:770`) IS
`FlatLe`; the bridge `FlatOrder.rel x y ↔ (x = b ∨ x = y)` is proved green, and
core ships `PartialOrder`/`CCPO`/`MonoBind` instances for `ExceptT`, `StateT`,
`ReaderT`, `OptionT` — the whole `SemMWith` stack above its base. Full
measurement, price and ruling: [docs/lean-order-census.md](lean-order-census.md)
(2026-08-23).

> **A shared abstraction is censused against the TOOLCHAIN before it is
> censused against the tree.** The tree's three copies were the visible
> duplication. Core's was the fourth, and it was invisible because nobody
> looked one level up — §9.0a's blind spot, one level up.

Two findings from it belong here rather than in the census, because they are
about how this family builds proofs and not about one lemma:

* **`@[partial_fixpoint_monotone]` IS A DOCUMENTED EXTENSION SEAM.** A tier's
  own congruences — the state zoom, `tryCatch`, `liftRes` — can be *registered*
  with core's dispatcher instead of being dispatched by hand. **Our seams stay
  ours to PROVE; they need not stay ours to DISPATCH.** That is the shape any
  future consolidation should take: keep the proofs, hand over the search.
* **CORE'S DRIVER IS THE SAME SHAPE AS OURS, ARRIVED AT INDEPENDENTLY.**
  `monotonicity`'s own docstring says it "performs one compositional step" —
  it is not a walker, and `partial_fixpoint` drives it. The driver that works
  is `repeat' first | <leaf> | monotonicity`, which is `mono_with` exactly:
  one step per goal, kept, never a parent that re-plans. **A congruence walker
  converged on by two independent designs is a design, not a workaround** —
  and that is the strongest evidence the backtracking `first` was the defect
  rather than the ambition.
* **AND THE SAME SIGNAL HAS NOW FIRED ON A NAME RATHER THAN A DESIGN — SECOND
  INSTANCE** (SV, in tenure). **Two tiers independently named the
  `Res`-to-monad bridge `liftRes`**, identically and without contact.

  > **THE SUBSTRATE'S VOCABULARY IS EMERGING BOTTOM-UP, and independent
  > identical naming is the same evidence as independent identical design.**

  **This is the `line`/`col` convergence's shape at ×3 arriving at ×2 on a
  different kind of object** — and naming is the cheaper instrument, because it
  costs nothing to observe and it happens before any code is shared. *When two
  tiers reach for the same word for the same seam, the seam is real and the
  substrate is late, not early.* **Record convergences on NAMES with the same
  weight as convergences on shapes;** they are the earliest signal this family
  gets that a component belongs in §3.2's list.

**AND TWO PLACEMENT LAWS THE LANDING PRODUCED**, both cheap to state and both
learned by nearly getting them wrong:

> **A shared name is worth an import; it is not worth relocating the trunk's
> elaboration cost.** The `Lean.Order` base instances were ruled to sit beside
> `FlatLe`. They do not, because `Core/Order.lean` is in `Python/Obs.lean`'s
> import closure and `Core/Outcome.lean` is not — so "beside" would have dragged
> `Std.Do` and the `grind` macro rule into all 65 `Examples/` files that import
> the umbrella. **Check whose closure a file sits in before deciding two things
> belong together.** The order facts stayed in `Core/Order.lean`; the stack
> instances went to `Core/Outcome.lean`, where the stack is.

> **ONE OPENING OF THE MONAD STACK IS THE RIGHT NUMBER.** A tier reasoning
> through `ExceptT`/`StateT`/`Except` by name should do it in exactly one lemma,
> in the module where the stack is DEFINED, and every other fact should compose
> that one. Python's is `Monadic/Substrate.lean`'s `bind_apply`; the `toRun_*`
> seam lemmas beside it translate do-notation into the trunk's `Run.bind`, so a
> proof about a monadic definition reaches the trunk's vocabulary without
> re-deriving the boundary. The tell that this is being violated is a proof that
> unfolds `Functor.map`: `map` drops BELOW the one opening's reach, and the goal
> stops being about the stack at all — `map_eq_pure_bind` is the way back up.

**AND A THIRD, FROM A GATE THAT CAUGHT ITS OWN AUTHOR ON ITS FIRST RUN.**

> **TWO FIELDS WITH THE SAME NAME ARE NOT THE SAME FIELD.** A new
> `refusal_census.py` check compared the model's `class` (§5.2's four refusal
> CLASSES) against the census's `WHITELIST_CLASS` (its own taxonomy of WHICH
> GAP a row is) and produced **109 confident DRIFT lines**, uniformly wrong.
> The word matched; the field did not.

The useful part is the SHAPE of the failure, because it is the shape a name
collision always takes: **not a few odd rows, but a large, uniform, confident
disagreement.** A check that suddenly convicts most of a corpus is far more
likely to be measuring the wrong column than to have found a systemic bug — and
the tell is the uniformity, not the count.

> **A GATE ADDED WITH A LANDING MUST RUN IN THAT LANDING'S TRIAD.** This one
> did, as a `--gates` addition, and it failed — 116 lines, all of them defects
> in the gate rather than in the tree, including 7 that flagged behaviour the
> same commit's own documentation specified. Had it landed unexercised it would
> have been a red gate in everyone else's tenure, blamed on their change.
> **An unexercised gate is not a gate; it is a claim.**

That is the same shape as C's routing law paying for itself at adoption: a
decision taken for one reason turning out to buy a second. Here the
**speaker split** (§3.4) is doing the work — because `Halt` is the model's
channel and no program construct observes it, monotonicity has no case to
consider where a timeout is inspected.

**Recorded as the family's MONOTONICITY RECIPE for ρ-bearing tiers**, with
its own boundary marker: **`le_tryCatch` is the one lemma SV's `fuelMono`
never needed**, because SV has **no `ρ`**. A tier with no program-error
channel gets a shorter recipe; a tier that adds one inherits exactly this
lemma.

**`Run σ α` IS A FAITHFULLY-EMBEDDED VIEW of that stack — a RETRACT, not
an isomorphism.** Both stacks `#synth` a `WPMonad` with **zero instances
written**, which **retires the 2026-08-13 spike's obstacle 1** — *"`Run` is
not a monad"* — as a permanent obstacle: it was a fact about the tree, not
about the type. The instance was never unavailable; it was never asked for.

**CORRECTION — this document twice called `ofRun`/`toRun` "mutually
inverse", and the Core payload landing makes that FALSE.** With
`Loud.unsupported` now carrying `(cause, message, snapshot)` and
`Run.unsupported` carrying **one field**, a round trip through `Run`
returns the only class `Run` can represent: **an `orderDependence` refusal
goes in and `unsupported` comes out.** The pilot's iso was true of the
poorer `Loud` it was proved against, and the payload ruling — which this
document argued for — is exactly what broke it.

**The lane replaced the claim rather than weakening it, which is the right
move**: `toRun ∘ ofRun = id` **still holds**, so `Run` embeds faithfully
and **no trunk-shaped outcome is corrupted by lifting**. The residue is
stated as theorems rather than left as a caveat — `ofRun_toRun_normalises`
says *exactly what is lost*, `ofRun_toRun_of_plain` says *exactly when the
trip is the identity*. A retract with its residue characterised is a
stronger artifact than an isomorphism that quietly stopped being one.

> **`Run` is a faithfully-embedded VIEW. The stack is RICHER by the
> refusal payload. Theorems about `Run` transport ALONG THE EMBEDDING —
> never the other way.**

#### FAMILY LAW — ONE `Except`/`throw` PATTERN, EVERY TIER

Thomas, on reading the `Halt` ruling below: *"Probably a good idea to use
the same `Except ε α` / `throw` pattern for all languages."* Codified.

> **Every tier's interpreter is written on `SemM`. It is the ordinary Lean
> `Except`/`throw` idiom, used TWICE — and the two are told apart by WHO
> SPEAKS, not by what is thrown.**

| channel | speaker | carries | reachable by a language construct? |
| --- | --- | --- | --- |
| **`ρ`** | **the PROGRAM** | its own errors: exceptions, abrupt completions, `longjmp`, `panic`/`recover`, Ada's exceptions | **YES — this is where a tier instantiates its catch constructs** |
| **`Halt`** | **the MODEL** | refusal (with the structured payload ruled below) and timeout | **NEVER — by type, per the ruling below** |

That split is the whole design, and it is why the ruling below is the one
that had to come first: **`ρ` is what the program can talk about; `Halt` is
what only the model can say.** A tier that gets a new catch construct
extends `ρ` and touches nothing else; a tier that grows a new refusal cause
extends `Halt` and no program can observe it.

**NO TIER-LOCAL OUTCOME TYPES going forward.** A new tier does not define
its own result inductive — it picks `W` and `ρ` and it is done.

**The existing ones converge BY TOUCH** (§9.2's discipline, and never a
big-bang): `Sv.Res`, C's value-layer `CRes`, and the legacy Python `Run`.
Under Thomas's *keep only the new versions, no backwards compatibility*
ruling, by-touch is about **SCHEDULING, not coexistence** — when a tier is
touched its local type is **replaced**, not wrapped, and no adapter is left
behind.

**Two seams that could be misread as contradictions, closed here.**

* **This does not reopen the `EStateM` question.** `Core.SemM` is **our**
  spelling — the explicit `ExceptT ρ (StateT W Halt)` stack, named once in
  `Core` — not core Lean's `EStateM`, which stays rejected on the measured
  1.4× kernel-`rfl` cost. One shared *name* for our own stack is exactly
  what "adopted by shape, not by spelling" asks for.
* **This is cheaper than the Python migration and must not be confused with
  it.** `Run → SemM` is an **embedding with a proved retract** (`toRun ∘
  ofRun = id`), so it owes **no adequacy theorem** — the contrast survives
  the correction above, and for the reason that always mattered: **a
  retract is not a second semantics.** It is one semantics with a poorer
  view, and `Run`'s theorems lift along the embedding unchanged. The
  migration that owes `twinAgrees` is the move to a *second semantics*
  (§3.4 clause b), which is a different thing entirely. Re-spelling: cheap,
  by touch. Second semantics: gated.

**THE RECONCILIATION, measured — and two of the sites are a SEMANTICS FIX,
not a rename.** Audit #2 counted the by-shape adoptions actually in the
tree: **13 sites across 5 spellings.** Most are genuine spelling variants
that an import will absorb. **Two are not:**

| finding | consequence |
| --- | --- |
| 11 sites: the stack's shape, spelled differently | **rename on import** — mechanical, by touch |
| **2 sites: a tier-local `inductive Halt α`** | **NOT interchangeable** — but see the correction below: the fix is in CORE |

**THE TWO SITES, NAMED — and the finding inverts.** Measured on master
after `Core/Outcome.lean` landed:

| site | its `Halt` | `unsupported` payload |
| --- | --- | --- |
| **Core** `Outcome.lean` | `abbrev Halt := Except Loud` | **`msg : String`** |
| **C** `C23/Memory.lean:739` | `inductive Halt α` | `(what : String) (snapshot : Option Mem)` |
| **ES** `Es/Completion.lean:174` | `inductive Halt α` | `(cause : EsRefusal) (message : String)` |

**All three agree on the SHAPE** — `ok` / `timeout` / `unsupported` — so
the covenant holds everywhere. **The whole divergence is the `unsupported`
PAYLOAD, and Core's is the POOREST of the three.**

**Both tiers implement rulings this document made.** C's `snapshot` is the
`Halt` ruling's structured payload, with the never-an-observable guard made
**structural** (its `BEq` ignores the snapshot; `Outcome` drops it) — the
exact two constraints §3.4 imposed. ES's `cause` is the `RefusalCause`
ruling. **Core carried neither — and that is the state the table above
records, which is no longer the state of the tree.** The row is kept
because the dispatch below is only legible against the gap it closed;
§5.4a asks a number to carry its state, and this table's state is
*master before the rebuild lane's merge*.

> **So convergence-by-import would DELETE both payloads.** That is a
> regression, and it is *"the quiet way to lose facts"* arriving from the
> other direction: not two tiers to be fixed, but **a trunk too poor to
> absorb them.**

**AND CORE'S OWN HEADER OFFERS AN ALTERNATIVE THAT THE COVENANT CLOSES.**
It suggests that *"a tier that needs more than two causes does **not**
extend this type; it adds an `.except` layer of its own, which composes for
free."* The Go lane — **the third independent finding of this gap** — named
why that cannot be the answer, and it is decisive on the family's own
terms:

> **An extra `.except` layer is, BY CONSTRUCTION, a CATCHABLE channel.**

`ρ` is the program's channel precisely because `ExceptT` is where catch
constructs are instantiated (§3.4's speaker split). Putting refusal causes
in another `.except` layer therefore puts **refusal in a catchable
position** — the exact thing the `Halt` ruling forbids, and it would be
re-forbidden per language by the N lemmas that ruling rejected. Composing
"for free" is free only if you do not need uncatchability, and refusal is
the one thing that does.

**So the payload goes INTO `Loud`, not beside it** — and Core's header
alternative is closed by the covenant rather than by preference.

**The fix is in CORE, not in C or ES**: parameterize `Loud.unsupported`'s
payload, exactly as the `Halt` ruling (cause + optional snapshot) and the
`RefusalCause` ruling (four classes, tier payload `π`) already prescribe.

**THE HOLDS ARE RELEASED — LANDED, not conditional.**
`Loud.unsupported (cause : RefusalCause π) (message) (snapshot : Option σ)`
is on master, and it **subsumes both tiers**: C at `σ := Mem` with its
guards lifted, ES at `π := EsRefusal`. **Both HOLDs release** — the two
payload-bearing tiers converge by import like the other eleven sites — and
this section's earlier *"Core carries neither"* **is now false, which is
the outcome it was written to become.**

**Master truth, checked rather than assumed** (the same discipline that
recorded the negative a landing ago): `LeanModels/Core/Outcome.lean` now
declares `inductive RefusalCause (π : Type)` with `| unsupported (detail :
π)`, and `Loud` carries the three-field payload. C and ES are released; Go
has the adaptation on master and **the structural-cause decision is Go's
to make**, not this document's.

**AND THE MECHANISM WORKED — this is worth recording because it was a
proposal a landing ago.** The discharge was pinned by a
**`docs_check`-checked block against `Core/Outcome.lean`** rather than by
prose, and **the gate is what retired the conditional paragraph**, not an
editor remembering to. The document's own §9 thesis, applied to itself and
now with an instance: **a claim that a type carries a field is checked
against the type, and it cannot rot silently.** `docs_check` reads
**87/87** on the merged tree.
**All thirteen sites may now converge by import** — the eleven mechanical
ones and the two payload-bearing tiers — because the trunk is no longer
poorer than its adopters. The hold existed to stop a convergence that
would have traded two implemented rulings for a `String`; it has served
its purpose and is discharged.

#### AND IT HAS LANDED — the dispatch is discharged, and the two HOLDs are released

The rebuild lane's merge carries exactly the parameterization dispatched
above. In `LeanModels/Core/Outcome.lean`, on the merge commit:

```lean
-- LeanModels/Core/Outcome.lean (excerpt: the landed payload and its guard)
inductive Loud (π : Type) (σ : Type) where
  | timeout
  | unsupported (cause : RefusalCause π) (message : String) (snapshot : Option σ)
instance [BEq π] : BEq (Loud π σ) where
    | .unsupported c m _, .unsupported c' m' _ => c == c' && m == m'
def Loud.observable : Loud π σ → String × String
  | .unsupported c m _ => (c.className, m)
```

That block is **checked against the tree**, not quoted at it: `docs_check`
matches every line above as a subsequence of `Core/Outcome.lean`, so the
subsumption claim below cannot drift from the definition without a gate
going red. A prose paragraph would have made the same claim and rotted
silently.

**AND `σ := Unit` IS THE FAMILY DEFAULT, on ES's reasoning:**

> **Adding a snapshot without a consumer is designing against nothing.**

A tier takes a non-trivial `σ` only when it has **both** a consumer for the
snapshot **and** the never-an-observable guard to keep it out of verdicts.
Absent a consumer, the parameter is a field nobody reads, carried through
every refusal, and it is exactly the kind of speculative generality §2.4's
census-gated placement rejects one level up.

**AND THE RIGHT WAY TO HOLD A FUTURE `σ`, from Ada: accept `Unit` now and
REGISTER the consumer.** Ada took `Unit` while naming a **predicted**
consumer — a partial trace on a mid-test refusal — and **dating it to inch
5**.

> **Predicting a consumer is not having one.**

So the anticipated need is **named, dated to an inch, and not built** —
which keeps the default honest (no field nobody reads) without losing the
design intent (the inch that will need it knows it is coming). A
prediction held this way is a scheduled decision; a prediction held in the
type is speculative generality wearing a plan's clothes.

ES takes `Unit`; C takes `Mem`
**because it has both**.

**It SUBSUMES both payload-bearing tiers, and the subsumption is checked
against the table above rather than asserted:**

| tier | its payload | how Core now expresses it |
| --- | --- | --- |
| **C** | `(what : String) (snapshot : Option Mem)` | `message` + `snapshot`, at `σ := Mem` |
| **ES** | `(cause : EsRefusal) (message : String)` | `cause` + `message`, at `π := EsRefusal` |

**And C's guard is lifted rather than re-implemented.** The
never-an-observable constraint is now enforced *twice, structurally, in
Core*: the hand-written `BEq (Loud π σ)` compares `cause` and `message` and
**ignores the snapshot**, and `Loud.observable` returns
`(cause.className, message)` — a pair with **nowhere to put a `σ`**, so a
snapshot cannot reach a comparison even by accident. That is C's instance
generalized, so no tier writes it again and a tier that forgets to cannot
silently promote a diagnostic into a verdict.

> **So both HOLDs become SUBSTITUTIONS.** ES's own record of its hold
> (`docs/backlog/es.md`, 51b1893) predicted this precisely — *"the adoption
> then becomes a substitution and both expected-empty gate theorems
> transfer unchanged, since they are stated about `esRefusal` rather than
> about the base"* — and the shape that landed is the shape it predicted.
> C's is the same substitution at `σ := Mem`.

**The two lanes are UNBLOCKED, not migrated.** This document does not
perform their imports: §9.2's by-touch discipline is theirs to schedule,
and the covenant it was waiting on is now a fact about the trunk rather
than a promise about it. What changed is only that importing Core no longer
trades an implemented ruling for a `String`.

The two are not interchangeable **by this document's own `rfl`**: `Halt`
sits outside `StateT`, so a `Loud` result carries **no `W`**; an
`Except Loud` in a position the stack types as `Halt` is a *different
type*, not a different name for one. Whatever those two sites currently
prove, they prove about a stack that retains state where the family's does
not.

**So the rule at `Core`'s landing:** by-shape definitions are **REPLACED by
import** — that is the cheap, mechanical majority — **and the two
`Except Loud` sites are opened as a semantics fix**, with whatever their
theorems said re-established over the real stack. Filing them under
"rename" would be the quiet way to lose two facts.

**`Core.SemM` IS the one spelling — LANDED** — imminent, in its post-merge triad as this is written.

**And the SV verdict softens accordingly.** §3.6's hybrid reading — *a
dormant tier that will not be rebuilt* — becomes **migrates when touched**,
and the opener is already identified: the `SelfCheck` `halted` flag is a
hand-rolled `ExceptT ρ`, and replacing it with the real layer is **one
`@[spec]` lemma that deletes a check from every statement case**. The
cheapest possible first touch, on a tier that already proved the shape was
right by inventing it.

#### RULING — WHERE `unsupported` LIVES: in `Halt`, with a PAYLOAD

Two tiers diverged and a third was about to invent a third answer, so this
is ruled rather than left to convention.

**The divergence.** ES and the Python rebuild put `unsupported` in the
**`Halt` base**, outside `ρ`, each pinning by lemma that no language-level
`try`/`except` can reach it — *an except clause can never swallow "I do not
model this."* The C tier put it **inside `ExceptT ρ`**, so a REFUSE row can
report the state at refusal time: because `Halt` sits outside `StateT`, the
stack unfolds to `W → Except Loud (Except ρ α × W)` and **a `Loud` result
carries no `W` at all**. C's diagnostic need is real, and neither placement
is obviously right.

**THE RULING: refusal stays in `Halt`. The diagnostic need is met by giving
`Halt.unsupported` a STRUCTURED PAYLOAD** — a cause, plus an *optional*
state snapshot captured **at the refusal site**, where `W` is in hand,
before the abort. It says what happened without becoming catchable.

**Why the invariant must be TYPE-level and not lemma-level.** Inside
`ExceptT ρ`, "no catch reaches a refusal" becomes a proof obligation
**re-discharged per language, per catch-like construct** — Python's
`except`, C's `longjmp` *and* signal handlers, Ada's handlers and `abort`,
ES's `try`/`catch` plus a generator's `.throw()`, and Go's `recover()`,
which is designed to catch everything. ES and the rebuild pinned their
lemmas honestly, but they pinned them for languages whose catch is one
well-understood construct. **A family law that holds only where the
language happens to be simple is not a family law** — and §0.1 principle II
is decisive here: the uncatchability of a refusal belongs to the
**definition**, which is trusted and minimal, not to the **library**, which
is incomplete by design. Putting it in the library inverts the trust
boundary for the one property that makes a refusal loud.

**Why the payload is nearly free for C — the existing law already pays for
it.** §3.4 already requires *never a bare polymorphic `throw`; route every
refusal through a NAMED primitive with its own `@[spec]` lemma.* **That
primitive is exactly where the snapshot is captured**, by a `get` the
primitive performs itself, so no refusal site can forget it and the
plumbing is the plumbing the family already mandates.

**Two constraints on the payload**, so it cannot be abused: the snapshot is
**optional** (a tier needing no diagnostics passes none), and it is
**never an observable** — it is diagnostic data on a REFUSE row, never part
of a verdict, or it becomes a way to smuggle state out of a halt and into a
comparison.

**Why the alternative — `Halt` INSIDE `StateT`, so every halt retains `W`
— is REJECTED.** It would work at the type level:
`ExceptT ρ (ExceptT L (StateT W Id)) α` unfolds to
`W → (Except L (Except ρ α) × W)`, retaining `W` on every outcome. It is
refused for three reasons that are not about C:

1. **It changes `Run`'s covenant.** `.timeout` and `.unsupported` carry
   **no state** today; under this order every halt would. That is the
   four-constructor covenant §3.2 calls neutral, and it breaks the pilot's
   proved `ofRun`/`toRun` iso.
2. **It invalidates landed work in two tiers** — ES's pinned lemmas and the
   rebuild's `tryCatch` dividend both rest on the current order.
3. **It is wrong for `.timeout` on the merits.** Fuel exhaustion means the
   run did not complete; handing back "the state at exhaustion" invites
   treating a TIMEOUT as an observation, which §5.1 forbids.

*(The unfolding above is the same `ExceptT`/`StateT` pair whose order §3.4
already establishes by `rfl`; the two tiers independently report the
`Loud`-carries-no-`W` consequence from opposite sides, which is the
corroboration that matters here.)*

**What this stack CANNOT do, stated here because it is a property of the
substrate and not of any tier: it cannot SUSPEND.** `ExceptT ρ (StateT W
Halt) α` unfolds to `W → (Except ρ α × W)` — an `α`, or a `ρ`, plus a `W`,
and no third case. `StateT` is run-to-completion. A language whose
processes pause mid-body must defunctionalize, putting the continuation in
`W` and making suspension a return value; **§3.6 (1a) is the pattern and
SystemVerilog is the worked example.** A tier that plans a suspension
*effect* is planning something the types do not admit.

Two design constraints make this work and both are load-bearing:

* **Fuel stays OUT of the monad — and the reason is stronger than this
  document originally gave.** It is an index on the step function
  (`step : Nat → Stmt → SemM W ρ Unit`), not a reader layer. The original
  argument was that `fuelMono` and the ∃-threshold form are theorems about
  a *family* of programs. The pilot's is harder: **fuel as a monad layer
  does not typecheck.** Fuel's job is to BE the recursion argument, so
  hidden in state it is not an argument and the interpreter fails to show
  termination — *"`loopF` does not take any (non-fixed) arguments"*. The
  alternative does not merely cost something; it does not exist.
* **Nondeterminism enters as an explicit PARAMETER**, per the ∀-resolution
  ruling — a schedule, an evaluation order, an entropy stream. The monad
  stays deterministic and the ∀ lives at theorem level. This is what keeps
  SystemVerilog's event regions and C's unspecified order expressible
  without changing the interpreter's type (§7.2 is what happens when it
  cannot be done).

Fuel monotonicity and the threshold form are then proved **once**, as
properties of the stack, instead of once per language.

**Layer 2 — the DEFAULT `mvcgen`, over one `WPMonad` instance.** Measured
on the pinned toolchain `leanprover/lean4:v4.33.0-rc1`: `Std.Do.Triple`,
`Std.Do.WP`, `Std.Do.WPMonad`, `Std.Do.PostShape`, `SPred`, `PostCond` and
the `mvcgen` tactic all resolve, and `Triple.pure` elaborates with its
`⦃P⦄ … ⦃Q⦄` notation. **No toolchain bump is required.** The pilot
independently confirmed this and sharpened the import boundary: `@[spec]`
is a BUILTIN attribute needing no import — which is why `Logic.lean`
already uses it — while the tactic needs `import Std.Do` and
`import Std.Tactic.Do`, both CORE modules, so `lakefile.toml` and
`lake-manifest.json` are untouched. **The expensive experiment this
document anticipated does not exist.**

Per-language work under this scheme is then: **the World type, the error
type, the primitive step functions, and `@[spec]` lemmas for the
primitives.** Priced by the pilot against C's six design pieces: **≈2 type
declarations + 2 `abbrev`s + ~14 `@[spec]` lemmas ≈ 120 lines**, against
the **5 343 lines** of Python-specific walker (`VC` 546 + `VC2` 939 +
`VCTactic` 3 371 + `LoopTactic` 487) that the shared substrate replaces.
The three never-pooled refusal causes (§5.2) cost nothing — one `.except`
layer each, free by composition — and **C's drain amendment at its 181
short-circuit sites IS the altitude law, at 3 `@[spec]` lemmas.**

**THE ASTERISK ON THAT PRICE, measured by the rebuild lane, and it is the
difference between a demo and an estimate.** The pilot's headline
elaboration economics — a `mvcgen` step in **568 ms** against a gate whose
real-interpreter counterpart takes 24 s — were measured against the
**SHALLOW TWIN**. Run the *identical statement* against the **FAITHFUL
interpreter** and it **does not close at 8 M heartbeats (~14 minutes)**.
The gap is not overhead; it is **exactly the fidelity the twin dropped** —
the nine-step name-resolution chain and the five-way assign fork. Two
smaller faithful gates do close, at **~10–11 s**.

So the economics are real but their granularity is different:
**mvcgen's advantage holds at ARM-LEVEL granularity, given sufficient
`@[spec]` coverage.** The per-language estimate above should therefore be
read as a floor that **grows toward per-arm lemma sets** — ~14 lemmas is
what the *shape* costs, not what a faithful interpreter's every arm costs.
A founding lane should price its `@[spec]` set per interpreter arm and
treat 120 lines as the entry fee.

> **A PERFORMANCE NUMBER MEASURED ON A TWIN IS A CLAIM ABOUT THE TWIN.**

(§5.4a's provenance law, second instance.)

That is the exact twin of §3.4 clause (b)'s adequacy warning, and the two
should be read together: a second semantics owes an **adequacy** theorem
before its *correctness* transfers, and owes a **re-measurement** before
its *performance* transfers. The twin was built to be fast in precisely the
places the real interpreter is slow, so its timings describe the
simplification, not the tier.

**THE BOUND, and it corrects this document.** §3.2 item 11 said *"no
language writes a vcgen."* That is **true on the fuel-free fragment and
false at the fuel-recursive points.** At a symbolic fuel `F`, `mvcgen`
returns the goal **unchanged after 1 m 31 s**: nothing in `Std.Do` relates
two runs at DIFFERENT fuels, because `Triple` is unary on one program while
`fuelMono` and the threshold form are about a family. So
`∃ t, ∀ F ≥ t, run F = .ok w v` is **neither produced nor consumed by
mvcgen; it is assembled around it**, and each language still writes its own
threshold assembly at `call`, loop, and generator points. The saving is
real, it is large, and it is **bounded** — and a tier choosing the
∃-fuel route is choosing the route mvcgen cannot walk, which is a decision
to take consciously and with these numbers.

**The fuel-free fragment is nonetheless large**, which is why the saving
survives the bound: the pilot's `evalM` is structural on `Expr`, and a
whole real gate's slice carries no fuel numeral anywhere. Fuel is owed only
at `callIn` / `execWhile` / `execFor` / `heapEq` / generators.

**A WORKED INSTANCE OF THAT SCOPE, and it resolves the third defect this
document was holding.** The held question was whether per-arm `@[spec]`
lemmas suffice for **nested-match** arms — the binding lemma could not be
*stated*, because `mvcgen` splits the inner match **without retaining the
discriminant**, so unreachable branches arrive as bare `⊢ False`. **The
outcome: the nested-match ceiling stands, and the tier routes around it.**

The generator proof layer on the monadic interpreter is founded as
**judgments with discriminant premises — the trunk's method — and NOT as
`mvcgen` triples.** The ceiling decided it.

**And the reason the trunk's method transports is exact**: the
computed-shape law (§5.6) **never relied on a tactic retaining discriminant
equations** — the premise carries the discriminant explicitly, so nothing
is lost when a tactic declines to. A method that depends on what a tactic
happens to preserve is fragile in precisely the way the harvest rule (§9.2)
warns about; a method that carries its own premises is not.

So §3.4's *"mvcgen on the fuel-free fragment"* has a measured boundary
inside the fragment too: **arm-level `@[spec]` where the match is flat,
judgments-with-premises where it nests.**

**Four laws to adopt now, at zero cost**, all measured rather than
proposed:

* **Altitude lemmas persist, and `@[spec]` is their registry.** With the
  primitives UNFOLDED, `mvcgen` leaves **259+ VCs** and `mvcgen_trivial`
  fails outright; the same goal with four `@[spec]` triples leaves **12**,
  all pure, and closes. The family's existing altitude lemmas do not merely
  resemble `Spec` lemmas — they transliterate.
* **Specs must be OUTPUT-DETERMINED.** A spec taking the answer as an INPUT
  made mvcgen unify the result metavariable with a loop ACCUMULATOR — a
  wrong-but-typechecking instantiation — leaving 23 VCs with dependent
  metavariables. Restated so the value is determined by the postcondition:
  3 and 12 VCs, none.
* **`Triple` does not frame the state.** A read-only primitive must SAY it
  leaves the state unchanged; Std ships `Triple.observe` for it.
* **Never a bare polymorphic `throw`** — route every refusal through a
  NAMED primitive with its own `@[spec]` lemma. This is forced by a real
  Std bug the pilot found in twenty lines (`Spec.throw_Except` carries
  binders its conclusion does not determine, yielding universe-level
  metavariables), and **it is what this family wants anyway**: a refusal is
  a first-class notion here, and mvcgen rewards making it one.

**Risk, recorded straight:** `mvcgen` warns on every invocation that it is
experimental and should be avoided in production, and one Std bug surfaced
in twenty lines of probing.

**And none of this stratum is trusted (§0.1, principle II).** The monad is
part of the definition — it is how the interpreter is written — but the
vcgen, the `@[spec]` collection and every tactic over them are LIBRARY:
they search for proofs of statements the semantics fixed without them, the
kernel rechecks whatever they produce, and a gap in them is a gap to
report rather than a reason to restate a theorem.

**This formalizes existing practice; it does not discard it.** The Python
lane already has a hand-built triple layer — `PyTriple.call`,
`PyTriple.callsTo_ofRet`, `execStmts_append_run` — and its altitude lemmas
(`boolChain_and2`, `boolChain_and3`, `boolChain_and_falsy`, `compare_one`
in `Examples/python/sunfish/fold_depth1.lean`) ARE hand-made `Spec`
lemmas for primitives. `@[spec]` is already core Lean's mvcgen attribute
on this toolchain, and `Logic.lean` says so. The migration renames a
practice that was arrived at independently; that convergence is the
argument for it.

**Three caveats. Two are retired by measurement; the third is now a
standing rule with a named blocker.**

1. **Deep embedding — RETIRED.** `mvcgen` reasons about Lean programs in a
   monad, and the interpreter's SUBJECT is an AST value, so the vcgen must
   unfold the interpreter's `match` on a **pinned** program literal. The
   pilot did exactly this on a real gate and it worked, closing the same
   fact with the gate's own fourteen premises.
2. **Toolchain — RETIRED**, twice independently (this document's probes and
   the pilot's census). `Std.Do` is already at the pin.
3. **Python is MID-CAMPAIGN. The policy is MIGRATION BY EROSION** — not a
   permanent exemption. An earlier draft of this section said Python
   *"bridges, does not migrate"*, which reads as a standing no and is not
   defensible: the right question is not *whether* but *in what order and
   against what evidence.* Three clauses.

   **(a) NOT DURING THE SUNFISH CAMPAIGN — because an interpreter rewrite
   RE-FOUNDS every landed theorem.** The precedent is measured and it is
   sobering in the direction that matters. §L15's re-pin changed only the
   OBJECT PROGRAM — not the interpreter — and its blast radius still came
   in **four files wider than priced**; what moved was **78 pinned spans,
   61 synthesized `<genexpr@n>` names, three censuses and 15 battery
   pairs**, and the law it produced is *"price a re-pin by its `#guard`s,
   not by its `theorem`s."* The reassuring half is that **every theorem
   re-elaborated green with no edit** — because the interpreter did not
   move. **A monadic migration moves exactly the thing the re-pin held
   fixed**, so the half that saved §L15 is the half that would not apply,
   across every file carrying proof edits. That is the cost of doing it
   *now*; it is not an argument that it is wrong.

   **(b) THE BRIDGE IS THE FIRST HALF OF ANY SOUND MIGRATION, not an
   alternative to one.** The monadic form is a **second semantics**, so
   replacing the tier's definition — validated by **1 394 differential
   cases** — without `twinAgrees` would be an **untrusted definition
   change**, and §0.1's first principle makes that the one move the
   architecture forbids: the definition is the trusted artifact, and
   swapping it on the strength of a convenience layer inverts the trust
   boundary. So adequacy is not a toll gate peculiar to Python; it is the
   required artifact on **every** route:

   > **Any route that introduces a second semantics owes an adequacy
   > theorem, and the differential corpus does not discharge it.**

   Whether the monadic form ends up the bridge's far side or the tier's
   new definition, `twinAgrees` is on the critical path either way — which
   is precisely why building the bridge is progress toward migration
   rather than a detour around it. The pilot's twin is already executable
   and `#guard`ed on a fixture, and its fidelity gap to the real
   interpreter is exact and stated (name resolution consults the static
   globals fold first; the twin's does not).

   **(c) AFTER ADEQUACY, THE QUESTION DISSOLVES.** With `twinAgrees`
   proved, the two forms are **interchangeable by theorem**, and the
   migration needs no flag day: new Python work is written monadic, old
   theorems transport across the bridge **on demand** — paid per theorem
   that is touched anyway, never as a campaign — and the deep interpreter
   retires **gradually, or never**. "Never" then costs nothing, because a
   proved interchangeability makes the surviving form an implementation
   detail rather than a commitment. Erosion, not migration.

   **THE `GenFrame` RULING — what a SHARED type may do while the legacy
   layer erodes.** Erosion raises a question neither "freeze it" nor
   "maintain it" answers well: a type used by *both* layers, which is not
   itself retiring, and which the new layer needs to **grow** for a new
   capability. Ruled:

   > **A shared-not-retiring type MAY grow for new capability. The legacy
   > interpreter's contract is exactly three things: it COMPILES, it
   > REFUSES what it does not implement, and it GAINS NO CONSUMERS.**

   So the growth lands, and the legacy layer absorbs it with **a one-line
   refuse arm — which is the legacy layer's ONLY permitted growth.** That
   is the whole allowance: not a stub that half-works, not a TODO, and
   certainly not an implementation. A refusal is loud, fuel-independent and
   correct (§5.2 cause 1), so the legacy layer stays *true* without being
   *maintained*.

   **Both failure modes it forecloses are real.** Freezing the type blocks
   the new layer's capability on a layer that is supposed to be dying —
   the dead hand of the thing being retired. Implementing the arm in the
   legacy layer gives it a new consumer and a new reason to live, which is
   the opposite of erosion. The one-line refuse arm is the unique move that
   keeps the legacy layer compiling without giving it a future.

   **EXECUTED, and the first measured instance: the completeness lane's
   inch 3a.** The shared type grew; **the trunk took exactly one refuse
   arm**; and the change landed at **9 arms — the number the
   pattern-position law had just rescued from an identifier count of 35**
   (§5.4a). A ruling and a counting law, both minted within a day, paying
   off together in the same inch: the ruling said what the legacy layer was
   allowed to do, and the counting law said how much it would cost. Neither
   number nor shape moved on contact.

   **AND THE MIRROR-IMAGE DEFECT, measured as a master RED.** Erosion has a
   second direction nobody had ruled on: not the legacy layer growing, but
   the **TRUNK** growing after the branch cut. Rung 3b's **seven
   draining-consumer arms** landed on the trunk and were **merged without
   the capability crossing the presentation boundary** — so the rebuild
   **refuses what the trunk runs, on 25 rows.**

   **`diff_test` is blind to this class — but the blindness belongs to the
   AIMING, not to the instrument.** An earlier revision of this section said
   it was *"what a differential harness is"*; that was too strong, and the
   rebuild successor measured why. A differential compares **its two
   sides**, so when both sides are MODELS and both refuse, **parity holds
   while both are wrong.** Point the *same unmodified* `diff_test` at
   **CPython** — the branch with `--monadic` removed — and it **convicts**:
   *predicted 25, came back 25.*

   **So the law is not a limitation but a procedure.** *Agreement with the
   ORACLE is the evidence* becomes **operational by REMOVING THE SECOND
   MODEL**: with one model and one oracle, the ordinary harness already
   sees this class.

   **AND THAT HAS NOW HAPPENED — master truth, checked.** After the
   collapse, `Main.lean` imports `LeanModels.Python.Monadic` and calls
   **`Monadic.callInMono` AS the interpreter** (line 543, under a comment
   naming it exactly that). So `diff_test`'s **1427 / 0 / 116 / 1311**
   validates **the rebuild against CPython directly** — not one model
   against another. The second model is gone from the closed-function
   surface, and with it the blindness: this is the procedure above,
   executed rather than described.

   **A SECOND MEASURED INSTANCE, and it is smaller and therefore worse.**
   `for` has **three** entry paths — `execGen`, `SKont`, `Kont` — and the
   **third was missed**. `diff_test` could never have caught it, for the
   same reason: **the trunk refuses the same rows**, so parity held while
   both were wrong. The 25-row instance was a whole capability going
   missing; this one is **a single dispatch arm**, invisible by exactly the
   same mechanism. The class does not announce itself by size.

   > **Agreement between two models is not evidence. Agreement with the
   > ORACLE is.**

   That is **§5.3 one level up**: §5.3 forbids a run that executed nothing
   from scoring as agreement; this forbids **two refusals** from scoring as
   agreement. Same shape — a check finding sameness where there was no
   content — and the same fix: anchor the expectation outside the pair.

   **AND THE SAME SHAPE AGAIN, one level further out — applied not to
   models but to SOURCES.** A claim was supported by reading **two sources
   that agreed with each other**:

   > **Reading two sources that agree with each other is not verification
   > when both are about a THIRD THING the model does not use.**

   Two documents concurring tells you they concur. If the model's own
   constant is not the one they are about, their agreement is a fact about
   *them* — as unanchored as two interpreters both refusing. **The
   referent, not the concurrence, is what makes reading into evidence**,
   which is why the check is *read the model's definition*, not *read more
   sources*.

   **THE RULE:**

   > **Every merge across a presentation boundary owes a CAPABILITY-PARITY
   > AUDIT** — the census, run against **both** targets — and
   > **trunk-landed capabilities must RE-PRESENT in the rebuild before the
   > trunk arm may retire.**

   Without it, erosion silently loses capability: the trunk arm retires
   because the rebuild "agrees", and the agreement was two refusals.

   **AND AN AUDIT MUST LOOK AT THREE SITES, not two: a construct's meaning
   can be decided at INGESTION.** The corrected `pyc` design fuses at
   ingestion — `list(d.keys())` rewritten to `list(dictkeys(d))`, on the
   `ListComp` precedent — so the capability lives in **the ingestion
   rewrite**, not in the walker on either side.

   An audit that compares only the two interpreters **cannot see it**: both
   walkers are innocent, and the behaviour is decided before either runs.
   So the parity audit sweeps **the trunk, the presentation, AND the
   ingestion rewrites** — and a capability found missing on one side should
   prompt the question *"is this implemented as a rewrite over there?"*
   before it is filed as an unported fix.

   **AND THE TRIAGE RULE FOR WHAT THE AUDIT FINDS.** The audit surfaces
   divergences; it does not say how to read them, and the R-track lane
   corrected its own ledger on exactly that. It had recorded the 25
   dict-keys rows as a **tier-boundary disagreement needing a ruling**. The
   ruling was **"defect — rung 3b never crossed the presentation
   boundary."**

   > **When two interpreters of the SAME tier differ, the null hypothesis
   > is an UNPORTED FIX — never a boundary dispute.**

   It is a cost argument as much as a frequency one: **disputes are rare
   and cost a ruling; unported fixes are common and cost a line.** A prior
   that reaches for the expensive rare explanation will be wrong most of
   the time and expensively wrong each time.

   **And the recorded reasoning error is the transferable part**, because
   it is a mistake anyone reading a refusal will be tempted into:

   > *"I read a deliberate refusal MESSAGE as evidence of a deliberate
   > STATE — a refusal message is written at the DEFINITION SITE and says
   > nothing about whether reaching it HERE was intended."*

   A carefully-worded refusal proves someone thought about **refusing**;
   it proves nothing about whether **this path should have arrived**. The
   two are authored at different places and different times.

   **The tell was already in the lane's own log**: the **trunk answered**,
   **CPython agreed**, and **only one presentation refused** — which is an
   unported fix's signature and not a dispute's. A dispute would have the
   two sides disagreeing about what the *language* does; here they agreed,
   and one side simply had not been told.

   **AND THE AUDIT HAS AN END CONDITION, which is what makes it scaffolding
   rather than a tax: it is the rule for THE WINDOW IN WHICH TWO MODELS
   COEXIST.** When the second model goes away — when the presentation
   boundary closes and the harness's other side is the oracle again — the
   ordinary differential resumes covering this class on its own, and the
   audit retires with the window.

   **THE COROLLARY, and it is the maximal-trunk design paying off
   measurably: the fix cost ONE LINE.** The rebuild's single `iterValues`
   dispatch serves **six** consumers that the trunk pays **seven arms**
   for. The defect was expensive to *find* and trivial to *fix*, and the
   ratio is the argument — a design that concentrates dispatch converts a
   seven-arm capability gap into a one-line one.

   **The SEQUENCING rationale, which is about risk and not about Python.**
   `mvcgen` warns on every invocation that it is experimental, and one Std
   bug surfaced in twenty lines of probing (§3.4). **New tiers should
   absorb that tactic churn; the flagship estate should not.** A tier with
   no landed theorems pays nothing when a tactic's behavior shifts under
   it; a tier with a campaign's worth pays in re-proofs. So the order is
   the risk-weighted one, and it happens to also be the cheap one.

   §3.8 applies the same trigger discipline to `Run`.

**The pilot is landed** (`docs/mvcgen-pilot.md`, §L61) and its numbers
replace this section's earlier estimates throughout. Its recommendation:
new tiers adopt the substrate and use mvcgen on the fuel-free fragment,
**deciding fuel's fate BEFORE writing the interpreter** — which is a
founding-checklist item, not an afterthought.

**§3.4 HAS A GATE NOW: `tools/substrate.sh`.** `tools/laws.sh` measured this
section as the most-cited home in the tree with **no gate at all** — nine laws
at 21 ledger citations, more than any other unenforced section, and it is the
contract every tier's refusal vocabulary is built on. The census reports, per
tier: the monad as **ADOPTED / BY-SHAPE / OWN / NONE** (STMT-21, *by shape,
not by spelling* — the ES tier defines its own `SemM` with Core's name, and a
grep for the NAME would call that adoption); Core-channel refusal sites against
locally-declared ones; an uncatchability statement found **by pattern**
(STMT-19); whether the tier **has a run** (STMT-22); and two evaluators sharing
a signature, with their adequacy theorem or `OWED` (STMT-67, §8.5).

First run, 2026-08-23: **Python ADOPTED** with adequacy **OWED**
(`runScriptClockMono` beside `runScriptClock`), **Go ADOPTED**, **C and ES
BY-SHAPE** mid-adoption, **SV OWN**, and **Ada NONE** — ingestion only, no
evaluator in the tree yet. The tool distinguishes `OWED` from `TWINS?`, because
signature identity is **necessary and not sufficient**: `alloc / allocZeroed`
share one and are siblings, not rivals.

#### 3.4.1 THE FIT BOUNDARY — the substrate is for INTERPRETERS, and one tier found the edge

Recorded by the **Lean tier's founding lane** (`docs/lean-tier-charter.md`
§10.3, §L79), because this section says *"new tiers adopt the substrate"*
without stating for what, and the first tier to price the instantiation
honestly found it does not fit.

> **`SemM`/`Run σ α` is a substrate for INTERPRETERS: a program RUNS,
> consuming fuel, over a mutable world, producing effects. A tier whose
> subject is a JUDGMENT rather than a run does not have that shape, and
> forcing it would be measuring the substrate and calling it the
> language — principle I's failure mode, pointed inward.**

The Lean tier's subject is Lean's own kernel: a **recursive decision
procedure over an immutable environment**, returning `Except`. Mapping it
against §3.2's list, item by item and measured against a 7 888-line C++
kernel and a 39 468-line existing mechanization:

| substrate element | fit for a typechecker |
| --- | --- |
| `.unsupported` — loud, fuel-independent | **fits exactly** — it is REFUSE |
| `.timeout` — fuel exhaustion | **fits** — the kernel ships its own recursion-depth guard, and the existing mechanization uses fuel counters |
| `W` — heap, globals, stdout | **absent.** There is no mutable world; the environment only grows, monotonically, and is never destructively updated |
| effects as world data | **absent.** A typechecker has no observable effects |
| the schedule ∀-parameter (§3.6) | **absent.** Zero nondeterminism — the family's simplest ∀-resolution row |
| the ∃-fuel threshold form | **fits the shape, but the interesting theorems are not about fuel** — they are `checker accepts ⟹ the model admits it` |

**Two rulings this does NOT imply**, stated so the note is not over-read:

* **It is not an argument against the substrate.** Six of the seven
  language lanes ARE interpreters and the substrate is right for them.
  It is an argument against the word *"every"*.
* **It is not a licence to invent a second substrate.** The Lean tier's
  own conclusion is to **consume an existing mechanization** rather than
  build a surface at all (its option (b)), precisely because a
  from-scratch instantiation prices badly.

**The generalizable rule, and it belongs in the founding checklist:**
§8 step 7 already says *decide fuel's fate before writing the
interpreter*. This adds the question that comes **before** it:

> **Does this tier HAVE a run?** A tier whose artifact is a relation — a
> typechecker, a linker, a type system in isolation — answers no, and
> should say so in its charter rather than discovering it at step 7.

The Circuit and Spice lanes are the existing precedent (§0.2: they model
by enclosure and contract, do not use `Run`, and *are not asked to*). The
Lean tier is the second family of misfit, and unlike theirs it was found
by pricing rather than by inheritance — which is why it is cheap to
record now and would have been expensive to discover at inch 7.

#### 3.4.2 A TOOLING HAZARD: dot notation unfolds `def`s, and silently re-slots arguments

Found by the Lean tier (`docs/backlog/lean-tier.md`), and it costs a tenure every
time it fires, so it is recorded where proof authors read rather than in one
lane's log.

**The mechanism.** Lean resolves `h.foo` by the head constant of `h`'s type. When
that type is a `def` rather than a structure, elaboration may **unfold it first**
and resolve against the head underneath. In lean4lean, `HasType` is

```lean
def HasType (env : VEnv) (U : Nat) (Γ : List VExpr) (e A : VExpr) : Prop :=
  IsDefEq env U Γ e e A
```

so `h.instN` on a `HasType` hypothesis resolves to **`VEnv.IsDefEq.instN`**, not
`VEnv.HasType.instN`. Both exist. Both typecheck at the call site's arity. **They
take their arguments in different orders:**

| lemma | argument order |
| --- | --- |
| `VEnv.HasType.instN` | `(henv) (W) (H) (h₀)` |
| `VEnv.IsDefEq.instN` | `(henv) (h₀) (W) (H)` |

So `hA.instN henv W h₀` binds `W` where `h₀` is expected. The failure is a type
error at a *later* argument, or — worse — no error at all when two arguments
happen to share a type.

**Why it is worth a section.** The Lean tier's first red tenure was this hazard's
sibling: `hA.instL hls` resolved to `IsDefEq.instL`, which *did not exist in the
import closure*, and reported as `the environment does not contain
Lean4Lean.VEnv.IsDefEq.instL` — **a missing import wearing a name-resolution
error's clothes.** The same call was then green only because `instL`'s two
orders happen to agree. That is luck, not correctness, and the next lemma in the
same file does not share it.

**THE RULE: in a foreign proof tree, name the lemma explicitly.** Write
`VEnv.HasType.instN henv W hA h₀`, never `hA.instN …`. It costs six characters
and removes an entire class of silent mis-binding. The same applies to a tier's
*own* definitions the moment one is a `def` over another — the Lean tier's
`ProjField` (a `def` over `ArgFromRight`) is the same shape and got the same
treatment.

### 3.5 SOFTFLOAT — shared component #2, and the premise it was deferred on is FALSE

**The correction first, because the record is wrong.** Three tier documents
defer floats as though the problem were the *specification*. It is not.
**IEEE 754's arithmetic core is the best-specified thing in this family** —
better specified than C's sequencing, better than SystemVerilog's event
regions, better than anything CPython documents. For `+ − × ÷ √` and the
comparisons, the standard names one correctly-rounded result for every
input, and computing it is **decidable integer arithmetic on finite
encodings**. There is nothing approximate about it.

**AND THE TIER HAS NOW MADE THAT CONCRETE IN THE STRONGEST AVAILABLE FORM — A
SPEC-CONFORMANCE FACT EXTRACTED FROM AN IMPLEMENTATION BY PROOF** (SoftFloat's
arrival, ticketed).

> **"Core's rounding is no longer a bit procedure I reason AROUND — it IS
> round-half-to-even."** The four branches **ARE** §4.3.1's four cases.

**This is the endgame shape for every mirror tier in this family, seen once.**
The usual relationship between an implementation and a spec clause is *the
implementation is believed to satisfy the clause*; here **the branch structure
was PROVED to be the clause's case split**, which converts a body of bit
manipulation from an obstacle to reason around into **a citable statement of the
standard.** *A tier that can do this for a component stops needing a model of
it.*

**AND THE METHOD NOTE PAID TWICE, WHICH IS WHY IT IS RECORDED AND NOT JUST
NOTED**: *the one guess-driven attempt made it WORSE — 2 failing cases became
8.* **A guess in a domain with a decidable specification is strictly dominated**,
because the answer is derivable and the guess is not even cheap: it costs the
attempt plus the diagnosis of the six new failures. *Where the spec names one
correct result, reading it is the fast path, and this is the second measurement
that says so.*

**AND THE NEXT SHIFT'S WHOLE OBLIGATION REDUCED TO A DISTINCTION WORTH CARRYING
OUT OF THE TIER** (SoftFloat, ticketed): the carry-out is **REPRESENTATION AND
NOT VALUE**, with **evenness making the absorption lossless** —
`RoundWithAccuracyIsNearest` is now **down to the interleaving argument alone.**

> **A STEP THAT CHANGES THE REPRESENTATION AND NOT THE VALUE OWES A LOSSLESSNESS
> ARGUMENT, NOT A CORRECTNESS ONE — and the two have completely different
> shapes.**

**Naming which kind a step is collapses the obligation before any tactic runs**,
because a value-preserving re-encoding is discharged by an invariant while a
value-changing step needs the spec's own case analysis. *The tier reached one
remaining argument by classifying its steps rather than by attacking them* —
which is the analog tier's coordinate discipline in a different substrate, and
the second measurement this week that says **structure found before the prover
runs is worth more than the same structure found inside a tactic block.**

**The obstacle was believed to be Lean-internal, and on the pinned
toolchain it no longer exists.** `docs/completeness.md` §6 records the
float rung as gated because *"Lean's `Float` is not kernel-reducible, so
`#py_check` and every captured `rfl` run would break on it — the same
family as the mergeSort trap."* Measured today on
`leanprover/lean4:v4.33.0-rc1`:

```
-- (illustrative — probes run against the pinned toolchain, not tree files)
structure Float where toModel : Float.Model
structure Float.Model where
  toBits : UInt64
  valid  : Float.Model.Format.binary64.Valid toBits.toBitVec
def Float.add : Float → Float → Float := fun a b => { toModel := a.toModel + b.toModel }
```

`Float` is a plain structure over a bit-level model and `Float.add` is a
plain Lean definition. Three theorems were kernel-checked to confirm that
this reduces, not merely elaborates:

* `total = 6.75` where `total` folds `(· + ·)` over a `List Float` —
  reduction through a library higher-order function;
* `sumTo 4 = 10.0` for a user-defined structurally recursive
  `Nat → Float` — reduction through the shape an interpreter has;
* `((0.1 : Float) + 0.2 == 0.30000000000000004) = true` — correct binary64
  rounding, which is the fact that matters.

All three depend on `[propext, Classical.choice, Quot.sound]` and nothing
else — **rung 1 and rung 2 of §0.1 II(a), with no `native_decide` needed
and none used.** Core ships **1856 lines**
of logical model under `Init/Data/Float/Model/` — a width-parametric
`Format` (`mantissaBitsWithoutImplicit`, `exponentBits`) with **both
`binary64` and `binary32`**, an unpacked representation, a rounding layer
whose `Accuracy` type encodes exactly "exact, or inexact and where the
infinitely precise value sits relative to the approximation plus half an
ulp", packing lemmas, and operations `Add Sub Mul Div Sqrt Compare Sign
Status OfNat OfScientific ToNat`. Its own header says it is *"part of the
logical model for floats which authors of float libraries need to rely
on."*

**So the component is not "write a softfloat". Layer 1 already exists.**

#### 3.5.1 The two layers

**Layer 1 — executable bit-level operations.** What interpreters observe.
Kernel-reducible and **width-parametric down to the packed boundary**
(`binary32` and `binary64` are instances, not definitions — see the
requirement below). **Supplied by core Lean on the pinned toolchain**; the family's work here is to
*depend on it deliberately* — pin the interface, gate the reduction
behaviour with `#guard`s the way every other tier gates its primitives, and
own the residue core does not cover.

**Layer 2 — the SPEC ALGEBRA, and this is what the family builds.**
Per-operation correctness, proved once, in IEEE form:

```
-- (illustrative — the obligation shape, not a tree file)
op_correct (fmt : Format) :
    bitOp fmt x y  =  round fmt mode (exactRational (val x ∘ val y))
```

##### LAYER 3 — TRANSFER, and core COMMISSIONS it explicitly

The two layers above are not the whole component, and core says so in its
own words. `UnpackedFloat`'s docstring disclaims the role outright: it is
**not a goal of that development** to be the basis of a general-purpose
float library *"or to have any direct lemmas written about it at all."*
Users wanting such a library should

> develop it **completely separately**, prove the operations **equivalent**
> to core's, and then **transfer lemmas** to `Float` and `Float32`.

**So the third layer is TRANSFER, and it is commissioned rather than
optional.** This sharpens §3.5.1's "layer 1 is free": core supplies the
*executable* model for free and **explicitly declines to be a proof
basis**. The family's layer 2 is the separate library core asks for; layer
3 is the equivalence-and-transfer bridge that makes layer 1's reduction
usable in a proof about `Float`.

It also explains the shape of the work: without transfer, a theorem about
our `Format`-parametric algebra says nothing about the `Float` an
interpreter actually observes, and a `#guard` on that `Float` attests only
the runtime (§5.4). **Layer 3 is what joins the two oracles the differential
pair names.**

**AND THE NaN PAYLOAD IS UNSATISFIABLE OVER CORE'S MODEL — an open Thomas
decision.** §3.5.4 routes NaN payload and sign to ∀-resolution, quantifying
over the admissible payloads. Core's `UnpackedFloat` states plainly:
*"There is no payload attached to a NaN in this format."* **You cannot
quantify over a payload the type does not have.** So the routing §3.5.4
prescribes is not available on core's model as it stands, and the choices —
carry our own NaN representation in layer 2, restrict the claims to
payload-independent facts, or accept core's payload-free NaN as the
family's answer — are **Thomas's**, not this document's. Registered as
open.

##### WIDTH-PARAMETRICITY IS A REQUIREMENT, not a description

Thomas's directive, and it is binding on this component: **the Float spec
must be width-parametric — no hard-coded mantissa or exponent widths.**
Three clauses.

**(1) THE SPEC ALGEBRA IS DEFINED OVER A GENERAL `Format`** — exponent
width and significand width as **parameters**, mirroring IEEE 754-2019's
own §3.3 parameterization of formats. **`binary16`, `binary32`, `binary64`
and `binary128` are INSTANCES, never separate definitions.** A component
that defines "the binary64 algebra" and later "the binary32 algebra" has
already lost: it will carry two of every lemma, and the second copy is
where the divergence lives.

**(2) EVERY LAYER-2 THEOREM IS STATED OVER THE GENERAL `Format`.** The
`op_correct` family above quantifies over `fmt`. Width-specific theorems
are admissible **only** as (a) instance corollaries — `op_correct
binary64` — or (b) `decide`-closed **base cases** of an induction, per the
§0.1 II(a) ladder. Thomas, precisely: *decide can be useful for the
inductive base case, but width-parametric theorems are usually desired.*
This is the ladder's rung 1 with a component-specific edge: here, rung 1 is
not merely preferred, it is the deliverable.

**(3) THE ALIGNMENT CHECK ON CORE, verified at the pin — and it has a
boundary that must be FLAGGED, not absorbed.** Measured:

| core declaration | width-parametric? |
| --- | --- |
| `Float.Model.Format` (`mantissaBitsWithoutImplicit`, `exponentBits`, `numBits`) | **yes** — the parameter record itself |
| `Float.Model.Format.Valid : (spec : Format) → BitVec spec.numBits → Prop` | **yes** — indexed by the format |
| `Float.Model.UnpackedFloat` | **yes** — width-agnostic; the format is not baked into the type |
| `UnpackedFloat.add : Format → UnpackedFloat → UnpackedFloat → UnpackedFloat` | **yes** — takes the format as an ARGUMENT |
| `Float.Model` | **NO** — zero parameters; hard-codes `Format.binary64` and `UInt64` |
| `Float32.Model` | **NO** — zero parameters; hard-codes `Format.binary32` and `UInt32` |

**Core's parametricity stops at the PACKED boundary.** Everything beneath
it — the format record, validity, the unpacked representation, the
rounding layer and the operations — is parametric; the two packed wrapper
types are per-width duplicates. So the requirement has a concrete
consequence: **build layer 2 over `Format` + `UnpackedFloat`, never over
`Float`/`Float32`.** The moment a theorem mentions `Float`, it has
hard-coded binary64 and clause (2) is violated silently, because nothing
about the statement looks width-specific.

Where core's API forces a fixed width, the tier **flags it** — records the
declaration, states which widths it therefore cannot serve, and either
wraps it parametrically or reports the gap. It does **not** absorb the
fixed width into our layer and call the result general.

Downstream proofs then target **round-of-exact** and never our bit
algorithm. A SystemVerilog divider proof says "these output bits are the
correctly-rounded quotient", not "these output bits equal what
`Float.Model.div` computes" — the second is a tautology about an
implementation, the first is the theorem anyone wants.

**Why both layers are kernel-computable, which is the fact that makes this
tractable.** For `+ − × ÷ √` and `fma`, the **exact** result of finite
binary64 inputs is a **RATIONAL** number — sums, products and quotients of
dyadic rationals are rational, and `√` is decidable by comparing squares
rather than by computing a root. Rounding a rational to a format is finite
integer arithmetic on its numerator and denominator. **ℝ never appears.**
It enters only with the transcendentals, which is exactly why they are
deferred (§3.5.4) and exactly why deferring them costs the core nothing.

#### 3.5.2 The flagship theorem shape — cross-tier, in the family's own pattern

Thomas named the client: *proving a SystemVerilog circuit computes
floating-point division correctly.* That theorem factors the way the C
charter's twin-bridge theorem factors — **through a shared vertex, never as
a comparison of two models**:

> the SV tier runs the circuit and yields output BITS;
> SoftFloat layer 2 says what those bits must be — `round (exact quotient)`;
> the theorem is that the two agree, for all inputs in the claimed domain.

The circuit side is an ordinary SV-tier obligation; the specification side
is one `op_correct` instance; neither side knows about the other's
internals. This is the verified-FPU tradition — the AMD K5 divider and its
ACL2 lineage are the precedent, **cited and not vendored** — restated in
this family's shared-vertex pattern. Flocq is the corresponding precedent
for the layer-2 algebra itself, and likewise cited only.

**The circuit-side foothold, censused, because the obvious guess is
wrong.** `LeanModels/Circuit/` is **not** it. Measured: that lane imports
`Mathlib.Data.Real.Basic`, `Mathlib.Analysis.Calculus.Deriv.Basic` and
`Mathlib.MeasureTheory.*`, and its subject is `DCBlock`, natures,
disciplines, DC/AC/transient analysis and interval enclosures — it is the
**analog** lane, continuous-time physics over ℝ, and a floating-point
divider is a synchronous digital datapath. The two lanes share exactly one
edge in the whole tree: `Circuit/MixedSignal.lean` imports
`LeanModels.Sv.Surface`, which is the analog↔digital boundary and not a
shared circuit model. **The divider theorem's circuit side is the SV tier**
(`LeanModels/Sv/`, and the parametric `sv-0.2` layer in particular). A
founding lane that goes looking in `Circuit/` will find calculus.

#### 3.5.3 Consumers — and ECMAScript BLOCKS on this

| tier | need | consequence |
| --- | --- | --- |
| **ECMAScript** | its **only** number type is binary64 | **BLOCKING.** A float-free JS core slice is very nearly empty — no arithmetic, no array index arithmetic, no `length` comparison in its true type. The ES founding lane's charter must state SoftFloat as a **dependency**, not defer floats the way the Python lane could. |
| WebAssembly | `f32` and `f64` | needs the component **width-parametric**, which core's `Format` already is (`binary32` and `binary64` both present). Wasm is also where the NaN residue is specified rather than hand-waved (§3.5.4). |
| C | Annex F rung | unblocks the rung whose gate was "neither host declares `__STDC_IEC_60559_BFP__`" — that gate is about the *oracle's* conformance claim and stays; the *model's* half is answered here. |
| SystemVerilog | `real`, and the divider flagship | §3.5.2 |
| Python | `float`, `/`, `**` with negative exponent, `str`/`repr` of a float | the four grammar rows `docs/completeness.md` names, on a premise that has now moved. |
| Go | `float32`/`float64` | same component, no new work. |

#### 3.5.4 The genuinely unspecified residue routes to EXISTING machinery

Nothing here needs a new mechanism, and saying which mechanism is the
point:

* **NaN payload and sign** — genuinely unspecified by IEEE 754 for most
  operations. Routes to **∀-resolution** (§3.4's explicit-parameter
  design): the payload is a parameter, quantified at theorem level.
  WebAssembly is the exemplar because its specification *enumerates* the
  admissible NaN result patterns rather than leaving them to folklore, so
  the Wasm tier can state the ∀ precisely and the other tiers can copy the
  shape.
* **Excess precision and FP contraction** (`FLT_EVAL_METHOD`, fusing
  `a*b+c` into an fma) — these are **profile items**, exactly like
  `char_signed` and `sizeof(int)`: facts a host either provides or does
  not, pinned as a schema with a `#guard` per host and a loud rejection by
  name.
* **Transcendental accuracy** — C leaves it implementation-defined,
  ECMAScript calls it implementation-approximated. Routes to
  **REFUSE(`environment`)** — an unmodeled library function — or to a
  profile pin where a tier's oracle documents a bound. It never routes to
  an invented answer, and it is the only place ℝ would be needed.

#### 3.5.5 The price, honestly

Layer 1 is **free on the pinned toolchain** and its cost is a pin plus
gates. Layer 2 is the build, and it has a natural order:

1. **Base operations and comparisons** — `+ − × ÷ √`, the six comparison
   predicates, and the exact-rational bridge they all share, **all stated
   over a general `Format`**. This is the component; everything below is a
   widening.
2. **Conversions** — integer↔float both directions, and format-to-format
   conversion **stated between two general `Format`s**, of which
   `binary32 ↔ binary64` (what Wasm needs) is an instance.
3. **Decimal parsing and printing — its own sub-inch, and larger than it
   looks.** Correctly-rounded decimal↔binary conversion is a real
   algorithm, and it is where `printf`'s `%f` lives. The C tier's own
   census says float conversions are 21% of c-testsuite's format specs and
   10% of Fujitsu's, so this sub-inch is what unblocks that slice — and
   nothing before it needs it.
4. **`fma`** — one more correctly-rounded operation, same shape as (1),
   and the one C's contraction question resolves against.
5. **Transcendentals — LAST, and only per-tier need.** They are the only
   part that leaves the rationals, and no tier in the family has
   demonstrated a need for them.

**A build lane is commissioned on this plan.** Its first deliverable is
step 1's census in the family's own pattern (§5.4): which operations each
existing tier's corpus actually reaches, measured, before any Lean.

**And the stale record is corrected in three places.** The claim in
`docs/completeness.md` §6, and the float deferrals in
`docs/c-semantics-design.md` §1.3 and `docs/c23-goal.md` §5.3, were
correct when written and are now correct only about their *oracle-side*
halves. The Lean-side premise is measurably false on the pinned toolchain.
Whether a tier's oracle declares Annex F is still a real question; whether
Lean can compute a correctly-rounded sum in the kernel is no longer one.

### 3.6 CONCURRENCY — the four-piece pattern, and it is the ∀-parameter ruling at scale

The goal, stated by Thomas: *prove a multithreaded C program correct for
**all** possible interleavings — and where it is not correct, be unable to
prove it AND able to exhibit a counterexample.* That is not a misfit. It is
§3.4's explicit-parameter design at a larger scale, and it needs no new
architecture. Four pieces.

**(1) INTERLEAVING SEMANTICS — the schedule is a parameter.** A schedule is
an explicit input: a thread-choice stream, exactly the shape §3.5.4 gives
a NaN payload and §6.2 gives an entropy stream. The interpreter is
**deterministic per (program, schedule)** — and, precisely, per observable
(§6's determinism-indexing sibling) — so `SemM`, `fuelMono`, the
∃-fuel threshold form and `mvcgen` are all untouched — a threaded step
function is `sched → Nat → SemM W ρ α`, and nothing about the monad
changes. Correctness is then the ordinary shape:

    ∀ schedule, the run under that schedule satisfies the spec

The ∀ lives at theorem level, where this family already puts every
resolution of nondeterminism.

#### (1a) `SemM` CANNOT SUSPEND — and the pattern survives only because the
process table lives in W

**The claim above is true and its stated reason was wrong**, which the SV
lane's scheduler-first assessment found by trying to build on it. The
sentence *"nothing about the monad changes"* invites the reading that **the
monad carries the concurrency. It does not. `W` does.**

**The structural fact, verified by `rfl` on this substrate:**
`ExceptT ρ (StateT W Halt) α` unfolds to `W → (Except ρ α × W)`. A
computation therefore returns **an `α`, or a `ρ`, plus a `W` — and there is
no third case.** `StateT` is **run-to-completion**: there is nowhere in the
monad to put *"paused here, resume at this point."* No arrangement of these
transformers gains a suspension case, because none of them has one.

So any language whose processes **pause mid-body** — SystemVerilog's
`@`/`#`/`wait`, and eventually goroutines blocked on a channel — cannot
express suspension as an *effect*. It must **DEFUNCTIONALIZE**:

* **the continuation becomes DATA in `W`.** SV's form is
  `ProcState.residual`: the remaining statement list. This is **sound
  because suspension points are SYNTACTIC** — a process can only pause at a
  construct the grammar names, so "where it paused" is a position in the
  program text and not an arbitrary closure. A language that could suspend
  at an arbitrary point would need a real continuation and this trick would
  not be available.
* **the interpreter becomes a SCHEDULER LOOP** over the process table,
  rather than a walk down one process's body.
* **AND ITS MIRROR — the limit on what a plan may carry.** The rule above
  says a continuation *may* become data. The mirror says what that data
  may not be, and the two are one rule:

  > **A pure plan may decide WHAT to do — but it must never supply a term
  > the definition then RECURSES ON.**

  The reason is the measure, and it differs by half:

  * **in the FUELED half the plan is free**, because **fuel is the
    measure** — the recursion decreases whatever term it is handed;
  * **in the FUEL-FREE half the measure IS THE SYNTAX**, and **a
    plan-supplied term erases it** — a computed scrutinee is not a
    syntactic subterm of anything.

  So: **data may carry the DECISION; it may not carry the SCRUTINEE.**
  That is step 10's *reconstructed node* generalized — a rebuilt node is
  merely the most obvious way to compute a term the recursion then eats,
  and any plan that produces one has the same effect on the measure.

  **AND THE PAYOFF CASE FOR WRITING *WHY* AT THE SITE.** The file's own
  comment sat **three lines above the attempted edit**:

  > *"The free-scrutinee discipline is load-bearing twice over — it is
  > also what keeps this block structurally recursive."*

  **That is the positive counterpart to §5.4's two docstring laws**, and
  the distinction is worth stating plainly so they are not read as *"do
  not write prose"*: a docstring asserting a **FACT about the world** (a
  reachable set, a case that cannot arise) is **a claim, and needs a
  check**. A comment recording **WHY a constraint exists**, at the site it
  constrains, is **guidance** — it cannot be wrong about the world because
  it makes no claim about the world, and it is read exactly when someone
  is about to violate it. **Write the second freely; gate the first.**

* **suspension is a RETURN VALUE, not an effect** — the step function
  answers *"finished"* or *"suspended, with this residual"*, and the
  scheduler decides who runs next.

**The worked example, and its shape is the reusable part.** SV's
`stepProcess` **subsumes `execStmts` by one field** plus an
adequacy-shaped lemma: the ordinary statement walker is the special case
where nothing suspends, and the lemma says so. That is the migration path
for any tier that starts sequential and later grows concurrency — you do
not rewrite the walker, you generalize its return type and prove the old
one is the non-suspending case.

**THE LAZINESS LAW — a defunctionalized knot must ASK for what the trunk
gets free, and asking is INVISIBLE.** This is the pattern's sharpest trap
and it was found by a gate **stalling**, not by reading.

The obvious spelling binds the successor level with a `let`:

```
-- (illustrative — the WRONG spelling, not a tree file)
| fuel + 1 => let K := kont m fuel
              { call := fun … => … K …, … }
```

**`let` is STRICT.** So constructing `kont m F` forces the entire chain
down to 0 **before a single statement runs** — **O(F) work and O(F) stack
per entry**. The fix is one property: **every field takes its successor
level INSIDE its own lambda**, making construction O(1) and forcing the
chain exactly as deep as the run actually goes.

**Why this is a trap and not merely a bug: the answers stay CORRECT.** Only
the constant explodes, so nothing fails — it survived **three green gate
runs** at the closed-function surface's fuel of **10 000**, where the waste
is invisible. Script mode runs at **1 000 000** and stalls outright, having
executed nothing at ~0% CPU.

> **The trunk gets laziness FREE by matching `fuel` inside each function,
> so only the levels actually reached are ever built. A defunctionalized
> knot has to ASK for it — and every `#guard` runs at low fuel and hides
> the omission.**

Any tier adopting (1a)'s shape inherits this, because it is a property of
defunctionalization and not of SV or Python: the moment a continuation
becomes data, the language stops arranging its laziness for you. A tier
whose gates all run at low fuel has **no evidence either way** — that is
§5.4a's provenance law again, with fuel as the state the measurement was
taken in.

**CORROBORATION FROM INSIDE THE SV TIER, and it is convergent evolution
rather than analogy.** SV's dormant `SelfCheck.lean` **already hand-rolled
the `ρ` layer**: `$finish` executes as `.ok` with `halted := true` set in
the output record, output preserved, and **every downstream statement
short-circuits on the flag** (`if out.halted then .ok …`, at the statement
walker and again at the process fold). That is `ExceptT ρ`
**defunctionalized into the state** — the same move (1a) prescribes for
suspension, applied to termination — and it was written **2026-07-21,
thirty-two days before this substrate was specified**, by a lane that had
no substrate to read.

**A pattern a tier REINVENTED under pressure is stronger evidence than a
pattern a document prescribed**, which is why it earns a paragraph here
rather than a footnote. And it locates the boundary precisely: the tier
reached for state-plus-short-circuit for an effect the substrate **does**
supply (`ExceptT`), which is exactly why (1a) can be confident the same
technique is the right answer for the one it **cannot** (suspension).

**It also hands the migration its smallest worked example.** Replacing the
`halted` flag and its manual short-circuit with the `ExceptT` layer is
**one `@[spec]` lemma that deletes a check from every statement case** — a
tier-sized version of §3.4's altitude law, and the cheapest possible first
step for the SV consolidation lane.

**What this costs the pattern: nothing — and that is the test it passed.**
Schedule-as-parameter survives, `fuelMono` survives, the ∃-fuel form
survives, `mvcgen` survives. But they survive **because the process table
is World data**, so the scheduler loop is an ordinary state-threading
program over it. Stated precisely: **the monad carries one process's step;
`W` carries the concurrency.** A tier that reads §3.6 as "the monad handles
threads" will design a suspension effect, discover it cannot exist, and pay
for the discovery.

**AND THE OBLIGATION THAT COMES WITH THE SCHEDULER LOOP — DISCHARGED, and it
is the pattern every tier that takes this route will owe** (SV, `b499afa`, on
master). Defunctionalizing produces a **second** interpreter shape: the
resumable stepper beside the walker that was already there. The ruling is that
the walker does **not** retire:

> **`execSStmts` is RECOVERED as the NON-SUSPENDING CASE of `stepSStmts`, not
> superseded — proved, so the two cannot drift into a second interpreter.**

The old definition becomes a **theorem-backed special case**. That is the whole
of the discipline, and it is cheap **only at the moment the stepper is
introduced**: the agreement theorem is provable then, when the stepper was
built to generalize the walker and nothing has diverged yet.

**THE CONTRAST THAT PRICES IT is inside this repository — the Python
trunk/rebuild window.** There, both implementations stayed **executable**, and
that single fact is why the tier needed the **whole capability-parity
apparatus**: a parity audit sweeping trunk, presentation and ingestion rewrites
(§3.4, `2026-08-23-architecture-23`), a census of what each side can do, and a
standing question of which one a finding is about.

> **Two EXECUTABLE implementations of one semantics cost a parity APPARATUS.
> One executable plus one theorem-backed SPECIAL CASE costs a THEOREM.**

Both are legitimate — the Python window was a deliberate migration with the
apparatus priced in — but **the choice is made at the moment the second
implementation appears, and only then is the cheap option available.** A tier
that ships a stepper without the agreement theorem has silently chosen the
expensive one, and will not find out until the two answers differ.

**For the Go tier specifically: goroutine parking takes this exact shape**
— a blocked goroutine's continuation becomes data in `W`, the runtime
becomes a scheduler loop, and parking is a return value. Go's charter
should **cite this section rather than re-derive it**; the only thing that
differs is which syntactic constructs are the suspension points.

**(2) THE COUNTEREXAMPLE IS FIRST-CLASS, and this is a capability worth
naming.** Because the interpreter is deterministic per schedule, a
violation witness is a **finite, concrete schedule** — and it is checked
by *running* it:

```
-- (illustrative — the witness shape, not a tree file)
#guard (run prog badSchedule fuel).observable == theWrongAnswer
```

A kernel-checked, executable counterexample. This is the house law —
*every refusal path RUN, not admired* — applied to bug-finding rather than
to instruments. **Failure to prove correctness comes WITH an exhibitable
breaking interleaving**, which is precisely the asymmetry Thomas asked
for: the artifact cannot be talked into a proof, and when it declines it
says why in a form a human can replay.

This is **§0.1's exit (a)** made concrete, and it is the reason the
doctrine's third principle is constructive rather than a shrug: when a
proof does not come, the framework's first move is to try to hand back a
run that shows why it should not have.

**(3) THE DRF-SC FENCE, spec-mirrored — the standard's own clause carries
the bridge.** Full C11/C23 atomics exceed interleaving semantics: relaxed
and acquire-release orderings admit behaviors no interleaving generates.
The bridge is in the standard, and the citations below were **verified
against N3220 by the §2.1 instrument** rather than quoted:

* **C23 §5.1.2.5 ¶35** defines a data race — two conflicting actions in
  different threads, at least one non-atomic, neither happening before the
  other — and states that any such race **results in undefined behavior**.
* **C23 §5.1.2.5 NOTE 18** states the DRF-SC guarantee in the standard's
  own words: programs that prevent all data races using simple mutexes and
  `memory_order_seq_cst` operations, and no other synchronization, behave
  **as though their threads' operations were simply interleaved**, each
  value computation reading the last value stored in that interleaving —
  *"normally referred to as sequential consistency"* — and this **applies
  only to data-race-free programs**.
* **C23 Annex J.2 item (5)** indexes it: *"The execution of a program
  contains a data race (5.1.2.5)."* — so the refusal is J.2-numbered, and
  §2.1's finding that C23 numbered its UB list pays off here concretely.
* The coherence and ordering requirements the guarantee rests on are
  **§7.17.3 *Order and consistency***, whose number is stable across C17
  and C23 (verified — one of the minority that did not move).

**One honesty note, because it is load-bearing.** NOTE 18 is a NOTE, and
notes are informative rather than normative in ISO drafting. The
*normative* basis is ¶35's UB-on-race plus §7.17.3's ordering rules; the
note states the consequence. A tier that cites the note as if it were
normative would be making exactly the kind of overclaim §2.5 caught.

**What this buys.** DRF itself has a theorem-friendly interleaving
characterization — a program has a race iff there is an SC execution in
which two conflicting cross-thread accesses are adjacent — which is a
∀-schedule statement in our own terms, provable by the machinery of piece
(1). So: **the axiomatic model stays OUTSIDE the artifact, and the
standard's own clause is what lets it stay outside.** A racy program is UB,
which is REFUSE(`undefined`) indexed at J.2 (5) — **with the witness
schedule attached**, per piece (2). The refusal is not a shrug; it is a
bug report.

**(4) PROOF-BURDEN TIERS — three, and the default is the cheap one. All
three are LIBRARY, none is semantics (§0.1, principle II).** Piece (1)
fixed what correctness MEANS, quantified over every schedule; these are
three ways to find a proof of it. None of them may narrow the ∀, and their
incompleteness is expected rather than concealed.

| burden | method | analogue already in the tree |
| --- | --- | --- |
| **bounded fixture** | ∀-schedule is **DECIDABLE** by exhaustive exploration of the finite schedule space, checked as a battery | the census-battery pattern (§5.4) |
| **general theorem** | commutativity / **mover** lemmas (Lipton's reduction): show adjacent steps commute, collapse the schedule space | the concurrency analogue of `@[spec]` and the altitude lemmas (§3.4) |
| **heavy artillery** | ownership / separation-logic (Iris-style) reasoning | **named, not the default** — reached for only when movers fail |

The first tier is the important one: for a bounded fixture, "correct for
all interleavings" is a *computation*, not a proof, and it lands as a
`#guard` battery on day one.

**UNIFICATION — Go and C-threads are ONE pattern with two citations.** Go's
memory model is explicitly DRF-SC, so a Go tier and a future C-threads
extension share pieces (1), (2) and (4) verbatim and differ only in which
document supplies piece (3). Building either builds most of the other, and
a lane founding one should say so in its charter.

**But they differ sharply on what a RACY program means, and the scoreboard
must not pool them.** C says a data race is **undefined behavior** — no
bound at all — so a racy C program is REFUSE(`undefined`), as above. Go
does **not**: it bounds what a racy program may observe, describing the
permitted outcomes rather than surrendering. **A racy Go program is
therefore not a refusal — it is a MEMBERSHIP site**, scored by §5.1's rule:
the model is right when its outcome is *one of* the permitted ones. Mapping
Go's bounded races onto C's `undefined` would refuse programs Go fully
describes, which is the same false-statement-about-the-language error §4.3
catches at Ada's bounded errors. Same shape, three languages.

The Go charter sharpens what that membership set contains: it is
**size-stratified**, and **`halt-with-race-report` is always in it** — a
race detector stopping the program is itself a *permitted* outcome, not a
divergence from the ones that do not. A scoreboard that treated the
report as a failure would manufacture exactly the DIVERGE §5.1 forbids.

**THE RESIDUAL TRUE MISFIT, narrowed to one sentence.** What remains
genuinely outside is **verifying the relaxed-atomics fragment itself** —
reasoning about programs that deliberately use `memory_order_relaxed` or
acquire-release beyond what DRF-SC covers. Those behaviors are defined by
axioms over execution graphs rather than generated by any schedule, so the
"parameter" would be the graph, and the artifact would become a
consistency CHECKER — a different architecture (§6.1).

**AND THE ∀-PARAMETER RULING NEEDED ONE REFINEMENT, SUPPLIED BY THE ANALOG TIER**
(A12, ticketed; verify at landing). A world believed **pinned** had a **free
coordinate**: no uniform rate bound exists over the supply, because the rate
**→ 0 as supply → threshold⁺**.

> **A WORLD IS NOT "PINNED" OR "FREE". EACH COORDINATE IS.**

**The whole-world adjective is the defect**, and it is the unit family in a new
dress: *"pinned" is a summary of a vector*, and a summary that a lemma quantifies
over will be wrong on exactly the coordinate nobody named. **The corollary
therefore carries `hsupply = 5` EXPLICITLY** — the pin, written where the theorem
can be read, rather than inherited from a word.

**And the lane convicted its own prior error one level finer**, which is what
makes this worth a section rather than a footnote:

> **"Both times, the shape I checked was REAL and the shape I skipped was the
> one that MATTERED."**

*A verification that confirms a true property is not evidence about the property
you did not check* — and a true confirmation is **more** dangerous than a false
one, because it discharges the feeling that prompted the check. **The remedy is
the coordinate list, not more care**: enumerate what the world is made of, and
mark each one **pinned or free, by name.** *Any tier with a structured world owes
that list;* the concurrency parameter above is one coordinate of it, and this
register had been treating it as the whole vector.

### 3.7 `Span` — the ruling on three shapes

Measured, three span types for seven lanes:

| type | shape | lanes |
| --- | --- | --- |
| `LeanModels.Span` | 4 fields: `lineno`, `colOffset`, `endLineno`, `endColOffset` | Python, C |
| `LeanModels.VerilogA.Span` | 2 fields: `line`, `column := 1` | Verilog-A |
| `LeanModels.Circuit.Spice.SourceSpan` | 1 field: `line` | Circuit, Spice |

And the "language-neutral" one is not neutral: its own docstring says the
field names *mirror CPython's `ast` attributes*. A C span is a clang span
wearing CPython's field names.

**Ruling.** `Span` stays in `Core` and is the family's span, with the
docstring corrected to state the *contract* (1-based lines, 0-based
columns, exclusive ends) rather than its Python provenance. The two
divergent types are **not** defects to be merged on sight: Verilog-A and
SPICE genuinely observe less (a line, or a line and a column), and
widening them would manufacture end positions their frontends do not
report. The rule is therefore

> a lane MAY narrow the family span to the positions its frontend
> actually reports, and MUST NOT re-declare a type with the same name at
> a different shape.

`VerilogA.Span` violates the second half — same name, different shape, in
a sibling namespace — and is renamed when that lane is next open. The C
envelope's two-location spans (spelling and expansion, forced by six
function-like macros) are the model for how a lane EXTENDS rather than
redeclares.

### 3.8 `Run`'s move to `Core` — deferral CONFIRMED, trigger FIXED

`docs/c-tier-charter.md` §2.4 priced the move and deferred it. The
deferral is confirmed and two things about it are made concrete, because
"later" is not a trigger.

**Destination:** `LeanModels/Core/Outcome.lean`, with
`LeanModels/Python/Runtime.lean` re-exporting so no Python call site
changes.

**Trigger — RE-DERIVED, because its old premise was false.** This section
previously leaned on `Run` already having two lane consumers. It does not:
type-aware, it has **one, Python** (§3.1). So the trigger cannot be "when
the second consumer appears" as an observation about the present; it is a
statement about which lane arrives first, and there are now **three
candidates**:

| candidate | status | would it trigger? |
| --- | --- | --- |
| **C's M2 inch 4** — statements + `CWorld` | planned; C is at inch 1 and uses its own `CRes` at the value layer | yes — the first C code that needs a world |
| **the rebuild lane's `SemM`** | **LANDED — this was the first-arriving trigger** | **FIRED** — and it arrived as the stack, not as bare `Run` |
| a third tier adopting the outcome type | none proposed | yes |

**Whichever lands first is the trigger**, and the rule is unchanged in
substance: the move happens when a second consumer exists, not before
(the ingester tier does not mention `Run`) and not after (a second
interpreter landing with its own copy of `Run` is a defect, not a design).

**And §3.4 collapses this question into one.** `Run σ α` is a
**faithfully-embedded VIEW** of `ExceptT ρ (StateT W Halt)` — a retract,
`toRun ∘ ofRun = id`, **not** the isomorphism this section first claimed
(§3.4 carries the correction). So "move `Run` to `Core`" and "land the
`SemM` substrate" are still **the same landing**, not two: the destination
is the stack, with `Run` as its established view, so a lane arriving by
either route finds one artifact. What changes is the direction of travel —
**`Run`'s theorems lift into the stack; the stack's facts do not descend
into `Run` without passing through the residue theorems.**

**And the price is drifting.** §L35 measured 1251 `Run.` sites in 24
files; today it is **1282 in 31**. The deferral is correct and it is not
free, which is precisely why the trigger is a named landing rather than a
judgement call.

The `Run.exn` payload decision (`Run σ ε α`, or C's terminal riding in α)
belongs to the same inch. It is the one place the outcome type is not yet
neutral, and naming it here is cheaper than discovering it there.

**AND THE SECOND CONSUMER HAS SETTLED WHICH WAY IT GOES.** Ada raises
**identities**; ES throws **values**. Both fit with no negotiation, because
`ρ` is a **parameter** and never a shared enumeration. So **`ε` does not
need to be settled centrally at all** — the answer is *parameterize*, which
is what the family already does everywhere it has two consumers. The ES
charter's *"where does `RVal` live"* question therefore **dissolves rather
than being answered**: it was a question about a type that was never going
to be shared. The same move rules `RefusalCause` (§5.2) — classes in
`Core`, payload per tier — and the two rulings are one idea applied twice.

---

## 4 THE AUTHORITY TAXONOMY

### 4.1 THREE authorities, and a tier declares which it is

**SPEC-MIRROR.** A published normative document defines the language. The
model's obligation is **clause coverage**: every clause the tier claims is
realized by a declaration, and the manifest says which. C, SystemVerilog,
WebAssembly, ECMAScript, Ada, RISC-V.

**INTERPRETER-EXTRACTION.** No normative document is the authority in
practice. The model's obligation is **differential agreement**, and the
differential harness IS the extraction instrument. Python, SPICE,
Verilog-A.

**OFFICIAL-SUITE — the third, added by the Ada charter.** A conformance
suite exists that is owned by **neither the standards body nor an
implementer**, and ships **its own published grading rules and its own
grading tool**. Then the model's obligation on a suite test is neither
"match the document" nor "match an implementation" but **"earn the verdict
the suite's grader assigns"**, and the suite owner is the authority for
what that verdict is.

This is a genuinely distinct third thing and the family already contained
both poles without naming the axis. **C has no official suite at all** —
`docs/c23-goal.md` opens by saying so, which is precisely why its goal had
to be *restated* as agreement with three compiler projects' regression
histories, and why its §4.3 has to warn that a high score means "agrees
with what these projects test", not "conforms to ISO 9899". **Ada has the
opposite**: ACATS 4.2, 4 188 tests, six named classes, and an
implementation-neutral event-trace format that makes the grade
machine-readable rather than a convention. ECMAScript's test262 is the same
shape. The axis is worth naming because it changes what a tier can honestly
claim: only an official-suite tier can say "conformant" and mean the word
the way the language's own community uses it.

The distinction is about where a rule comes from, not about rigor. The
Python lane's `docs/completeness.md` §5 records five grammar verdicts read
off the source and MEASURED otherwise — four of them became the cheapest
rung on its ladder. Under extraction, `print(5 ^ 3)` outranks any reading.

### 4.2 The precedence rule where BOTH exist

Most spec languages also have a dominant implementation, and every tier in
this family that mirrors a spec also runs one: C targets ISO 9899 and runs
clang; SystemVerilog targets IEEE 1800 and runs pyslang plus a simulator;
Wasm, ECMAScript and Ada all have reference implementations.

> **The SPEC is the target. The IMPLEMENTATION is the oracle for
> behavior. The SUITE OWNER is the authority for the expected VERDICT. A
> divergence between any two is a FINDING — recorded with both citations,
> and it blocks none of them.**

The third clause is the Ada charter's amendment, and it is not a
restatement of the second. An implementation tells you *what happened*; a
suite's grader tells you *whether that counts as passing*, and those are
different questions the moment a test is graded on anything but byte
equality — which ACATS's six classes routinely are (a class-C test passes
on `PASSED` **or** `NOT-APPLICABLE`; a class-D test passes on the exact
answer **or** a capacity error). Reading a grader's rule off an
implementation's behavior would silently substitute one authority for
another.

Concretely: the model's rules cite the spec's clauses; the harness's
expected values come from the reference implementation; MATCH means the
model agreed with the implementation; a manifest row means the model
states the spec's rule. When they disagree — the implementation does X,
the spec says Y — **the model states Y, the harness records that the
oracle does X, and the row is published as a divergence finding.** Neither
side is silently adjusted, and neither is "fixed" to make a scoreboard
green.

The tree already contains the benign instance: the C tier's `-std=c23` pin
on `VM_VAL`'s conversion, where the spec MANDATES what an earlier edition
left implementation-defined and both development hosts happen to do the
mandated thing. The unbenign instance is §1.5's SV row — a lane citing one
edition and measuring against another's corpus, with no field that could
have said so.

**Where the spec is silent or ambiguous: REFUSE.** The model never invents
a rule the document does not state and the oracle merely happens to
exhibit. The single exception is the unspecified-order class, which gets
the canonical-plus-census treatment already recorded (§5.2, cause 4).

**AND THE SAME REFUSAL RUNS ONE ABSTRACTION UP, ON THE INSTRUMENT** (C,
`b57e983`, merged; **28 → 67/300**). The scoreboard needed struct layouts to
size what it was measuring, and the lane **declined to compute them**.

> **A LAYOUT COMPUTED FROM AN UNDECLARED RULE IS A FABRICATED LAYOUT — a
> FABRICATED COLUMN one abstraction up.**

Padding is **implementation-defined** and natural alignment is **an ABI this
project has not pinned**, so a layout derived from *what the host happens to do*
is exactly the rule §4.2 forbids the model to invent — **arriving in the
MEASUREMENT instead of the semantics, where the table above does not look for
it.**

**The fabrication family now spans three levels and refuses at one principle**: a
fabricated **column** (a scoreboard field the oracle never emitted), a fabricated
**name** (an identifier reconstructed rather than read), and a fabricated
**layout** (a size computed from an unpinned ABI). *Whatever the artifact, the
defect is identical — a value that reads as measured and was reasoned.*

**And an instrument's fabrications are harder to catch than a model's**, because
**a tier's refusals are COUNTED and a scoreboard's are not.** The model has a
taxonomy that makes it say *I decline*; **the instrument has a column that will
hold whatever is put in it.** *§4.3's table should be read as binding on every
artifact a tier publishes, not only on its semantics.*

### 4.3 The behavior-classes → refusal-taxonomy mapping slot

Every spec-mirror tier fills this table before it writes semantics. C's
row is filled; the rest are the founding lanes' first deliverable.

| tier | the spec's behavior classes | mapping |
| --- | --- | --- |
| **C** | undefined; unspecified; implementation-defined; locale-specific; constraint violation | UB → REFUSE(`undefined`), never retires, 11 classes armed, J.2-shaped. Unspecified order → canonical left-to-right + census, REFUSE where the census cannot show it unobservable (20 residual sites). Implementation-defined → PINNED by the profile schema; a host that disagrees is rejected by name. Constraint violation → the frontend rejects, phases 1–6 being outside Lean. |
| **SystemVerilog** | "shall be an error"; implementation-dependent; and a large SCHEDULING nondeterminism class (the event regions) | **PROPOSED.** The event regions are cause 4's natural home; the schedule is the explicit parameter of §3.4. |
| **WebAssembly** | deterministic by design, with a small NAMED nondeterminism set (NaN payloads, resource exhaustion, host behavior); traps are DEFINED outcomes, not UB | **PROPOSED.** Expect cause 2 to be nearly EMPTY, and gate that: a Wasm tier emitting `undefined` has a bug. This is the family's best case and worth founding early for exactly that reason — it calibrates the instrument against a language where coverage can be near-exact. |
| **ECMAScript** | implementation-defined / implementation-approximated (locale, `Date`, `Math`); host hooks | **PROPOSED.** The spec is ALGORITHMIC — numbered abstract-operation steps — so the mirror is per abstract operation and coverage is per step, not per prose clause. §5.5's manifest is written to allow this. |
| **Ada** | errors detected before run time; errors detected at run time; **bounded error**; erroneous execution; unspecified; implementation-defined | **FILLED** (`docs/ada-charter.md` §1.5). Run-time errors are an ORDINARY OUTCOME — `Run.exn` already has the shape. **Erroneous execution is cause 2, `undefined`, exactly.** Unspecified is cause 4 plus the ∀-parameter shape. Implementation-defined is the PROFILE, verbatim. **Bounded error fits none of the four**, and pre-run-time errors are not a refusal at all but a VERDICT the family lacked — both below. |
| **Go** | **no `undefined` class at all** — the string does not appear in the Go specification; data races; `select` choice; map iteration order; goroutine scheduling; implementation restrictions; implementation-defined | **FILLED** (`docs/go-charter.md` §2.6). **Cause 2 is EMPTY and GATED** — a Go tier emitting `undefined` has a bug, per the WebAssembly prescription; this is the family's second near-empty bucket, empty for a *different* reason (Wasm's by design, Go's because the memory model bounds its worst case instead of surrendering it). **Data races are MEMBERSHIP sites (§5.1), not refusals.** `select` is cause 4 with a *specified distribution* rather than a free order — stated, deliberately not sampled. Map order and goroutine scheduling are cause 4 verbatim, the latter at its largest: a schedule is not syntactically bounded, so a **race-freedom census** replaces C's may-alias census. Implementation *restrictions* are permissions to REJECT — frontend, where C's constraint violations land. Implementation-defined is the PROFILE. |

**THE PREDICTION IN THIS ROW WAS ANSWERED, AND IT WAS WRONG.** This
document predicted that if a fifth REFUSE cause were needed, Ada is where
it would show. **It does not show. The gap is one level up, in the
scoreboard** — §5.2's four causes are complete, and §5.1's verdicts were
not.

Walk a bounded-error site against the four causes and each fails for its
own reason. The construct is in the vocabulary (not cause 1). The standard
**describes the behavior fully** — the possible effects of a bounded error
are enumerated for each such error — so calling it `undefined` would be a
**false statement about the language**, and false in the expensive
direction: it refuses a program the standard fully describes, and that
refusal is then indistinguishable on the scoreboard from a tier gap, which
is the exact conflation §5.2 exists to prevent. Nothing is missing from the
slice (not cause 3). And it is **not cause 4**, because the quantifier is
the other way round: cause 4 is about ORDERS and its obligation is that
*every* admissible order gives the same observable — a **∀**; a bounded
error admits several OUTCOMES and its obligation is that the model's
outcome is *some* permitted one — an **∃**.

That ∀/∃ flip is the whole finding, and it lands in §5.1.

**Extraction tiers have no such table, and that is the point.** Their
behavior classes are whatever the census DISCOVERS, not what a document
enumerates — Python's are hash order, live dict mutation, stateful
generator drain, boundary observation forms, and they were found by
running programs. That is why `docs/completeness.md`'s class list is
measured and `docs/c23-goal.md`'s is derived.

---

## 5 THE VERDICT AND SCOREBOARD SYSTEM

One scoreboard shape for the whole family. The invariant is unchanged and
is the whole point: **DIVERGE must be zero, and REFUSE is never
agreement.**

### 5.0a DECLARED DIVERGENCES — where a KNOWN, DECIDED difference lives

**RULED 2026-08-24, on the pyc lane's request.** The lane found that **CPython's
dict-iterator error state is STICKY and the model's is not** — an **inherited,
named** divergence (from `enumDict`, `§pycomplete-14`) — and **deliberately gave
it no witness row, because a row would be a DIVERGE.** It lived only in prose,
and *never-hide-errors says prose is not a ledger.* Both halves of that are
right, which is why it needed a ruling rather than a preference.

**THE RESOLUTION STARTS BY SEPARATING TWO THINGS THE WORD "DIVERGE" WAS
CARRYING.** `DIVERGE` is a **verdict about a run**: the model answered, the
answer was wrong, and **nobody had decided that in advance**. What the pyc lane
holds is not that. It is a **decision the tier has already taken and can
state** — the model answers differently, on purpose, for a reason with a name
and an owner.

> **A DIVERGENCE THE TIER HAS DECIDED TO CARRY IS NOT A VERDICT. IT IS A DEBT —
> and debts are REGISTERED, AGED and GATED, never narrated.**

**So the invariant is untouched: `DIVERGE` stays zero, always.** A declared
divergence is not admitted to the scoreboard, because admitting it would make
the one number that means something mean nothing. **It goes to its own
register.**

**THE DECLARED-DIVERGENCE REGISTER — machine-readable, per tier, beside the
refusal whitelist** (same instrument family, same form, so it is read by a tool
and not by a reader's memory). Each row carries **six fields**:

| field | why it is required |
| --- | --- |
| **SITE** | what construct, at what spelling — so the row is findable from the code |
| **ORACLE behaviour** | what the language does (*sticky*) |
| **MODEL behaviour** | what the tier does (*not sticky*) |
| **INHERITED FROM** | the upstream decision and its id (`enumDict`, `§pycomplete-14`) — **blank means ORIGINATED here**, which is a different and heavier claim |
| **DECLARED** | the date, so the row can be AGED |
| **RETIREMENT CONDITION** | what would close it — and *"when someone models it"* is not a condition (§9's WAITING rule) |

**AND THE REGISTER IS GATED IN BOTH DIRECTIONS, which is the part that makes it
a ledger rather than a list.** For every row, an instrument asks:

* **is the model still divergent here?** — a divergence that has been **silently
  FIXED** leaves a **stale declaration**, and a stale declaration is a false
  claim about the tier that reads as diligence;
* **is the divergence still the one described?** — a divergence that has
  **silently WIDENED** is the same row describing a bigger fact, which is the
  worse failure and the one no reader will notice.

That is the paired-guard law (§5.2): **a boundary is guarded on both sides, or
the unguarded side is where it moves.**

**AND IT IS COUNTED IN §9.0 AS A THIRD QUANTITY — never folded into either
existing one.** A declared divergence is **not** coverage (the tier does not
model that behaviour) and **not** a gap (the tier does model the construct, and
answers). It is **covered-wrongly-on-purpose**, so the standing line reads
`declared-divergences: N` **beside** the coverage number rather than inside it.
**Folding it into the numerator would claim the behaviour; folding it into the
denominator would claim the tier had never reached it. Both are false.**

**Aging is the point of the DECLARED field**, and it hooks the audit cadence
(§9.7): **a row that has aged past several audits without its retirement
condition moving is a finding** — not because carrying it is wrong, but because
*a debt nobody has priced in months is a debt nobody is going to pay*, and the
honest options at that point are to retire it, to escalate it, or to say plainly
that the tier ships this difference permanently.

**INHERITED IS NOT ORIGINATED, and the field exists because the retirement
condition lives UPSTREAM.** The pyc row's owner is not the pyc lane; it is
whoever owns `enumDict`. **A tier that inherits a divergence inherits the
obligation to cite it, not to fix it** — and an inherited row that has lost its
upstream citation has become an originated one by neglect.

**THE RULING MET ITS FIRST IMPLEMENTATION WITHIN THE HOUR, and the contact
changed four things** (pyc lane's inch-3 design; **drafted off-repo and NOT
verifiable from this clone — landed on the design's account, conditional on that
inch, and owed a re-read at its landing**).

**(a) THE MODEL FIELD IS A MEASUREMENT, NOT A READING.** The first row's MODEL
field was **read from the code, not run**, and the lane **flagged its own field
as unverified until the probe exists.** That is the hole in the six-field spec
above, and it closes here:

> **A DEBT ROW'S `MODEL` FIELD IS A MEASUREMENT. THE ROW AND ITS INSTRUMENT LAND
> IN ONE COMMIT — they land together, or the row is prose with a schema.**

**A register whose fields are read rather than run is the thing it was built to
replace.** The whole argument for §5.0a over prose was that prose cannot be
gated; a row asserting *the model does X* on the strength of someone's reading
has **imported prose into the schema** and made it look like data.

**(b) A DEBT WHOSE PROBE IS BLOCKED BY ANOTHER DEBT — and the resolution is a
LAYERED instrument.** Observing the stickiness **in-tier** needs
`except RuntimeError:`, which is **a whitelisted refusal**: *the tier's own
refusal surface blocks the program-level probe of its own divergence.*

The probe therefore moves **to the model level** — a Lean `#guard` at the frame
stepper, where **THE BUILD IS THE GATE and it is two-sided**: a model that
*became* sticky fails it, and **any other move fails it too**. That leaves
exactly one hole the build cannot see — **the guard being deleted** — so **the
harness checks the guard's PRESENCE**, and **the row and the guard are deleted
together or not at all.**

> **LAYERED INSTRUMENTS: the BUILD gates the CONTENT; the HARNESS gates the
> EXISTENCE. Each layer's blind spot is the other's subject.**

**This is §5.4b's pointer question answered for a two-layer instrument**, and it
generalizes past this row: **a check strong enough to verify content is usually
blind to its own removal**, because a deleted check produces no output to be
wrong. **Pair it with a cheaper check that only asks whether it is still
there.**

**(c) A RETIREMENT CONDITION IS A CONSTRAINT PAIR — ONE POSITIVE, ONE
NEGATIVE.** The first row's: `except_builtin` **must leave the whitelist
FIRST** (the blocker **named**, not hand-waved), **and** `exc_lab::gen_closes`
**must STAY MATCH** — *closing on exception is correct for a user generator, so
a fix that flips `gen_closes` has fixed the wrong thing.*

> **A retirement condition names what must CHANGE and what must NOT. The
> negative half is protection against the FLATTERING REPAIR.**

**Third appearance of that hazard** (§5.4b's paired guard, §5.2's two-sided
resolution gate, and now a debt's own retirement), and the pattern is stable:
**wherever a condition can be satisfied by moving the wrong thing, name the
thing that must hold still.** A retirement condition with only a positive half
is a target, and **a target can always be hit from the wrong direction.**

**(d) INHERITED-FROM-SELF IS A REAL CASE — do not blank the field when the
debtor is the debtee.** Upstream here is **the same lane** (`enumDict` →
`iterDict`, both pyc), and **the field still does its work, because ORIGIN ≠
SITE.** The lane drew the right conclusion, and it is the one worth recording:

> **With no other lane to wait on, the retirement condition gets STRONGER, not
> weaker.**

**A blank `INHERITED FROM` claims the divergence ORIGINATED at this site**, which
is a heavier claim and a false one; and an inherited-from-self row that blanks
the field **loses the only pointer to the decision that created it.** The
temptation is real — *"it is us either way"* — and it is exactly backwards:
**self-inheritance removes the excuse, not the citation.**

**RULED — THE REGISTER'S CANONICAL SHAPE, before a third tier picks a fourth
one** (2026-08-24; ES filed `docs/es-declared-divergences.json`, pyc's approved
design is `harness/divergence_register.py`, SV is about to file two rows).

**The two shapes are not competing. They are two halves of one design that
arrived from opposite ends**, and the repository already has the pattern they
belong to — §5.4's census contract: **the INSTRUMENT is shared-shaped, the DATA
is per-tier JSON at a fixed path.**

> **DATA: per-tier, one schema — `docs/<lang>-declared-divergences.json`.**
> **CHECKER: ONE shared script — `harness/divergence_register.py` — which
> validates every tier's file, enforces the run-not-read rule, and gates both
> directions.**
> **PROBE: per-tier, and NAMED IN THE ROW, because it must speak the tier's own
> language.**

**So neither lane rewrites.** ES's file is the **data** half, correctly placed
and already gated both ways; pyc's script is the **checker** half, correctly
placed beside the whitelist infrastructure. **What was diverging was not the
design but the vocabulary for describing it.**

**Why the checker is shared and the probe is not**, since that is the line a
third tier will need: **the checker asks questions that are the same for every
tier** — does this row have all its fields, does it name a probe, did the probe
run, is it still divergent, has it widened — and MEAS-28 forbids implementing
that six times. **The probe asks a question only the tier can ask**: ES proves
two named theorems, pyc guards a Lean frame stepper. *A shared probe would have
to know every tier's semantics, which is the thing tiers exist to keep
separate.*

**AND THE SCHEMA GAINS TWO FIELDS THAT THE FIRST IMPLEMENTATIONS TAUGHT**, on
top of the six ruled above:

| field | why the implementation added it |
| --- | --- |
| **GUARDS** | the **two named** both-direction guards (ES: `es_div_1_still_divergent` / `es_div_1_has_not_widened`) — this is the run-not-read rule made **checkable**: the row names its probes, and the shared checker verifies they exist and ran |
| **KIND** | **`semantic`** or **`provenance`** (SV) — because **the retirement conditions differ**, and a register that cannot tell them apart will age them identically |

**`KIND` is not a taxonomy for its own sake.** A **semantic** divergence says
*the model is wrong*, and retires by **remodelling**. A **provenance**
divergence says *the CLAIM is unsupported* — SV's case: **model and simulator
have not been shown to disagree; what outran the evidence is the claim of
agreement** — and it retires by **re-running**. **Same register, same gating,
completely different work**, and a row that does not say which has told its
reader nothing about what would close it.

**AND THE FIRST ROW WITH A LIVE TWO-SIDED PROBE CAME WITH A REJECTED
ALTERNATIVE, which is the part worth keeping** (pyc `pyc-div-2`, `fcb1463`).
Ruled: **declare now**, with **fix-at-construction** as the named retirement.
**Rejected: refuse the shape.**

> **Scaling the model DOWN to dodge a debt is DEFINITIONS-WEAKENED-TO-PASS, one
> level up.**

> **A refusal adopted to AVOID A DEBT is a weakening wearing a boundary's
> clothes.**

**And it would have been invisible as a weakening**, which is why the rejection
needs recording rather than just applying: a tier that refuses the shape has a
**smaller surface and a clean register** — *no divergence row, no debt, no
aging* — and every number it publishes improves. **§0.1's first principle
forbids narrowing a definition to make a proof go through; this is narrowing the
MODELLED SURFACE to make a LEDGER go clean**, and the ledger was built to stop
exactly that.

**AND THE `has_not_widened` GUARD IS A CONTROL RUN, NOT A STATEMENT.** Move the
mutation **past the first `next`** and **oracle and model AGREE** — both exit 1,
both print `'1'`.

> **The row cannot silently grow into *"genexp cursors are wrong."***

**A widening guard whose content is a PASSING AGREEMENT CASE is the sharpest
form this register has seen**: it does not assert a bound, **it exhibits the
window's edge.** The earlier guards count sites or test artifact presence — good,
and they answer *"has it spread?"* with a number. This answers **"where does it
stop?"** with a **run that agrees**, and a run that agrees is the only evidence
that the boundary is real rather than merely undisturbed.

**AND THE DIVERGENCE IS LOCALIZED TO A CONSTRUCTION-SITE DIFFERENCE, WHICH NAMES
THE FIX.** **Two dict cursors in one tier, one right and one wrong**, and the
only difference is **where the frame is built**: `iterFrame` inside
`applyBuiltin` **snapshots at creation** — *which is why the earlier inch's
witnesses matched* — while `execGen` **pushes at first resume.**

> **The fix is to make the second do what the first already does.**

> **A divergence localized to a CONSTRUCTION-SITE DIFFERENCE is a divergence
> with a MECHANICAL retirement.**

**And the right-hand cursor is the retirement condition's own witness**: the
correct behaviour is **already in the tier**, so the row's closing condition is
not *"implement PEP 289"* but *"make these two sites agree"* — **a condition a
reader can check by diffing two functions.** *The best retirement conditions
point at something that already exists.*

**AND A SELF-REPORTED INCIDENT WITH A FAMILIAR SHAPE: A DEBUG PROBE FELL
THROUGH INTO A REAL ENQUEUE AGAINST THE LIVE QUEUE** (QoL, `3c278ce`).

> **A self-test that can reach the live queue is the `ci.sh` recursion incident
> wearing different clothes.**

**And the diagnosis is the part that generalizes**: *the e2e runs were isolated
all along; the DEBUG probes were the gap.* Corrections were a
**nothing-existing-moved** re-application and **ALL probes — not just e2e
runs — under `LS_QUEUE` / `LS_LOCK` overrides.**

> **ISOLATION DEMANDED OF TESTS MUST BE DEMANDED OF EVERY PROCESS THE TEST
> SESSION SPAWNS — and the INFORMAL ones are where the gap lives.**

**The formal tests get the isolation because they are the things called
"tests"**, and a debug probe is written in thirty seconds to answer one
question. **It is the same asymmetry as the self-selecting instrument** (§5.4):
the machinery is disciplined and the thing typed beside it is not — **and the
undisciplined thing runs in the same session, with the same environment, against
the same live infrastructure.**

**AND A SELF-REFERENTIAL EXISTENCE CHECK PASSES A FILE IT SHOULD REJECT** (pyc,
checker + census done). The declaration-shape self-test's **fake guards pointed
at the checker itself**, and **the substring check found them** — so the
rejection fixture passed.

> **A checker that searches for text can find its own fixtures' text, and an
> EXISTENCE check is the search most likely to.**

**Self-selection (§5.4) arriving in the one place it is hardest to see**: the
fixture is *designed* to contain the strings the checker hunts, so **the fixture
and the false positive are the same artifact.** And the catch is the encouraging
half — **the self-test's own expectation caught it**: the row expected a
rejection, got a pass, and **the disagreement between the two was the finding.**
*A rejection fixture is the only test whose success is a failure, which is why it
is worth writing even when the accepting path looks obvious.*

**AND THE CENSUS CAUGHT THE LANE'S OWN NEW CODE AS A FALSE DRIFT, FORCING
CALLER-BASED COUNTING.**

> **A worker living in a trunk file proves nothing; WHO CALLS IT decides.**

**Residence is not membership** — the same unit error as counting identifiers
where pattern positions were meant, arriving at **file location instead of
syntax.** A function's home directory is a fact about how someone organized the
tree; **its callers are a fact about the tier's surface**, and only the second is
what a drift census is asking about.

**And the correction is PINNED AS A POSITIVE EXPECTATION** — *so the correction
cannot be quietly lost the way the belief was.* **That is the sharpest sentence
in the batch.** A belief is lost by nobody re-stating it; **a positive expectation
is lost only by something failing** — so the repair is not *"we now know better"*
but **a row that breaks if the knowledge decays.** *The way a correction is
stored decides whether it survives the person who made it.*

**AND THE CHECKER'S OWN DISCIPLINE SET, from the third filing** (pyc inch 3).
**`--self-test` rejects TEN MUTATED COPIES OF A REAL FILE** — *a checker that
only ever passes is a claim* — and **`UNGATED` and `ORPHANED` are both checked,
in both directions**, because:

> **ORPHANED is the shape a DELETED ROW leaves behind — the one hole a build
> cannot see.**

**A row deleted with its guards left standing produces no error anywhere**: the
guards still elaborate, the register still validates, and the debt has simply
stopped being declared. **Only a check that looks from the GUARDS back to the
ROWS finds it**, which is the layered-instrument rule (§5.0a (b)) pointed at the
register's own contents rather than at a tier's.

**AND BETWEEN A RULED IDIOM AND AN IMPLEMENTED PRECEDENT, THE IMPLEMENTED ONE
WINS.** Rev 2's **named-Lean-declaration** guards became **probe functions**,
because **SV's precedent was IMPLEMENTED** and **no spec in the tree touches the
monadic stepper** — the lane's own verdict: *writing that idiom blind was the
wrong risk.*

> **A ruled idiom with no instance is a design; an implemented precedent is a
> measurement. Until the ruling has an instance, follow the instance.**

**This is a rule about MY OWN rulings and it is the right one.** A ruling is
written from the cases visible when it is made; **a precedent has met the tier's
actual materials.** The ruling is not overturned — it is **waiting for its first
implementation**, and a lane that builds the ruled shape blind is **testing the
ruling with its own inch.** *The register's job is to record which shapes have
been built, not to make lanes prove designs.*

**AND A RULING'S CONSTRAINTS CAN BE MADE LOAD-BEARING IN THE DIFF'S GEOMETRY,
RATHER THAN ASSERTED IN ITS PROSE** (C, `7eccf52`; **the span-col ruling's
landing, which is what earns it a row**). Three shapes, and each converts a
promise into a fact a reader can check without trusting anyone:

* **"Same order, same effects" is a fact about WHICH FUNCTION THE DIFF IS IN** —
  not a promise about the diff. *Scope is checkable; intent is not.*
* **The allocation sits OUTSIDE the match**, so eliding it **would require
  moving lines rather than deleting a branch.** *A constraint enforced by
  geometry costs an obvious edit to violate, and an obvious edit is one a
  reviewer sees.*
* **"Nothing can observe it" is A THEOREM ABOUT THIS `Mem`, not a licence.**
  *The scope of the claim travels with it, so the next `Mem` does not inherit
  permission the first one earned.*

> **A CONSTRAINT MET STRUCTURALLY SURVIVES THE READER WHO NEVER SAW THE RULING.**

**This is the ruled-idiom-versus-implemented-precedent rule collecting its own
dividend.** The ruling was **held as a design** until a landing tested it; the
landing **did not merely comply — it showed what compliance looks like in the
code's shape**, which is the form the next lane can copy without re-reading the
ruling at all. *A ruling that only lives in prose is obeyed by whoever remembers
it; one whose constraints are geometric is obeyed by anyone who edits nearby.*

**AND A SPEC'S UNITY IS NOT ITS IMPLEMENTATION'S** (C inch 6). §4.2's spec had
**three jobs belonging to different machines** — a fetcher, a one-process Lean
driver, and an independent re-scorer — and was **amended to BUILT with the
original spec KEPT VERBATIM, because every clause still binds.**

> **ONE SPEC, THREE PROGRAMS. A spec is a set of obligations; a program is a
> deployment of them, and the two need not have the same shape.**

**The disposition is the instructive half.** The alternative — rewriting the
spec into three — would have **lost the fact that the clauses belong together**,
and it is the kind of edit that looks like tidying: *the implementation has three
pieces, so the spec should.* **Keeping it verbatim and marking it BUILT records
both facts**: the obligations are one set, **and** they are discharged by three
processes with different lifetimes and different machines.

**This is the annotation norm applied to a specification** — *the spec was right
as written; only its realization is plural* — and it protects the next reader
from concluding that a clause is optional because no single program owns it.

**AND AN ACCEPTANCE CLAUSE CAN BE REFUTED BY THE IMPLEMENTATION, WHICH IS PART
OF THE ACCEPTANCE** (QoL item 6, merged `3c278ce`). The requested clause —
*"an unquoted `;` must refuse"* — **would have refused the DEFAULT FLOOR
ITSELF.** Refined to refuse only **empty-gate strays**, on the reasoning that
*a mistyped separator could remove a CHECK without removing a LINE*, with
**trailing `;` MEASURED as harmless** (command substitution strips it).

> **A spec written by the REQUESTER meets the implementation's floor, and the
> implementer's COUNTER-MEASUREMENT is part of the acceptance.**

**A requested clause is a hypothesis about the implementation**, and the
implementer is the only party positioned to test it. **The failure mode this
avoids is an acceptance test that passes by breaking the thing it was written to
protect** — and it would have passed: refusing the default floor is a
perfectly consistent reading of the clause as written.

**The measured half is what makes the refinement trustworthy rather than a
weakening** (the shape §5.4b keeps warning about): the trailing `;` was not
*assumed* harmless, it was **measured** harmless. *A narrowing justified by a
measurement is a correction; the same narrowing justified by inconvenience is
the loosened line this register keeps refusing.*

**AND AN ACCEPTANCE TEST WHOSE SUBJECT IS A GLOB INHERITS EVERY FUTURE TIER FOR
FREE.** The checker's acceptance test was *"validate ES's file when it
merges"* — **SV's file was on master first**, so the checker **validated a SECOND
tier on day one**, with **`git diff --quiet` proof it changed nothing.**

> **An acceptance test written against a PATTERN rather than a NAME is satisfied
> by whichever instance arrives first — and by every one after it.**

**The pattern was not a shortcut; it was the design of the ruling** (per-tier
data at a fixed path, one shared checker), and this is what that design buys on
its first day: **the cross-tier claim was demonstrated by an accident of merge
order**, at no cost, against a tier the checker's author had not seen.

**AND THE FULL ROUND TRIP HAS NOW RUN, END TO END** (pyc inch 4, merged
`7129f2b`). The witness measured **DIVERGE** at inch 3 → moved **OUT of the
census into the register** as `pyc-div-2` → the fix compiled and **the row's own
guard began failing** → the row **retired on BEHAVIOUR** → **the witness returns
to the census AS A MATCH.**

> **A register that only ever grows is a LIST; this one SHRANK on a failing
> guard.**

> **A RETIRED DIVERGENCE LEAVES A MATCH WHERE IT STOOD.**

**That receipt structure is the design's proof of life, and it is worth naming
as a shape**: *witness out, witness back.* The row is not merely deleted — **the
thing it displaced returns to the scoreboard**, so the census ends up **one MATCH
richer than before the divergence was found.** A register whose closures left
holes would be indistinguishable from a register whose rows were quietly
dropped; **this one hands the evidence back.**

**And the guard failing THE MOMENT THE FIX COMPILED is the paired-guard law
paying out in the direction nobody designs for.** Both-ways gating was ruled to
catch **a silently fixed** or **silently widened** divergence — *defects*. Here
the same mechanism **detected the intended repair**, on the same day it was
written, **with no separate step to notice it.** *A guard built to catch a
regression announced a success, because the two are the same measurement read
from opposite ends.*

**AND A CENSUS WHOSE FIRST RUN CONVICTS THE LANE'S NEWEST LINE IS POINTED AT THE
RIGHT THING.** The construction-site census's **first output flagged code written
minutes earlier.**

> **A new instrument's first hit landing on the freshest code is evidence about
> the INSTRUMENT, not an accident of timing.**

**The complement of *a new instrument's first finding is the one to re-run
against the old input***: that guards against a tool inventing a dramatic
finding; **this observes that a tool which immediately sees the thing nobody has
had time to forget is aimed correctly.** *The newest line is the one whose truth
the lane is most certain of — so a census that convicts it is being checked
against the best-known facts available.*

**§5.0a HAS ITS FIRST RETIREMENT, AND THE CONDITION CLOSED IT** (SV, batched
tenure at head; `sv-div-2` retired). After the rewording, `still_divergent`
reported **`sites: 0` and FAILED** — *which is the guard working.*

> **THE COUNT CLOSED THE ROW; NO ASSERTION COULD HAVE.**

**That is the retirement-condition ruling collecting its dividend.** The
condition was built with *no place for an opinion to enter* — a count reaching
zero — and when the work was done **the row did not need anyone's judgement to
close: the guard failed, and the failure WAS the closure.** *A guard that fails
when the debt is paid is the only kind that can retire a row without a decision.*

**AND THE SCHEMA GAINS A SEVENTH FIELD — RULED: `retired_rows`.**

> **A ledger that forgets its closed rows cannot show that any row EVER
> CLOSES.**

**The shared checker accepts it, and retired rows stay in the file.** A register
that only ever grows reads as **a list of things nobody fixes** — and the aging
mechanism (§9.7) becomes unreadable, because *a row's age means nothing without
the distribution of ages at closure.* **Retirement is the register's only
evidence that it is a ledger rather than an accumulator.**

**AND THE DISCIPLINE THAT KEEPS A RETIREMENT HONEST WAS PRE-STATED BY THE NEXT
LANE TO REACH ONE** (pyc): `pyc-div-2` **stays filed until the guard is MEASURED
to flip.**

> **Retiring it on the strength of having WRITTEN THE CODE would be exactly the
> assertion its retirement condition forbids.**

**The condition and the code are two different facts**, and the gap between them
is where every optimistic closure lives. *A lane that has written the fix knows
more than anyone about whether it works, and is therefore the party least able
to serve as its own guard.*

**AND THE FIRST TWO FILINGS TAUGHT THE SCHEMA FIVE MORE THINGS** (pyc handoff
rev 2, verify at inch 3; SV's register, `ee8d8bd`, on master).

**(e) A PROBE MUST BE A NAMED DECLARATION — `#guard` IS ANONYMOUS.** The pyc
lane corrected **its own approved design** against ES's implementation:
*"`#guard` has no name for the checker to verify"*, and the lane's own verdict
was *"ES got this right and I did not."*

> **ANONYMOUS EVIDENCE CANNOT BE CITED. A certification schema forces naming.**

**Which is why the `GUARDS` field is a field and not a checkbox**: a row saying
*"guarded"* is a reading; a row **naming two declarations** is something the
shared checker can look up, and **a probe that cannot be named cannot be found
by anything except the person who wrote it.**

**(f) THE CHECKER FAILS ON AN EMPTY REGISTER SET.**

> **A test that passes because it found NOTHING is exactly the unexercised
> gate.**

**§5.3's vacuity ruling applied to the register's own acceptance test** — the
one place it would have been easiest to skip, since an empty register is the
normal state of a tier with no declared divergences. **The zero-row law
(§5.4's *an empty census is an instrument fault, never a finding*) reaches the
instrument that polices the debts.** Landed with commit claims **scoped to what
RAN**.

**(g) A RETIREMENT CONDITION CAN BE BUILT TO EXCLUDE JUDGMENT** (SV). One row's
guard tests **ARTIFACT PRESENCE** — the `xrun` fixture — so **it cannot be
closed by deciding the tables look right.** Another **COUNTS surviving sites**,
so **the count reaching zero closes it and assertion cannot.**

> **The best retirement conditions are not stricter opinions; they are
> conditions with NO PLACE FOR AN OPINION TO ENTER.**

**Both shapes generalize**: *presence of an artifact* and *a count reaching
zero*. Each converts *"is this fixed?"* — a question a motivated party answers —
into a fact a script reads. **The flattering-repair hazard (§5.0a's constraint
pair) is a defence against the wrong fix; this is a defence against no fix at
all.**

**(h) "WIDENED" MEANS SOMETHING DIFFERENT FOR A PROVENANCE ROW, discovered at
first use** (SV). For a **semantic** row, widening is the model diverging over
more inputs. For a **provenance** row, **widening is the UNSUPPORTED CLAIM
SPREADING TO MORE SITES** — guarded by **claim-site counts pinned at
`DECLARED`.**

> **A semantic-shaped guard would have had nothing to measure here.**

**So `KIND` does not merely change the retirement condition — it changes the
guard VOCABULARY**, and that is a stronger reason for the field than the one it
was ruled on. *A register with one guard vocabulary would have silently
mis-guarded every provenance row it accepted.*

**(i) AND THE FAILURE DIRECTION WAS RUN, NOT TRUSTED** — an **11th** claim site
makes `has_not_widened` report **11** against a pin of **≤ 10** and **exit 1.**
Plus the honesty that closes the loop: **the one field that could not be a
measurement** — the model's agreement with Xcelium, *the very thing unverified* —
is **SCOPED IN THE ROW rather than implied.**

> **A row that says what it CANNOT measure is the register's own honesty applied
> to itself.**

**RULED — §5.0a DOES NOT ADMIT A PERMANENT ROW, and the reason is that a
permanent row is NOT A DIVERGENCE** (analog's F1: *"model validity: MISSING"*,
architecturally unclosable, admitted 12× in the artifact; if filed, its
retirement condition is honestly **"never"**).

**Two things forbid it, and the second is the structural one.**

**(1) IT IS THE WRONG CATEGORY.** A declared divergence says *the model answers
differently from the oracle, and we decided to carry that.* F1 says **there is
no oracle** — the model's validity **cannot be established by any experiment the
domain admits.** That is the **EPISTEMIC BOUNDARY** (§5.2, as amended): *the tier
cannot construct an experiment that would tell.* Filing it as a debt claims a
disagreement nobody has measured **and nobody can.**

**(2) A ROW THAT CAN NEVER RETIRE DESTROYS THE AGING SIGNAL.** The register's
enforcement **is** the aging: §9.7 reads a row past several audits with an
unmoved retirement condition as **a finding**. A row whose condition is *never*
**trips that check forever**, and a signal that always fires is one lanes learn
to skip (MEAS-135). **One permanent row costs the register its only enforcement
mechanism.**

> **THE DISCRIMINATOR, so nobody has to re-ask: CAN THE CONDITION THAT WOULD
> CLOSE THIS BE NAMED — even if nobody intends to do it?**
>
> * **YES** → a register row, with that condition, however distant.
> * **NO — no experiment exists** → an **epistemic boundary**, not a debt.

**AND THE DISCRIMINATOR NEEDS A COMPANION FOR THE OTHER SIDE OF THE SAME LINE,
GENERALIZED FROM THREE INSTANCES** (pyc's `except_builtin` inch, `c8d46c8`,
ticketed). Each of the three was **TRUE WHEN WRITTEN**, and the common factor is
the finding:

> **AN ARGUMENT RESTING ON WHAT THE TIER CANNOT DO HAS AN EXPIRY DATE NOTHING IN
> THE TREE TRACKS.**

**A cannot-claim is a measurement of the tier, and the tier is the thing most
likely to change.** The epistemic boundary above is the *permanent* case — no
experiment exists, ever — while these are its **temporary look-alikes**: *we
cannot construct that yet* wearing the same words as *no one can*. **The
distinction is invisible in the sentence and decisive for the decision built on
it.**

**So a cannot-claim now carries two obligations, and the second is the one this
register was missing.** A **witness attempt at filing time** (§9.7's rule: the
claim is that you tried and it failed, not that it would) — **and a TRACKING
MECHANISM for the inch that lifts it**, because the first obligation says nothing
about the day the limitation goes away.

> **A LIMITATION-DEPENDENT ARGUMENT CITES ITS LIMITATION BY NAME, so the inch
> that removes the limitation can GREP FOR ITS DEPENDENTS.**

**This is the retirement-condition mechanism moved from the row to the
argument.** *A declared divergence has a named condition and an audit that ages
it; a cannot-claim buried in prose has neither* — and the cheap fix is not a
second register but **a citable name in the sentence**, which turns the lifting
inch into the auditor. *The lane that removes a limitation is the only lane
guaranteed to know it is gone.*

**AND THE FOURTH INSTANCE ARRIVED IMMEDIATELY, IN A NEW ARTIFACT CLASS** (pyc,
same inch): **the first expiring comment found IN A WITNESS.** The law's coverage
now spans **docstrings, architecture notes, a proof's prose, and witnesses** —

> **Four artifact classes is enough to stop qualifying this by artifact: ANY
> PROSE THAT ASSERTS A LIMIT EXPIRES, wherever it is written.**

**And a witness is the worst place for one**, because a witness is read as
*evidence* rather than as *commentary*: a stale sentence beside a passing case
inherits the case's authority. *The citable-name remedy applies unchanged — but
the population it has to reach is now every string in the tree, which is an
argument for the grep-by-name mechanism over any register of locations.*

**AND THE FIFTH ARRIVED IN THE WORST HOST YET — INSIDE AN INSTRUMENT** (pyc's
div-1 witness, `4a40ea8`, ticketed). The probe's own docstring said **"not
reachable by an in-tier program."**

> **An instrument carrying an expiring claim is WORSE than a comment carrying
> one, because the instrument is what a reader trusts WHEN THE COMMENTS
> DISAGREE.**

**The hierarchy of trust is exactly inverted from the hierarchy of maintenance.**
*A comment is suspected by default; an instrument is the thing consulted to settle
suspicions* — and its prose is maintained less often than a comment's, because
nobody re-reads the docstring of a tool that works. **An instrument's prose should
be held to the standard of its output, not to the standard of a comment.**

**AND A CONTROL DRAFT WAS CAUGHT PRE-TICKET BECAUSE THE LANE ASKED THE RIGHT
QUESTION** (same inch). The draft **raised `ValueError` — itself a whitelisted
refusal** — so the control would have been satisfied by the very behaviour it was
written to detect. *"Caught by asking what the program NEEDS rather than what it
looks like."*

> **A CONTROL IS VALIDATED AGAINST WHAT THE PROGRAM REQUIRES, NEVER AGAINST WHAT
> THE CONTROL RESEMBLES.**

**Resemblance is what a draft optimises for, because a draft is written by
reading the thing it will replace** — and this is the grep-versus-declaration
defect one more level up: the check looked right and answered a question adjacent
to the one asked.

**AND A DEBT ROW'S BLAST RADIUS IS AN OBJECT-IDENTITY CLAIM, STATED IN THE ROW**
(same landing):

> **"The row describes one poisoned OBJECT — not a poisoned dict, not a poisoned
> interpreter."**

**A divergence's scope is a fact the row must carry, because every reader will
otherwise supply their own** — and the three readings differ by orders of
magnitude in what they forbid. *§5.0a's schema already demands a SITE; this says
the site is a scope claim and must be written at the granularity that is
actually true.*

**AND A POTENTIAL GUARD FAILURE WAS PRE-DECLARED AS INFORMATIVE IN BOTH
DIRECTIONS** (same landing), with **the detail line printing BOTH SIDES** so the
tenure can distinguish **retirement** from **wrong witness** without a re-run.

> **DECIDE WHAT A RED WILL MEAN BEFORE THE RUN, AND MAKE THE OUTPUT CARRY THE
> DISCRIMINATOR.**

**A red decided after the fact is decided by whoever is tired**, and the
expensive part is never the failure but **the second run needed to learn which
failure it was.** *A guard whose output distinguishes its own two explanations is
worth more than a guard that is merely correct* — and, like the pre-stated zero,
it converts a possible embarrassment into a planned measurement.

**AND THE DISCLOSURE IS NOT LOST, which was the only real risk in ruling this
way.** F1 already lives **where §5.0a's own reasoning says a standing disclosure
belongs**: in the artifact's output, admitted **12 times**, *where the claim is
served rather than where the apology is filed.* It is additionally **named in
§9.0's standing line as a SCOPE qualifier on the coverage number** — not as a
debt against it. **A permanent admission is part of what the number MEANS**; a
debt is something the number is waiting on.

**AND A THIRD CASE THE TAXONOMY MUST NAME, so nobody files it either** (analog's
underdetermined node): the witness says **5 V**, ngspice says **3.996 V**, and
**BOTH satisfy the Lean KCL.**

> **AN ORACLE DISAGREEMENT IS NOT A DIVERGENCE WHEN THE SPEC ADMITS BOTH
> ANSWERS.**

**The node is underdetermined in that vector**, which is *precisely why
realizability is an ∃ and `DeterminateUnder` is a separate obligation this deck
does not claim.* **Filing it would be a category error in the other direction**
from F1: F1 has no oracle, this has **two legitimate answers** — and a register
row would assert the model is wrong where **the spec declines to choose.**
*Before filing a disagreement, ask whether the SPEC picks a winner; if it does
not, the disagreement is a fact about the SPEC's latitude.*

**WHY NOT THE ALTERNATIVES.** A *whitelist* would put the row inside the
scoreboard's own vocabulary and invite exactly the reading the invariant
forbids — *some DIVERGEs are fine* — and a whitelist is a permission, not a
debt: it does not age. **Prose in the tier doc is what this ruling replaces**;
prose cannot be counted, cannot be aged, and cannot be gated, and it is
indistinguishable from an oversight the moment its author leaves.

### 5.1 The verdicts

| verdict | meaning |
| --- | --- |
| **MATCH** | the model ran to completion and its observable **satisfies the site's expectation** — see the membership rule below |
| **REFUSE** | the model declined, loudly and fuel-independently. FOUR disjoint causes (§5.2), reported separately |
| **DIVERGE** | the model produced an observable and it does NOT satisfy the expectation. The invariant violation. Zero, always |
| **TIMEOUT** | fuel exhausted. The only exhaustion outcome; never conflated with REFUSE |

**THE DIVERGE TEST IS NOT EQUALITY AT EVERY SITE**, and this document said
it was. The Ada charter's bounded-error analysis (§4.3) forces the
correction:

> **At a site where the language enumerates several permitted outcomes,
> MATCH is MEMBERSHIP in that set, not equality with one oracle's
> observable. Two conforming implementations may disagree there and both
> be right.**

Scoring byte equality at such a site **manufactures DIVERGEs** — and
DIVERGE is the family's zero-tolerance invariant, so a manufactured one is
not a cosmetic error: it either halts a lane chasing a non-bug or, worse,
trains the lane to tolerate DIVERGE rows. Refusing instead is no better; it
is a coverage loss the language does not require, at a site the standard
describes completely.

**Three consequences, and the first two are what make it cheap.** The
permitted set is a **per-site datum** the tier carries, not a new verdict
name — the vocabulary above is unchanged. Equality is the **degenerate
case**, a singleton set, so every existing site is already correct under
the membership rule and nothing needs revisiting. And MATCH stops meaning
"agrees with the oracle" and starts meaning "is permitted", which is the
honest reading and the one an official-suite tier (§4.1) needs anyway,
since ACATS class C passes on `PASSED` *or* `NOT-APPLICABLE` and class D on
the exact answer *or* a capacity error.

**This class is not Ada-specific, which is why it belongs here.** It is
exactly what **Go's racy programs** need (§3.6): Go bounds what a racy
program may observe instead of surrendering to UB the way C does, so a racy
Go program is a membership site and not a refusal. C's
`unspecified`-but-enumerated sites are the same shape again. Ada found it
because Ada's standard *enumerates* the permitted effects per error where
other languages leave the enumeration implicit — the finding was always
there, and Ada's rigor apparatus made it visible.

**Two ways to carry the per-site datum, and neither is chosen here** —
it is Thomas's, and the Ada charter lists it as an open decision: the site
carries its permitted set explicitly, or the scoreboard consults a
predicate supplied by the tier. The architecture only fixes that the test
IS membership.

### 5.2 REFUSE has FOUR causes, and the fourth is a finding

They retire on completely different schedules, so pooling them makes the
scoreboard unreadable.

**AND A LIVE DEFECT HAS NOW SHOWN WHAT "UNREADABLE" COSTS — the classes are a
WORK ASSIGNMENT, not a label** (Go, `69ea58a`, on master). `int(x)` parses as a
**`CallExpr` on an `Ident`**, indistinguishable at the AST from calling an
undefined function, so the walker refused **every type conversion** as
`environment`. Measured: **51 255 of the stdlib's plain-identifier calls are
conversions to a predeclared type — 26.3%** — and every one was in the wrong
bucket. Verified by running the walker **before and after**, not by reading the
patch.

> **A MIS-BUCKETED REFUSAL IS NOT MISLABELLED — IT IS MIS-SCHEDULED. The class
> determines WHO OWES THE WORK.**

**AND A REFUSAL CAN BE RETIRED TOO EARLY, WHICH IS THE ONE DIRECTION THIS SECTION
HAD NOT PRICED** (ES's realm-gating).

> **"Correct machinery that can never find an iterator would convert today's
> HONEST REFUSAL into a WRONG ANSWER — the one trade this lane never makes."**

> **A CAPABILITY LANDED BEFORE ITS ENABLING CONTEXT IS A REGRESSION WEARING A
> FEATURE'S NAME.**

**The scoreboard rewards the trade, which is why it needs a law against it.**
Machinery that runs moves a row from `refused` to something; **a refusal that
becomes a wrong answer moves the number in the pleasant direction while making
the tier worse**, and no verdict in §5.1 distinguishes the two after the fact.

**The test is a question about the CONTEXT, not the code**: *can this machinery
reach the thing it is written to handle, in this tier, today?* **If not, the
correct landing is the machinery WITH the refusal still in place** — the code is
banked, the number does not move, and the row retires when the enabling context
arrives. *Gating a finished capability is not caution; it is the only way to keep
a refusal honest while building the thing that will lift it.*

`environment` retires by **widening the modelled slice**; `unsupported` retires
by **climbing a rung**. Different work, different owners, different schedules —
so a mis-bucketed row does not merely read wrong, it **queues the wrong lane**.
The downstream damage here was exactly that: the tier's ranked worklist was a
worklist of *environment* refusals, and **a quarter of what would have been on
it was never an environment problem at all.**

**THE FIX SHAPE IS THE REUSABLE PART: A PAIRED GUARD — one item per side of the
boundary.** One conversion and one genuinely-undefined function, so a
regression **in either direction** shows. A single-sided guard pins only the
half that was wrong when it was written, and re-classification defects move in
both directions by construction: the same edit that stops over-claiming
`environment` can start under-claiming it.

> **When a fix moves a boundary, guard BOTH SIDES of it. A one-sided guard
> ratifies today's error in the other direction.**

1. **`unsupported` — out-of-tier construct.** Retires by climbing a rung.

   **DEFERRAL HYGIENE, and it is a rule for every deferred construct.** A
   deferral is cause 1 and must stay cause 1; the failure mode is that it
   **quietly becomes a UB claim** — cause 2, which never retires — because
   nothing stopped the drift. Go's `fallthrough` is the worked example and
   the pattern to copy:

   * **the census figure travels IN the refusal message** — `fallthrough`
     refuses carrying its **4.0%** corpus share, so the cost of the
     deferral is visible **at the point of refusal** rather than in a
     document a reader would have to go find;
   * **it is guarded TWICE — on the CLASS and on `isUndefined`** — *so the
     deferral cannot quietly become a UB claim.*

   The double guard is the load-bearing half. One guard proves the
   construct is refused; the second proves **which kind of refusal it
   is**, and that is the property that would otherwise erode silently as a
   tier grows. A deferral that cannot be distinguished from undefined
   behaviour has given up the one distinction §5.2 exists to keep.
   Universal; Python's `.unsupported` exactly.
2. **`undefined` — the language says this run has no meaning.** C's UB,
   Ada's erroneous execution. **Never retires: it is the product.** Its
   presence is a per-language FACT — Python has no UB, and a
   deterministic-by-design language's bucket should be near-empty and
   gated as such.
3. **`environment` — the run needs something outside the modeled slice.**
   Unmodeled libc, an unprovided host import, an unmodeled builtin.
   Retires by widening the slice. (C's taxonomy calls this `libc`, which
   is too C-specific a name for a family contract.)
4. **`order-dependence` — the language admits several orders and the
   model cannot show the observable invariant under all of them.**

**THE LAST CODE-LEVEL OBSTACLE TO THE VOCABULARY IS C's `libc`.** C's cause
type is `valueUB` / `memUB` / `libc`, and the first two are refinements of
cause 2 (`undefined`) that fit the payload rule (§5.2's ruling above)
cleanly. **`libc` is the outlier**: it is §5.2's cause 3, `environment`,
under a name that says *which* environment rather than *that* it is one.
Recorded as **C's next-touch item** — the rename is mechanical, the payload
keeps the `libc` distinction, and it is the last place a cause class in the
tree does not carry a family name.

**Cause 4 is new at the family level, and the C tier is the evidence that
it is needed.** `docs/c-semantics-design.md` §3.1 fixes three causes;
§4.4 then rules "REFUSE where a static census cannot show the order
unobservable" for the 20 residual may-alias sites. That refusal fits none
of the three: the construct is in the vocabulary (not cause 1), the
program is *unspecified*-dependent rather than undefined (not cause 2 —
unsequenced modification is UB, but which argument evaluates first is
not), and nothing is missing from the slice (not cause 3). Python's twelve
hash-order refusals and its permanently-loud same-size key-set regime are
the same cause, arrived at from the other authority. SystemVerilog's event
regions will be its largest bucket.

#### RULING — WHERE `RefusalCause` LIVES: the four CLASSES in `Core`, the PAYLOAD per tier

Ada's M2 measurement forced the question the ES charter left open, and
three tiers now have a stake: ES fixed a three-constructor cause type; Ada
needs `undefined` as a constructor (ARM 1.1.5 erroneous execution, **23
paragraphs** in its core clauses); C already refuses with **J.2 indices**,
a richer shape than either.

> **RULING: `Core` carries the FOUR §5.2 CLASSES as a four-constructor
> type, PARAMETERIZED by a tier payload — `RefusalCause π`. The classes are
> family law; the payload is the tier's.**

C instantiates `π` with a J.2 index, Ada with an ARM paragraph, ES with a
host-hook name.

**AND TWO TIERS HAVE NOW CHOSEN THE SAME SHAPE INDEPENDENTLY, WITH OPPOSITE
NARROWING DECISIONS — which is stronger evidence than agreement would have
been.** Go and Ada each instantiated `π` as **a citation into their own
standard** (`SpecRef` / `ArmRef`) without coordinating. **And they diverge on
the class set, each justified by their own spec**: Go **NARROWS** the cause type
and **excludes `undefined`**; Ada **does not**, because its `undefined` bucket is
a real product — the ARM's **bounded errors**.

> **Convergence on the PARAMETER plus divergence on the INSTANTIATION is
> exactly what a correct parameterization looks like.**

Had both tiers narrowed the same way, the honest reading would be that the
family had guessed a *default* rather than found a *parameter*. **Two tiers
filling the same slot with different content, each on their own spec's
authority, is the ruling working as designed** — and it is §9.3's convergence
standard applied to a design decision rather than to a name. **The payload objection dissolves exactly the way `ρ` did**
(§3.4): what differs irreducibly per tier is not a *class*, it is a
*parameter*, and a parameter is the thing this family already knows how to
share.

**Why not per-tier cause types under a family law** — the alternative, and
it fails on this document's own precedent. "Each tier defines its own type,
constrained to partition into the four classes" makes the partition a
**per-tier proof obligation**, and the `Halt` ruling settled that shape:
*a family invariant that must be re-established per tier is not a family
invariant, it is N lemmas.* It also defeats the scoreboard — §9.4's
argument for a shared verdict vocabulary applies verbatim to causes, since
"how many REFUSE(`undefined`) across the family" is exactly the question a
cross-tier scoreboard exists to answer, and per-tier types make it a
translation table.

**AN EXPECTED-EMPTY CLASS IS PRESENT AND GATED, NEVER ABSENT.** This is the
part of the ruling that changes ES. Omitting `undefined` because ES has no
undefined behavior makes the emptiness **a fact about the type, invisible
to the scoreboard** — it cannot distinguish *"this language has no UB"*
from *"this tier did not model that column."* §4.3 already prescribed the
opposite for WebAssembly: *expect the bucket to be empty, and gate it — a
tier emitting `undefined` has a bug.* A gate needs a constructor to be
about. **ES converges by touch** (§9.2), gaining the two constructors it
omits and gating both.

**AND THE RULING NOW HAS ITS COUNTING RULE, measured on the first corpus run
that gated it (`6b91a8d`): TWO ZEROES THAT ARE NOT THE SAME ZERO.**

> **A zero for a class the tier CAN emit is a fact about the CORPUS. A zero for
> a class the tier's API CANNOT BUILD is a fact about the TIER. Same number,
> different claims.**

Measured: `environment=0` and `order-dependence=0` say **the whitelist corpus
does not reach `refuseEnv` / `refuseOrder`** — a **coverage** statement, and an
honest one. `undefined=0` says something else entirely: the tier's API **cannot
construct it**, so that zero is a **property of the model**, and it is the
`undefined` column's whole reason for existing (§4.3's *expect the bucket empty,
and gate it*).

**Conflating them is how a coverage hole reads as a soundness result.** *"No
undefined behaviour observed"* is a sentence both zeroes support and only one
earns; a scoreboard that prints a bare `0` in both cells has published the
weaker claim under the stronger one's name. **The distinction is
structural — can the API build it? — so it is decidable once per class rather
than argued per report**, and the census now gates the strong half from the
OUTSIDE, on the real corpus: *every interpreter refusal carries one of the four
class names, and none carries `undefined`.* 116 rows, 45 gap classes, 7
boundary-freeze refusals with no class **by design**, 0 drifts.

**AND AN UNREACHABLE REFUSAL GUARDS NOTHING — the first implemented §5.0a row's
own finding** (ES, `es-div-1` at `b312465`, triad queued). The refusal for sloppy
`this` **exists in `ordinaryCallBindThis` and is CORRECT** — and it is
**UNREACHABLE**, because `instantiateFunction` **hardcodes `[[ThisMode]] =
strict`. So sloppy code silently gets `undefined` where the language says
`globalThis`.**

> **REACHABILITY IS PART OF A GUARD'S DEFINITION. An unreachable refusal guards
> nothing.**

**A week of writing refusals as boundaries, re-read.** This is the sharpest
correction available to §5.2's whole apparatus: **the four causes describe what
a refusal SAYS, and none of them asks whether the refusal can be REACHED.** A
correct refusal on a dead path is **indistinguishable from a modelled
behaviour** — the tier looks bounded, the scoreboard shows no refusal, and the
silence reads as coverage.

**Pairs with §5.0a's layering law and inverts it.** There, *a check strong
enough to verify content is blind to its own removal*; here, **a check is blind
to its own unreachability** — and the second is worse, because deletion at least
leaves a diff. **Nothing changes when a guard becomes unreachable; the code that
strands it is somewhere else entirely.**

**AND THE LAW NEEDS A DISTINCTION IT DID NOT SHIP WITH, found by the pyc lane
auditing its OWN inch against it** (handoff rev 2; verify at inch-3 landing).
**Not every unreachable arm is a defect** — without the split, **every
exhaustiveness arm in the tree becomes a false positive:**

| kind | what it is | verdict |
| --- | --- | --- |
| **unreachable BY CONSTRUCTION, and DOCUMENTED** | the trunk's `.iterDict` arm — **the exhaustiveness obligation**, not a boundary claim | **fine** |
| **unreachable and BELIEVED REACHABLE** | ES's sloppy-`this` refusal — *the tier looked bounded while it answered* | **the defect** |

> **The defect is not unreachability. It is a REFUSAL BELIEVED TO BE A
> BOUNDARY that is not one.**

**RULED — REFUSAL-FORM FOR AN EXHAUSTIVENESS ARM, and the two candidate answers
both skipped a prior question** (pyc, raised rather than assumed; the trunk's
`forDict` / `enumDict` / `iterDict` arms).

**The prior question is: WHY IS THE ARM REACHABLE IN THE TYPE AT ALL?** The
comments answer it — *"the trunk never **builds** a `forDict` frame"* — which is
a claim about **construction sites**, not about the type. So the ruling is
three-way, not two-way:

> **(1) IF THE IMPOSSIBILITY IS PROVABLE AT THE TYPE LEVEL, DISCHARGE IT
> THERE** — `nomatch`, or narrow the frame type. **No arm, no message, no
> documentation, no failure mode.** This is the only outcome where nothing is
> load-bearing, and it is STMT-129's rule (*where a rule is at risk of
> re-collapsing, the durable form is a type, not a reminder*).

> **(2) OTHERWISE — the type admits the frame and only the trunk's construction
> discipline excludes it — REFUSAL-FORM WINS.** The arm is a **live defensive
> path** whose unreachability is a claim about **callers**, and callers change.

**(b)'s safety argument is decisive at (2) and it is the register's own
preference stated in a new place**: if the arm ever **becomes** reachable,
**refusal-form fails soft, loud and classed; absurd-form crashes.** This
document has ruled for the loud-and-classed failure every time it has been
offered the trade — *the flattering direction is the one that ships*, and a
crash in a model is the least informative failure available.

> **(3) BUT (a) IS RIGHT ABOUT ONE THING, AND IT IS TAKEN: THE DOCUMENTATION
> MUST STOP BEING WHAT CARRIES THE CLAIM.**

**Not by changing the form — by GATING the claim.** *"The trunk never constructs
this frame"* is **a measurable statement about the trunk**: a census over
construction sites, which either finds one or does not. So the arm keeps
refusal-form **and** the by-construction claim gets the check that §5.4 demands
of every prose claim.

**This refines what I ruled yesterday.** I wrote that *documented* is doing real
work in the by-construction row, because **an undocumented arm is
indistinguishable from the defect by reading** — true, and **reading was the
best instrument then available.** A census is better and is available. **Once the
claim is gated, the arm is no longer *believed* unreachable; it is *measured*
unreachable** — which moves it out of MEAS-256's defect category **by
measurement rather than by assertion**, and that is the whole difference the
category was drawn to capture.

**Summary for the three arms**: they are pyc's to keep in refusal-form, and
pyc's to gate. **No conformance edit is owed on form; a census is owed on the
claim.**

**AND THE CONVERSE CASE ARRIVED THE NEXT DAY, so the two must be read together:
AN UNREACHABLE *CHECK* IS KEPT** (pyc inch 3, `3ea2f2a`, ticketed). The
register checker's **empty-register test is now unreachable** — two tiers have
filed rows — and the lane **kept it**:

> **That is a fact about TODAY, not about the design. Deleting it buys a silent
> green.**

**This is not in tension with the law above; it is the same discriminator
answering differently, and the difference is worth being explicit about**,
because a lane holding both rules at once will otherwise pick by instinct:

| artifact | what it CLAIMS | what unreachability means |
| --- | --- | --- |
| **a REFUSAL** | *the tier declines this behaviour* — a claim about the **boundary** | the claim is **FALSE**; the tier answers where it says it stops |
| **a CHECK** | nothing about the tier — only *if this happens, fail* | the antecedent is **unmet today**, which is a fact about the **register's contents**, not about the checker |

**A refusal's unreachability falsifies it. A check's unreachability is just the
world not having produced its input yet** — and the input here is *a tier with no
declared divergences*, which every future tier starts as. **Deleting the check
would make its own resurrection silent**, which is the reverse of the dead-code
instinct and the right call: *dead code is removed because nothing will ever
reach it; this will be reached by the next tier that files nothing.*



**The discriminator is what the arm CLAIMS**, not whether it runs. An
exhaustiveness arm claims *the match is total*; **a refusal claims the tier
declines this behaviour** — and a claim about the tier's boundary is falsified
by unreachability in a way a totality obligation never is. **Documented is doing
real work in that first row**: an undocumented by-construction arm is
indistinguishable from the second kind **by reading**, which is the only
instrument available here.

**And the audit is the deliverable, with no new defect found** — which is the
outcome a lane should be able to report without embarrassment. *A law's first
application producing "we are clean, and here is the distinction your law was
missing" is worth more than a hit.*



**AND THE ROW WAS GATED BOTH WAYS ON THE FIRST TRY**, with two named theorems
(`es_div_1_still_divergent`, `es_div_1_has_not_widened`) — **§5.0a's
both-directions requirement implemented before it had been exercised anywhere.**
*A requirement that is met on its first use was specified at the right level of
detail.*

**AND A REFUSAL CAN BE USED AS AN INSTRUMENT — the model emitting the datum the
census cannot see** (Ada inch 2). The construct census **cannot see
`AssignStmt`'s target-child shape**, because libadalang's `CallExpr` covers
**both calls and indexed components**. Rather than guess a split or defer the
inch, the tier will **REFUSE every non-simple target** with
`RefusalCause.unsupported` citing **ARM 5.2**.

> **A REFUSAL IS A PENDING MEASUREMENT: honest, countable, and read off the
> MODEL by the next census.**

**AND THE CYCLE CLOSED, WITH AN OUTCOME STRONGER THAN THE ONE IT WAS DESIGNED
FOR** (Ada child-kinds, `43926b0`, merged). The measurement came back and
**RE-AIMED THE RUNG**: the refused **16.3%** needs **COMPOSITE VALUES**, not
wider target patterns —

> **widening would recognise `A(I) := X` and then have nothing to store into.**

**The pending measurement did not fill a gap in the plan. It replaced the plan's
next step.**

**That is the difference between a measurement and a checklist item**, and it is
why the refusal-as-instrument move earns its cost: a gap that gets *filled*
confirms the plan's shape, while **a gap that gets MEASURED can convict it.** The
lane was one inch from building the wrong widening — correctly, competently,
and into a construct with nowhere to put its result.



**The move is worth naming because the alternatives are both worse.** Guessing
the split puts an unmeasured number into the plan (§5.4a's motivated error);
deferring the inch waits for an instrument nobody is building. **Refusing turns
the gap into a datum** — every refusal is a row, the rows are countable, and the
count is exactly the measurement the census could not take.

**And it inverts the usual direction of evidence**: normally the instrument
measures the model. Here **the model measures for the instrument**, which is
available whenever the model can *recognize* what it cannot *handle*. That is
the same property §5.2's four causes already require — **a refusal names what it
refused** — used as a source of data rather than as an admission.

**AND A FIFTH CORRECTNESS SHAPE, owed by every RESOLUTION rung: A RESOLUTION CAN
BE WRONG, NOT MERELY MISSING** (Go, `fef0b79`, on master).

> **`pkg.F` where `pkg` is SHADOWED BY A LOCAL is a value selector wearing a
> package's name.**

**The two failures land on opposite sides of this section's own boundary**, and
that is why the shape needs naming. A **missing** resolution is a **refusal** —
loud, classed, and retiring on a schedule (§5.2's four causes). A **wrong**
resolution is **a value**: the model resolves confidently, steps something real,
and returns an answer that is simply not the program's. **The first is a
REFUSE; the second is a DIVERGE**, and DIVERGE is the one this scoreboard
requires to be zero.

> **Every resolution rung owes a SHADOWING ROW.** A resolver's acceptance case
> is not complete until it contains a name that *looks* resolvable and is not.

**This generalizes past `pkg.F` to every name-to-thing step a tier takes** —
imports, selectors, methods, builtins: wherever a model turns a **name** into a
**thing**, the language usually provides a way for the same spelling to mean
something else, and the tier that models only the *expected* binding has built a
resolver that cannot be wrong **in its own tests** while being wrong in the
corpus. It is §5.6's discriminating-row law pointed at resolution: **the row
that matters is the one a naive resolver gets confidently wrong.**

**AND A REFUSAL'S CAUSE MUST BE WITNESSED SEPARATELY FROM ITS SITE, OR THE SITE
GETS BLAMED** (pyc inch 3). The naive witness **REFUSES** — a body-assigned
local, hitting **the capture rule** — and **a lane writing only that row would
conclude the surface is out of tier.** The paired witness, with a **parameter
binding**, **MATCHES.**

> **What refuses is the CAPTURE RULE, which has nothing to do with dicts.**

> **A REFUSAL NAMES A SITE. It does not name its CAUSE — and the site is what a
> reader will blame.**

**This is the witness-spelling law's other half** (§5.4: *a witness must fail for
the reason it names*). That one keeps a row from failing for an **unrelated**
reason; this one keeps a row that fails for a **real** reason from being read as
a fact about **the wrong construct.** **The instrument is the same in both
cases: a PAIR** — one row that refuses, one that matches, differing in exactly
the feature under test.

**AND A REGIME THE TIER CANNOT WITNESS AT ALL, NAMED AS SUCH.** Dict-genexp
laziness is **observable only if the object outlives a mutation** — and
**outliving is exactly what the binding refusal forbids.**

> **An EPISTEMIC BOUNDARY, stated as a fact about the INSTRUMENT rather than as
> a gap in the MODEL.**

**Which is a third thing a tier can say about a behaviour**, beside *modelled*
and *refused*: **"the tier cannot construct an experiment that would tell."**
Recording it as a model gap would be **false** — the model may well be right —
and recording nothing would leave a silence indistinguishable from coverage.
**It is the §5.0a instinct applied one level earlier**: where a declared
divergence says *we know we differ and here is the debt*, this says **we cannot
find out, and here is why the question is unreachable from inside.**

**AMENDED ONE COMMIT LATER, BY THE LANE THAT MADE THE CLAIM — AND THE CLAIM WAS
FALSE** (pyc, `fcb1463`, ticketed; verify at landing). The lane wrote the
witness anyway and it found **the tier's first fully-probeable DIVERGE**: the
genexp-over-dict cursor **snapshots at FIRST RESUME** where **PEP 289 requires
`iter()` at CREATION** — CPython raises on create-mutate-next, **the model
answers.** The lane's own words:

> **"The claim is exactly why I did not look."**

> **AN EPISTEMIC-BOUNDARY CLAIM IS ITSELF A CLAIM, AND IT WANTS A WITNESS
> ATTEMPT BEFORE IT LANDS.** *"Cannot be witnessed"* was **testable, and
> false.**

**Both halves stand** (MEAS-181). The **category** is real — a tier can be
unable to construct the experiment, and saying so beats silence. What the
original did not carry is that **it is the most self-sealing claim in this
register**: every other claim invites someone to check it, and **this one
argues, in advance, that checking is impossible.** *A claim that explains why no
evidence will arrive is the one claim that must arrive with evidence.*

**The practical form**: an epistemic-boundary row is **landed only after a
witness attempt that FAILED to construct** — and **the failed attempt is what
gets recorded**, not the conclusion. *"I tried to build the experiment and here
is the step that cannot be built"* is a measurement; *"the tier cannot witness
this"* is a prediction about all possible experiments.

**AND WHY EVERY EARLIER WITNESS MISSED IT: THEY ALL ITERATED IMMUTABLE OR LAZY
SOURCES.** It took **the dict composition** to expose it — *the one thing that
inch actually added.*

> **COMPOSITION IS A CENSUS AXIS. Singles find nothing on it, by construction.**

**A per-construct census enumerates constructs and therefore tests each one
against a default context**, which is exactly where a composition defect cannot
appear. **The tier had covered both halves and neither cover implied the pair** —
and this is the general shape a coverage table cannot see, because *the table's
rows are the things it thought to list.*



**AND A DEFINED PANIC IS NOT A TIER GAP — STATED AS A THEOREM SO IT CANNOT
RE-COLLAPSE** (Go §G24, `eb1e8b0`). `Div` panics resolve into `PkgOutcome`'s
three cases, so **the model's panic is a MODELLED OUTCOME, not an
`unsupported`.**

> **A behaviour the language DEFINES as a failure is a value of the outcome
> type, never a hole in the tier.**

**This is §G14's mis-bucketing prevented STRUCTURALLY rather than by
vigilance.** The mis-bucketing law says a wrong class mis-schedules the work;
**a three-case outcome type makes the wrong class unrepresentable** — the
distinction that had to be remembered is now one the elaborator enforces.
*Where a rule is at risk of re-collapsing, the durable form is a type, not a
reminder.*

**AND A REFUSAL CAN BE HONEST ABOUT THE MODEL AND FALSE ABOUT THE WORLD — the
leaf-encoding trap** (Ada inch 2, branch `adainch2`, ticketed; verify at its
landing). `extract.py` emits **`children` when a node has children and `text`
otherwise**, so an `if` with no `elsif` carries `ElsifStmtPartList` as a **LEAF
WITH EMPTY TEXT** — in **30 of 31 fixtures.**

**A walker written from the GRAMMAR would refuse 30 of 31**, and the refusal
would be **correct about the walker and wrong about Ada**:

> **The model would have said *"I do not model this"* about a construct it FULLY
> MODELLED.**

**That is a refusal-correctness shape the four causes do not cover**, and it is
worse than a mis-bucketing (§5.2's mis-scheduling law) because **the class is
right**: `unsupported` is exactly what a walker meeting an unrecognized shape
should say. **The defect is one layer down, in the ENCODING** — and it surfaces
as a construct the tier believes it lacks.

> **Only CORPUS-DERIVED shapes catch this. A grammar tells you what the language
> can say; only the extractor's own output tells you what your tier will
> RECEIVE.**

**And the lane cross-checked it by arithmetic**, which is the part worth
copying: **31 `IfStmt` − 9 `ElsePart` = 22 nulls**, an independent count of the
same fact from a different column. *A shape discovered by reading is a
hypothesis; the same shape arrived at by counting is a measurement.*

**AND THE GATE IS TWO-SIDED, WHICH IS WHAT COMPLETES THE SHAPE** (Go E1,
`4a9f9ec`, on master; the census found **484 shadowing binding sites across 198
stdlib files**, so this is a live surface and not a corner). Both error
directions are real, and **a battery that bounds only one of them licenses the
other**:

| direction | what it does | cost |
| --- | --- | --- |
| **RECKLESS** | resolves a **shadowed** use | **wrong answer** (DIVERGE) |
| **TIMID** | refuses an **unshadowed** use | **lost reach** (a REFUSE that need not exist) |

> **A merely-CONSERVATIVE resolver fails this gate exactly as a reckless one
> does.**

**The timid direction is what a naive fix causes**, which is why it needs a row
rather than a note: Go's `:=` **binds only from its declaration point**, so a
use **PRECEDING** the shadow, and one whose shadow sits in a **SIBLING BLOCK**,
**must both still resolve.** A resolver that refuses on the mere *presence* of
the name is safe in the way that costs the tier its corpus. The battery is
**10 rows, exit 6 on failure, non-vacuity run — reckless fails 4, timid
fails 2.**

**This is the paired-guard law (§5.2) arriving where it is hardest to
believe**, because one side of the pair looks like caution rather than a
defect:

> **A CORRECTNESS GATE BOUNDS BOTH ERROR DIRECTIONS. Over-refusing is a failure
> mode, not a safe default.**

The two directions retire on different schedules, too — the reckless side is a
**DIVERGE** and must be zero, the timid side is a **REFUSE** that shows up in
coverage — so pooling them would hide a correctness defect inside a coverage
number (§5.2's own reason for separating causes).

**AND A ZERO *DELTA* READS DIFFERENTLY AGAIN — IT CAN BE THE HEADLINE** (pyc's
3c-i-c; **ticketed**). The inch's result is that **the whitelist did not move**:

> **The inch ADDS CAPABILITY WITHOUT ADDING A REFUSAL.**

**That is a shape worth naming, because it is the one result a refusal census
reports as silence.** A capability inch normally shows up as rows *leaving* the
whitelist; this one shows up as **nothing at all** — and a reader scanning the
diff of the census sees an unchanged file. **The non-move is the finding, and it
has to be claimed in prose because the artifact cannot claim it.**

**Read against the two zeroes above, the three are now distinct and must not be
pooled**: a **zero count** for a class the tier can emit is about the **corpus**;
a **zero count** for one its API cannot build is about the **tier**; and a **zero
DELTA across an inch that added capability** is about **the inch** — the tier
grew and its refusal surface did not. **Same digit, three claims**, and only the
third is evidence that a change was strictly additive.

**And the honest limit, which keeps it from becoming a boast**: an unchanged
whitelist proves the inch added **no new refusal**, not that it added **no new
behaviour** — those are different statements, and only the first is what a
refusal census can see.

**AND BY-CONSTRUCTION GATES RECONCILE WITH "PRESENT AND GATED" — they are
the STRONGER form, not an exception to it.** A tier-local refusal type may
legitimately lack a class outright (Go's `GoRefusal` has no `undefined`).
That is not a divergence from the rule, because the two live at different
levels:

* the tier's local type **maps into Core's four-class cause**;
* the **gate is the THEOREM that the image excludes the class**.

So **the scoreboard sees the constructor** — Core's vocabulary is complete
and the column exists — while **the tier cannot construct it**, provably,
rather than by a check that might not fire. A by-construction gate is
*better* than a runtime one for exactly the reason §3.4 prefers type-level
invariants to N lemmas: nothing has to fire.

The two instances: **ES's `es_never_undefined`** (a theorem, beside
`es_never_orderDependent`, and ES's own file already records both as
*"PRESENT and GATED"*) and **Go's build-breaking guard**. Different
mechanisms, same shape — the class is nameable by the family and
unconstructible by the tier.

**AND ES'S OWN REFINEMENT IS PRESERVED, because it is a real finding.** ES
did not merely drop a class — it **split `environment` in two by
RETIREMENT SCHEDULE**: `unmodeledIntrinsic` (a built-in outside the slice,
retires by widening it) versus `environment` (a host facility, *does not
retire by building more language*). §5.2 justifies its four causes on
exactly that criterion — *they retire on completely different schedules* —
so by the family's own rationale ES's distinction is legitimate. It lives
in the **payload** today, where the tier's docs can explain it and the
scoreboard still aggregates on the class.

**And it is registered as a candidate FIFTH class, not dismissed.** If a
second tier independently splits `environment` the same way, that is the
convergence standard §9.3 used to ratify the span field names — a
measurement, not a taste — and §5.2 should gain a fifth cause. One tier's
distinction is a payload; two tiers' identical distinction is a class.

**AND THE RULING IS NOT DELIVERED UNTIL THE CLASS REACHES THE JSON.** The
runner's canonical JSON currently **drops the refusal class**, so the
scoreboard **cannot bucket** — which is the one thing §9.4's shared
vocabulary and this ruling exist to make possible. A cause type that no
consumer can read is a well-typed private note.

**Follow-up: an OPT-IN field**, on the `--observations` model — off by
default so the canonical output stays byte-stable for every existing
`--compare` baseline (§5.4), on when a scoreboard asks for it. Recorded
here rather than in a lane's notes because it is the ruling's **delivery
gap**, not an implementation detail: until it lands, the four classes are
family law that the scoreboard cannot see.

**Ada's inch 1 consumes this directly**: four constructors, `π` = the ARM
paragraph reference, `undefined` carrying its 1.1.5 erroneous-execution
citation, and `order-dependence` present and gated until Ada measures
whether it fires.

**A TIER INVARIANT ON MEMBERSHIP SITES, from SV, and it guards a mistake
that would be invisible once made.** In SV, **X-propagation must NEVER
become `orderDependence`, or any refusal.** Unknown (`x`) is a **VALUE of
the 4-state semantics** — misfiling it as a refusal silently converts
**4-state into 2-state-plus-errors**, which is a different language
wearing the same name. Nothing would fail; the tier would simply stop
modelling SystemVerilog.

The candidate generalization:

> **A value the spec defines as a VALUE is never a refusal — however much
> it looks like "we don't know."**

**AND ITS INVERSE, measured on a construct where ANY answer is the defect** (pyc
successor's 3c-i-c census, branch `pyc-3cib2` at `0014d6d`; **re-gate queued —
conditional on that landing**). CPython:

```python
# (illustrative — the shape, not a tree file)
e = enumerate(d)
d[2] = 'b'
list(e)          # RuntimeError: dictionary changed size during iteration
```

A **snapshot** model prints a value here. It is not printing the *wrong* value:

> **A SNAPSHOT IS WRONG BY ANSWERING, NOT BY ANSWERING WRONGLY.**

**This belongs beside the silent-wrong-answer family as its inverse, and it
inverts the diagnostic with it.** The usual defect is *the model and the oracle
disagree about a value*; here **they do not disagree about a value at all —
they disagree about whether there IS one.** So the ordinary comparison cannot
see it: the model succeeds, the language raises, and a comparator keyed on
*"same printed value"* has nothing to compare. **The row is catchable only
because both harnesses compare the exception CLASS and not merely stdout and
exit status** (MEAS-52) — a rule that reads like hygiene until a construct
arrives whose entire specified behaviour is the raise.

**The design consequence, and it is the reason to record this rather than fix
one model:** a snapshot is not *approximately right* about such a construct, it
is the **wrong shape**. The mutation guard is a **feature of the iterator**, not
an accident of an implementation, so a model that cannot express *"observing
this is an error"* has no correct value to choose. **Check what a candidate
model does where the language's answer is a REFUSAL, not only where it is a
value** — that is §5.6's *rows the wrong model CANNOT STATE*, arriving from the
verdict side.


**Stated as a QUESTION for the tiers that would own the answer, not as a
family fact.** Two shapes look like siblings and neither is ruled here:
**Python's `NaN`** (a value in IEEE 754, and §3.5 already treats floats as
a component rather than a gap — so the question is only whether any tier
is tempted to refuse it), and **C's indeterminate-but-NOT-UB reads**, which
is genuinely open because the C tier currently arms *indeterminate read* as
one of its eleven UB classes; whether the not-UB subset is a value or a
refusal is **the C lane's to answer**, and the two cases must not be
conflated by this document. If two tiers answer the same way
independently, that is the convergence standard again and the invariant
gets promoted from tier to family.

**Why it belongs beside membership rather than beside refusal**: both a
membership site and a misfiled value are cases where *"the model does not
have one answer"* is true for **completely different reasons** — one
because the language permits several, one because the language supplies a
specific value that happens to mean uncertainty. The scoreboard cannot
tell them apart after the fact, so the distinction has to be made at the
modelling site.

**Why it is a REFUSAL cause and not a fifth verdict.** A refusal is what
the model actually emits today, on both boards. The alternative — a
genuine ORDER-DEPENDENT verdict meaning "the model ran, and the answer is
order-sensitive" — requires the model to enumerate the admissible orders
and show the observable invariant. That is a different and much larger
obligation, it is the honest home of §3.4's explicit-parameter design, and
it is named here as a priced fork rather than taken.

**AND THE IMPLEMENTATION LAW FOR THE CLASS FIELD, from the fuelMono lane**
(**LANDED**, `6b91a8d`). A model that reports
a refusal *class* alongside its outcome has two answers about one event, and
two answers is exactly the shape that drifts. The ruling:

> **ONE EXECUTION, TWO PROJECTIONS.** The outcome and its class come from the
> **same run** — `callInRaw` projected two ways, with
> `callInMono_eq_ofHalt` tying them — **so the two answers cannot drift.**

A second run, or a table consulted after the fact, would let the class describe
a different execution from the outcome it labels, and nothing would fail. This
is §3.4's routing discipline pointed at a *field* instead of a monad layer: the
class is not extra data about the run, it is **a view of it**.

**AND THE FIELD'S PRESENCE IS A THEOREM, not a convention.**
`refusalClass_isSome_iff` settles what an absent class means:

> **Absence means the run did NOT refuse — never *"refused, unclassified"*.**

Left as a convention, `none` is ambiguous in precisely the direction §5.2 exists
to prevent: an unclassified refusal would be **invisible to every per-cause
count** while the run itself was a refusal, and the scoreboard would read the
gap as *"no refusals of that kind"* rather than *"a refusal we failed to
classify"*. That is the silent-absence family (§5.4) inside the verdict system,
and a theorem is what removes it.

**AND THE CENSUS'S `WHITELIST_CLASS` IS NOW CROSS-CHECKED BY THE INTERPRETER
ITSELF**, which is the part that generalizes past this tier:

> **A table asserting how the interpreter classifies is an UNFALSIFIABLE CLAIM
> ABOUT the interpreter — until the interpreter is asked to confirm it.**

The whitelist was exactly that: a hand-maintained statement of the model's own
behaviour, checked against nothing, in an instrument whose whole purpose is to
report that behaviour. It is §5.4's docstring laws in table form — *a claim
about the world, and therefore checked data or prose that will go stale
silently* — and the fix is the same fix: **let the thing being described answer
the question.**

### 5.3 VACUOUS is not a verdict — and neither is MUTUAL REFUSAL

A run that executed **nothing** must never score as agreement.

**AND A LANE BROKE ITS OWN LAW IN THE COMMIT THAT LANDED IT — CAUGHT BY THE
GATE, NOT BY REVIEW** (pyc, `fcb1463`, ticketed). Having just written *a refusal
names a site, not its cause*, the lane **attributed `still_loud`'s refusal to
the binding** — when **the capture rule is what refuses.**

> **LAWS DO NOT INOCULATE THEIR AUTHORS. GATES DO.**

**This register now has four instances of the same shape in three days**, worth
reading as one fact rather than a run of coincidences: the heading guard
convicting §9.5a's own author; the enforcing lane minting owner-namespace ids
while conforming to the sender-namespace rule; **this document's §9.0
requirement producing three malformed headings in three lanes**; and now a lane
violating a law **inside the commit that introduced it.**

> **Writing a law is the moment of MAXIMUM confidence and MINIMUM habit — which
> is exactly when a mechanical check earns its cost.**

**A law's author has thought about it more than anyone and applied it fewer
times than anyone**, and no amount of care fixes that: only something that runs
can. *The gate does not care who wrote the rule.*

**AND A GREEN CAN CREATE DEBT AT THE MOMENT IT IS EARNED** (Lean tier). The
`trace_state` / first battery **never fired**, and the lane's disposition is the
row:

> **It never fired; it is DEBT IN A GREEN FILE.**

> **DIAGNOSTIC MACHINERY THAT A GREEN PROVES UNUSED BECOMES DEBT AT THE MOMENT
> OF THE GREEN.**

**Scheduled for deletion in the next landing, which is the right cadence** — not
removed in the landing that proved it unused, since **that landing's subject is
the proof, not the cleanup.** *The green is what converts scaffolding from
"possibly load-bearing" to "measured inert", and inert scaffolding in a green
file is the F7 surface this section keeps finding by census — here caught by the
verdict itself.*

**AND THE INVERSE DISPOSITION, WITH ITS ARGUMENT STATED AT THE ROW** (C's seam
lift). One row was **RETAINED against a dedup sweep**:
`EvalM.run_refuseUnsupported`, because **the capture lives in C's primitive BY
DESIGN, so no call site can forget it.**

> **RETENTION AGAINST A DEDUP SWEEP NEEDS THE DESIGN REASON STATED AT THE ROW.**

**The declined-lemma law's inverse** (*a lemma that cannot fail is not a lemma;
"the sibling has one" is not a consumer*): that one removes an artifact whose
justification is a resemblance; **this one keeps an artifact whose justification
is a design decision — and requires the decision to be written where the sweep
will next arrive.** *A duplicate retained silently is indistinguishable from a
duplicate missed, and the next sweep is run by someone who was not in this
conversation.*

**AND THE FAMILY HAS ITS FIRST CATCH AT CREATION RATHER THAN BY CENSUS**
(analog A1, ticketed; verify at landing). The lane wrote the sibling-mirroring
`observation_sound`, **saw the conclusion was definitionally trivial once
`output` instantiates**, and **removed it — leaving a comment where it stood so
nobody re-adds it.**

> **A LEMMA THAT CANNOT FAIL IS NOT A LEMMA, and "the sibling has one" is not a
> consumer.**

> **SYMMETRY IS A REASON TO LOOK FOR A LEMMA, NEVER A REASON TO KEEP ONE.**

**Two things make this worth a row.** It is **F7 — dead framework surface —
caught AT CREATION**, where every previous instance in this tree was found by a
later census; and the **comment left in place** is what stops the next author
re-deriving it, since *the symmetry that suggested it will still be there.*

**And "the sibling has one" is the exact reasoning that would have kept it**,
which is why it needed naming: a mirrored lemma **looks like completeness** and
reads as diligence, and the tell is that its justification is a fact about
**another file** rather than about a consumer in this one. *A consumer is a
theorem that needs it; a sibling is a resemblance.*

**AND A THIRD MECHANISM IN ONE LANE, WHICH TURNS THE FAMILY INTO A TAXONOMY BY
MECHANISM** (Go §G23, `9a6d6ad`). The blank-discard guard had **`| _ => true`
with unbound parameters**: the body **refused**, the **fallback fired**, and
**the row PASSED.** Flipping it gave **0 errors** — the row had never been
testing anything.

> **A FALLBACK ARM RETURNING `true` CONVERTS A FAILING RUN INTO A PASSING ROW.**

**Three mechanisms, one lane, and naming them separately is the point** — they
share a symptom (*a green row that tests nothing*) and **no two of them are found
the same way**:

| mechanism | how the row goes hollow | how it is caught |
| --- | --- | --- |
| **hand-typed oracle** (§G13) | the expectation is a human's reading, so both columns come from one source | provenance — *the oracle writes its own column* |
| **byte-identical section** (§G15) | the row duplicates its neighbour, so it cannot disagree | reading the rows against each other |
| **catch-all fallback** (§G23) | the row's own failure path returns success | **flipping the model** — nothing else reaches it |

**The catch-all is the worst of the three, because it converts a REFUSAL into a
PASS.** The other two produce rows that never had content; this one **takes a
row that was working, lets it fail, and reports the failure as agreement.**
*Every earlier vacuity in this section is an absence; this one is an inversion.*

**AND THE STRUCTURAL APEX OF THIS FAMILY: NON-VACUITY IS A CHAIN OF TWO LINKS,
AND A GUARD ON THE INNER LINK CANNOT SEE THE OUTER ONE** (analog tier's founding
census, branch `analog-m0-census` at `491b944`; **uncompiled and stated as
such**).

The chain is: **an inhabited WORLD set, then an inhabited BEHAVIOR set.**
`RealizableUnder` was added **precisely to stop empty behavior sets** — and it
is itself guarded by `allowed world`. So **an unsatisfiable `allowed`
discharges all three obligations at once**, and `#assurance_report` prints a
**real-looking result**. Measured: **24 assurance cases, 0 carrying a world
witness** before the inch.

> **THE GUARD'S BLIND SPOT IS POSITIONAL, NOT AN OVERSIGHT — the guard cannot
> see the outer link BECAUSE THE GUARD IS ITSELF INSIDE IT.**

**That is what makes this the apex rather than another instance.** Every other
vacuity in this section is a **missing check**: a row that never ran, a premise
that was false, a comparison that could not fail. This one is a **check that was
added for exactly the right reason, is correctly implemented, and is
structurally incapable of catching the case that subsumes it.** No amount of
care inside the guard reaches it; **the fix has to come from outside — a world
witness, at the outer link.**

**The general form, since every tier with layered obligations will meet it:**

> **Enumerate the LINKS of a non-vacuity chain and ask, per link, WHICH GUARD IS
> OUTSIDE IT. A link whose only guard is nested within it is unguarded.**

**AND THE PRIORITY OF PRACTICE IS RECORDED WITH IT.** The July tier
**implemented §5.3's ruling in Lean before this family minted it as prose in
August**: `AssuranceCase` **structurally refuses assembly from unrelated theorem
names** (`Circuit/Surface.lean` — verified on master), and the branch's
`SourceBinding` equalities block circuit substitution. **Cite `Surface.lean` as
prior art wherever §5.3 is stated** — a ruling this document wrote down had
already been built, which is the convergence standard (§9.3) arriving from code
to prose rather than the other way round.

**AND THE SHARPEST FORM IS A THEOREM THAT IS VACUOUSLY TRUE BECAUSE ITS PREMISE
IS FALSE** (R-track chain document). Plain `BoundRefines` is **FALSE** —
refuted at `pos := .int 5`, where the shipped `bound()` refuses so the
∃-conclusion has no witness (cookbook §11). A theorem premised on it is
therefore **vacuously true**, and the original `RecursionStep` was exactly
that: **green, elaborating, and about nothing.**

> **A FALSE PREMISE DOES NOT WEAKEN A THEOREM — IT VACATES IT, and a vacated
> theorem PASSES.**

**Which is why the repair is load-bearing rather than cosmetic**: `BoundRefinesW`
is the form the chain must use **throughout**, and a single downstream statement
left on the old premise re-opens the hole silently. **The other vacuity shapes
in this section announce themselves as empty** — a run that executed nothing, a
row that never ran. **This one announces itself as a proof**, which is the worst
available disguise: nothing is missing, the tactic closed, and the artifact is a
theorem in every respect except subject matter.

**The check is the one §5.3 already prescribes, pointed at the premise**: ask
what the statement claims **when the interesting case does not apply** (§8's
implication rule), and if the answer is *"nothing at all"*, the premise is
carrying the theorem rather than the other way round.

**AND THE DEEPEST FORM OF THIS FAMILY: A DIFFERENT HYPOTHESIS WITH THE SAME
STATEMENT** (pyc inch 2). `sbEvict_lit`'s **∃-quantified body HID the previous
inch's ingestion change from the compiler**: **zero theorems break**, three
prose sites are stale, and the `room` hypothesis **now prevents an unmodelled
STATE CHANGE where it used to prevent a REFUSAL.**

> **The statement is IDENTICAL, the meaning MOVED, and no tool can see it.**

**This is model-matches-code at the level of a hypothesis's RATIONALE**, which
is a layer below everything else this section covers. Every other divergence
here is visible to *something*: a red, a census, a diff, a verdict. **A premise
whose purpose has changed under a stable statement is visible to nobody** — the
elaborator is satisfied, the theorem is true, and the file compiles exactly as
it did.

**THE LANE ASKED WHAT INSTRUMENT COULD SEE IT. The honest answer is that none
can, AT THE STATEMENT LEVEL — and that the rationale becomes checkable the
moment it is written as a claim with a witness.** *"The `room` hypothesis
prevents X"* is a proposition, and it is testable in exactly one way:

> **DROP THE HYPOTHESIS, AND A SPECIFIC NAMED THING MUST HAPPEN.** Write that
> thing down as a row, and the rationale is no longer prose.

**When the purpose moves, the row's SUBJECT changes** — from *a refusal* to *an
unmodelled state change* — and **the row breaks even though the theorem does
not.** That is §5.3's own discipline (*pair every "did not change" with a "did
happen"*) applied to a **premise**, and it is the only construction that puts a
rationale inside the reach of a tool.

**The limit is worth stating too, because the lane's own answer named it**:
falsifiable witness pairs cover **behaviour**, and a rationale is not behaviour
until someone writes the counterexample it excludes. **An unwritten rationale
stays unfalsifiable no matter how good the instruments are** — the fix is not a
better tool, it is a sentence that could be wrong.

**AND THE MECHANISM HAS NOW BEEN NAMED, WHICH SHARPENS THE WHOLE ENTRY** (pyc
inch-3 design; off-repo, conditional). The `room` hypothesis's **failure mode
changed LOUD → QUIET**: the ∃-quantified body, plus **a proof that never opens
it**, means a violation that used to announce itself no longer does.

> **The hypothesis is UNCHANGED and STILL NEEDED. What changed is that its
> VIOLATION IS NOW SILENT.**

**That is the transition no instrument can see, stated precisely** — better than
*"the meaning moved"*, which is where this entry stood yesterday. **The premise
did not move and the theorem did not move; the OBSERVABILITY of the premise's
failure moved**, and observability is not a property any tool in this tree
measures. It was caught **only because the lane re-read its own prose.**

**And the repair is the constructive half**: the rationale is now written so
that **dropping the hypothesis produces a WRONG WORLD — with the exact heap
inequality and two named witnesses.** That is *drop the hypothesis and a
specific named thing must happen*, discharged: **the named thing is a world, an
inequality and two witnesses, and none of them is prose.**

**AND A HYPOTHESIS TAXONOMY FALLS OUT, because the RETIREMENT MOVE DIFFERS BY
KIND.** `room` was reclassified from a **TIER** hypothesis to a **MODELLING**
hypothesis, and the reclassification changed what closing it means:

| kind | what it says | how it retires |
| --- | --- | --- |
| **TIER** | the tier does not model this region | **widen the tier** |
| **MODELLING** | the model represents this region approximately | **model the thing** — here, **model the eviction** |
| **BRIDGING** | two layers are related only under this condition | **prove the relation**, or make it structural |

> **THE HONEST RETIREMENT IS TO MODEL THE EVICTION, NOT TO WIDEN THE TIER.**

**Misclassifying a modelling hypothesis as a tier hypothesis licenses the wrong
repair**, and the wrong repair is the *cheaper* one — widening a tier is a
declaration, modelling a behaviour is work. **So the taxonomy is not
bookkeeping: it is what stops a hypothesis being retired by redefining the
question.** A register row carrying a hypothesis should name its **kind**, for
the same reason a refusal names its **cause** (§5.2): **the kind determines who
owes the work and what "done" looks like.**





**And the same rule one level up, from a measured master defect (§3.4's
erosion clause): TWO REFUSALS MUST NEVER SCORE AS AGREEMENT.** A
differential harness compares the two sides to each other, so when both
refuse it reports parity — **while both are wrong.**

**The blindness belongs to the AIMING, not the instrument** (§3.4): the
same unmodified `diff_test`, pointed at **CPython** instead of at a second
model, **convicts** — *predicted 25, came back 25*. **Agreement between two
models is not evidence; agreement with the ORACLE is**, and that is made
operational by **removing the second model**, not by building a new
harness. While two models must coexist, the refusal census's expectation
column — written from CPython's measured behaviour rather than the
model's — is the instrument that covers the gap.

**AND THE SNEAKIEST FORM OF THE SAME FAILURE: a HAND-TRANSCRIBED
EXPECTATION.** A differential table's expected column was **typed by
hand**, and **it passed.** The defect is invisible at the moment it is
committed and matures later:

> *"The whole claim is that two independent implementations agree, and a
> hand-copied expectation makes the Lean side the source of BOTH columns
> the moment someone 'fixes' a row."*

A transcription is a **third implementation nobody declared** — a human's
reading of the oracle, which degrades into the model's own output the
first time a row is adjusted to make a test pass. Nothing fails; the
differential simply stops being one.

> **A differential expectation must be GENERATED by the ORACLE side, never
> transcribed. It would have shipped looking identical and meaning
> less.**

The fix is mechanical and is the shape to copy: the rows are **`printf`'d
from the compiled Go binary** and **mechanically rewritten into `#guard`
syntax**. That is the same provenance the refusal census's expectation
column already has — **written from CPython's measured behaviour** — and
the two together make the rule general rather than a Python habit: **the
oracle writes its own column, in every tier.**

**AND THE SIBLING CASE IS IN §5.4** — transcribing another **lane's source**
instead of an **oracle's answers**. Same defect, different remedy: an
expectation is a **value** and can be **generated**; a source line is **text**
and can only be **gated**. A lane that meets either should read the other.

Both halves of §5.3 are the same law: **a check must not report sameness
where there was no content.** Python's
harness carries `"live"`; C's scoreboard carries the statement count. This
is an instrument-level ERROR, not a verdict — a scoreboard that reports it
as MATCH is broken, and one that reports it as REFUSE is lying about
coverage.

**AND THE SHARPEST NON-VERDICT OF ALL, WHICH THIS LANE LEARNED BY BEING
CORRECTED** (Lean tier, fork `5414bb4`; **6/27, name and level categories
closed**). **Both fixes the coordinating role proposed for a matcher red would
have RESTRUCTURED THE PARSER UNDER PROOF.**

> **A PROOF OBLIGATION THAT CAN ONLY BE DISCHARGED BY REWRITING ITS SUBJECT HAS
> NOT BEEN DISCHARGED.**

**At full generality, and this register adopts it as a law rather than a Lean
habit:**

> **THE SUBJECT OF A VERIFICATION IS IMMUTABLE TO THE VERIFIER. Any fix that
> edits it changes the QUESTION.**

**The tier makes the cost legible in a way most do not**: the fork's entire
standing rests on **the divergence being exactly four edits, tripwired**, so an
edit to buy a proof is **visible as a number** — *"buying a proof by editing the
artifact under proof is the one purchase this corner cannot make."* **Where the
subject is a vendored source, a spec text, or another lane's tree, the same
purchase is available and leaves no counter to move.**

**And it belongs beside VACUOUS for one reason**: both are **greens that are not
about anything.** A vacuous theorem proves a statement with no content; a
subject-edited theorem proves a statement about **a subject that exists only
because the proof needed it.** *The second is harder to see, because everything
in it typechecks and the artifact is real* — **it is simply not the artifact the
claim was about.**

**The mechanical form is a diff, not a judgement.** A verification tenure should
be able to state **which paths were writable and which were the subject**, and a
subject touched during a proof is **a finding, not a step.** *This lane proposed
the edit twice; the guard that would have caught it is a list of paths, not more
care.*

**AND A VACUOUS FLIP WAS CAUGHT BEFORE IT LANDED, WHICH IS WHERE THIS FAMILY IS
CHEAPEST** (pyc, same inch). The candidate witness used **n=1**, which **never
divides by zero** —

> **It would have flipped `unsupported` → `match` WITHOUT ENTERING THE HANDLER.
> Only n=0 proves the catch.**

> **A FLIP MUST EXERCISE THE BEHAVIOUR IT CERTIFIES, NOT MERELY STOP REFUSING.**

**The two are indistinguishable in the scoreboard**, which is the whole hazard: a
row moving from `unsupported` to `match` reads as *the feature now works*, and it
is equally produced by *the test stopped needing the feature.* **Every scoreboard
in this family has this hole**, because a verdict records the outcome and not the
path taken to it.

**The standing form is a question a lane can ask of any flip**: *what would this
row do if the new code were deleted?* **A row that still passes is a row the
feature did not earn** — and asking it costs one re-run, against a wrong number
that survives every later audit because nothing in it looks wrong.

**AND THE RULE COLLECTED ITS SECOND AND THIRD INSTANCES INSIDE ONE INCH** (pyc,
merged `b5c63e8`): **n=1 never divides**, and **`stmt.Try` never raises** — *both
would have flipped to `match` without entering a handler.* **Three catches in one
inch, all pre-certification**, which is the number that makes this a systematic
hazard rather than an anecdote: **a lane writing witnesses reaches for the
simplest input, and the simplest input is the one least likely to reach the new
code.** *The witness-writing instinct and the certification requirement point in
opposite directions by default.*

### 5.4 One census-instrument pattern per tier

`harness/c_construct_census.py` fixed the contract; every tier's
instrument copies it:

* named `harness/<lang>_<subject>_census.py`, output to
  `docs/<lang>-<subject>-census.json`, sorted and machine-readable;
* **A DOCSTRING THAT ARGUES A CASE AWAY IS A CLAIM — CHECK IT AGAINST THE
  CLAUSE IT CITES.** Sharper than the drift below, because prose reasoning
  reads as *justification* rather than as *assertion*. Measured on ES:
  `Completion.lean` argued **in prose** that `Abrupt.brk`/`cont` never need
  a `[[Value]]`. **§14.2.2 step 3 refutes it** — `while (true) { 5; break;
  }` completed **empty**, and the language says **5**. A second, same
  shape: **`V` starts at `undefined`, not empty**, so `1; while (false);`
  answered **1**. Both are the **test262 `-cptn` family** — silent wrong
  answers, found only by **re-reading the pinned spec against the
  docstring** after the inch was green and queued.

  > **The missing GUARDS were the real defect.** The docstring stood where
  > a guard belonged, and prose cannot fail.

  A docstring arguing a case away is doing the job §5.5's manifest exists
  to do — pairing a claim with the clause that settles it — but **without
  the check**, which is the whole of the difference.

  **AND THE SECOND MEASURED INSTANCE ADDS THE WORSE HALF: A FALSE BLANKET
  CLAIM HIDES THE REAL GAP.** `Examples/python/bench_bisect/spec.lean`
  asserted that the live CPython oracle **could not take** its cases. It
  could — since the batch protocol — and the truth was a gap **far smaller
  than the claim**: nine rows added, and **exactly ONE genuinely
  unreachable**, now whitelisted **with its reason** (2026-08-23 audit,
  `## python` HIGH; pyc lane, staged on its queued ticket).

  > **A false blanket claim hides the real gap — the gap was far smaller
  > than the claim, and THE CLAIM IS WHY NOBODY LOOKED.**

  That is the self-preserving property, and it is what makes this worse
  than an ordinary wrong docstring: **a gap with a stated cause is not
  re-measured.** An unexplained gap nags; an explained one is closed
  business. So the false explanation does not merely misinform — it
  **removes the incentive to look**, and it goes on doing that for as long
  as it stands.

  **AND THE CLAIM WAS ABOUT ANOTHER COMPONENT'S CAPABILITY, which is why it
  rotted without anyone touching it.** *"The oracle cannot take these"* was
  true when written and false once the harness gained the batch protocol —
  **a capability claim about a component you do not own is a transcription
  with a timestamp** (the law below), and it rots the same way, on the same
  schedule, for the same reason. The remedy is the same too: it must be
  **checked against the component**, not restated. Nine rows that now run
  against the oracle *are* that check;
* **AND THE REPAIR SHAPE FOR ALL OF THEM: CONVERT THE LIST INTO A THEOREM**
  (Go §G24, `eb1e8b0`). `modelledPkgFuncs` **named `bits.Len`** while `pkgCall`
  **implemented `Len64` only** —

  > **A list that says what a model supports is a CLAIM, and an unchecked claim
  > drifts on the first edit. This one drifted INSIDE ONE RUNG.**

  **Repaired by making the list arity-carrying and `rfl`-checked** by
  `surface_is_honest`, axioms clean. **That is the constructive answer this
  bullet family has been circling**: the docstring laws say *a claim needs a
  check*; this says **what the check should be when the claim is a LIST** —
  not a census that re-reads it, but **a theorem that cannot elaborate unless
  the list and the implementation agree.**

  **And the drift interval is the argument.** A list that goes stale over months
  invites a periodic census; **one that drifted inside a single rung cannot be
  policed by any cadence** — the only instrument fast enough is the elaborator.
  *Where a claim and its subject live in the same build, the check belongs in
  the build;*
* **AND A CLOSED-LIST DOCSTRING IS A TIME BOMB — the 2026-08-13 incident
  REPLAYED FROM A COMMENT** (pyc inch 2). `Expr.genAllocFree` named **"a closed
  list of two"** generator allocators. **`iter` is the third**, and without the
  fix **ordinary Python reports `internal: heap well-formedness violation`.**

  > **A DOCSTRING THAT ENUMERATES IS A CENSUS THAT NO INSTRUMENT RE-RUNS.**

  **The closed-list form is the aggravating factor, not the enumeration.** *"Used
  by `heapEq`, `setDedup`"* is a claim that drifts; ***"a closed list of two"***
  is a claim that **licenses code to assume completeness** — the reader who adds
  the third member is told, in the file, that there is no third member. **The
  docstring did not merely go stale; it argued against its own repair.**

  **And the failure surfaced as an INTERNAL error on ordinary input**, which is
  the shape §5.4a keeps convicting: **the tier's own invariant broke, and the
  message named the invariant rather than the cause.** The same incident had
  already been paid for once in August; **it came back through a comment**,
  because the code was fixed and the sentence that would recreate it was not;
* **A DOCSTRING NAMING A REACHABLE SET IS A CLAIM, AND IT DRIFTS.**
  `Kont.fuel`'s docstring read *"used by `heapEq`, `setDedup`"*; the
  **measured** set is **`heapEq` + `valContains`** — or so a correction
  recorded here claimed.

  **THAT CORRECTION WAS ITSELF WRONG, and the way it was wrong is the
  sharper law.** `setDedup` **IS** reachable — via `applyBuiltin`'s set arm
  (`Eval.lean:392`, two `K.fuel` sites), and its `setDedup_mono` is
  *consumed* in `Obs.lean` through `le_liftRes`. The correcting grep had
  measured **"0 hits FROM `evalCompareOpH`"** — it inherited the **frame of
  the very docstring it was correcting**, and so re-answered the old
  question accurately instead of asking the right one.

  > **A measurement that CORRECTS a claim must not take its SCOPE from the
  > claim it corrects. Sweep the whole surface, not the cited path.**

  This is the retrieval family's worst case, because a correction carries
  *more* authority than the claim it replaces: it arrives with a
  measurement attached. Inheriting the scope makes the second number as
  wrong as the first **and harder to doubt**. The fuelMono lane fixes the
  docstring in its landing ticket, carrying that sentence in it. Nothing failed — a
  docstring naming the wrong consumers compiles exactly as well as one
  naming the right ones, and a lane reading it to decide a blast radius
  (§5.4a) would have grepped for the wrong thing. **A reachable set is
  measurable, so it is checkable**, and a docstring that asserts one
  belongs in the same category as a clause citation: **checked data, or
  else prose that will go stale silently.** Being corrected by the owning
  lane;
* **A TRANSCRIPTION OF ANOTHER LANE'S FILE IS A COPY WITH A TIMESTAMP, AND
  IT ROTS THE MOMENT THEY COMMIT.** The two laws above are about claims that
  go stale when *you* change something. This one goes stale with **no local
  event at all**: the text is true when written, false once somebody else
  commits, and **nothing happens in your lane in between**.

  **Measured half-life: SIX MINUTES.** SoftFloat's
  `harness/softfloat/probe_es_unblock.lean` transcribed ES's `numberToString`
  under the label *"`Convert.lean:219-226` as landed"* (`f255c03`,
  `23:47:56`). ES committed the routing at `9dab312`, `23:54:26` — **six
  minutes thirty** — and the probe went on presenting the **pre-unblock**
  body as the landed one, its two expected-FAIL rows sitting under the
  heading *"The landed version"*. **Anyone running it would have concluded
  the unblock was UNLANDED** — the exact opposite of what that lane had just
  measured, in the file whose whole purpose was to demonstrate it.

  > **A cross-lane transcription must carry a TRIPWIRE in the gate set, or
  > it is a lie with a fuse.**

  Six minutes is short enough that **"be careful" is not a control**: nobody
  re-reads a copy on a six-minute cadence, and no amount of care makes a copy
  notice a commit. The lane's structural fix is the shape to copy —
  `harness/softfloat_consumer_census.py --check-transcriptions` asserts that
  **every text a probe assumes about another lane's file is still in that
  file**, wired into the gate set so the next ES move turns the probe **red
  instead of quietly lying**; its **own failure path is exercised in the
  self-test** (a fixture whose cited text is absent must make the tripwire
  FIRE); and a row **pins the probe's expected-error COUNT**, because a file
  that is *expected to error* is green whatever it says, and the count is the
  only part of an expected failure that can notice a change. *(State stamp,
  §5.4a: that gate is on branch `softfloat-m1` at `046d9dc` and is **not on
  master**, which is why it is described here rather than quoted as a checked
  block.)*

  **FOUR RIDERS — three CONVERGENCES and one sharpening, recorded rather than
  re-minted: this law was already in the document, pointed elsewhere, three
  separate times.**

  1. **§5.3 ALREADY CARRIES A TRANSCRIPTION LAW, aimed at a different target,
     and the PAIR is the statable thing.** There, *a transcription is a third
     implementation nobody declared*: hand-copying an ORACLE's answers
     destroys the **differential**. Here, hand-copying another LANE'S SOURCE
     destroys the **citation**. **The remedies differ, and that difference is
     the useful part** — an expectation is a **value**, so the fix is to
     **GENERATE** it and let the oracle write its own column; a source line is
     **text**, cannot be generated, and so must be **GATED**. Together:

     > **A transcription is an undeclared copy of something you do not own.
     > Make the owner PRODUCE it, or make the copy FAIL LOUDLY when the owner
     > moves. If neither is available, do not transcribe.**

  2. *A check that has never failed is a design, not a control* is §7.1a's
     line about **amendments that have never fired**, re-derived here about
     **gates**. The self-test exercising the tripwire's failure path is that
     rule paying rent in a second place, which is the evidence that it was
     measured rather than phrased.
  3. **The rename is the identifier law below, not cosmetics.**
     `numberStringPreUnblock` names the transcription's **vintage**; *"as
     landed"* named its **status**, and a status is a verdict with a shelf
     life. A copy named for what it is a copy *of* survives the other lane's
     next commit; one named for what it currently *is* cannot.
  4. **And the CHEAP half comes first, which the dispatch did not say and
     which this document owes MEAS-10: STAMP THE COPY.** *"As landed"* is a
     present-tense claim about a file you do not own; *"as landed at
     `f255c03`"* stays true forever. A stamped copy goes **out of date**; an
     unstamped one goes **wrong**. The control is two-part and the parts do
     different jobs — **the stamp makes a stale copy READABLE, the tripwire
     makes it LOUD** — and only the second is a gate. That is *the fix is the
     stamp, not the refresh* (`docs/backlog/architecture.md`
     `2026-08-23-architecture-24`, F2) arriving at a copy instead of at a
     count.

  **This document's own transcriptions are gated**, which is why the ES half
  is quoted below as a marked block instead of paraphrased: `tools/docs_check.py`
  *is* the tripwire this law demands, pointed at `.md`. The landed
  `numberToString` routes through the bit model —

  ```lean
  -- LeanModels/Es/Convert.lean (excerpt — the LANDED numberToString, routed through the model)
      let t := n.toModel.toInt64
      if Float.ofModel (Float.Model.ofInt64 t) == n && n.abs < 1e15 then
        some (ToString.toString t) else none
  ```

  — and the `%` arm the same probe cited is **WITHDRAWN**, a fact no
  line-number citation could have carried:

  ```lean
  -- LeanModels/Es/Convert.lean (excerpt — the WITHDRAWN `%` arm)
          SemM.refuseConstruct "`%` needs a non-clamping truncation (SoftFloat's toInt_eq_truncate); refusing rather than clamping"
  ```

  **The general form, and it is the one to carry away: A TRANSCRIPTION MUST
  LIVE WHERE A GATE CAN REACH IT, OR BRING ITS OWN GATE.** A `.md` block has
  `docs_check`; a comment in a `.lean` has nothing, which is the whole of why
  this one rotted — and generalizes into §5.4b.

  **AND THE DURABLE FORM OF A CITATION IS A NAME, NOT AN OFFSET** (pyc lane,
  staged on its queued ticket). Line numbers rot on **every insertion above
  them**, by anyone, forever — so an audit row asking for the offsets to be
  corrected was **declined, correctly**:

  > **Fixing offsets buys ONE LANDING of accuracy. The durable fix is lemma
  > NAMES.**

  A name survives every edit that does not rename the thing, and a rename is
  loud. Which is also why the `%` row above had to be **re-stated** rather than
  re-numbered: `Convert.lean:303` was not merely stale, it pointed at a
  *different arm* — and *"the arm is WITHDRAWN"* is a fact no line number can
  carry, at any offset. **Cite by name**; cite the line only as a courtesy
  beside it;
* **ROWS AND WITNESSES ARE NAMED FOR THE CONSTRUCT, NEVER FOR THE
  VERDICT.**

  > **A name asserting a VERDICT has a shelf life. One asserting a
  > CONSTRUCT does not.**

  Measured: a row named `keys_for_is_still_loud` **expired the moment inch
  3a landed** — the construct stopped being loud, and **both instruments
  convicted the NAME** rather than the behaviour. Renamed
  `keys_for_live_cursor`, which names what the row *exercises* and is
  therefore still true after the tier grows. A verdict-named row is a
  small piece of prose embedded in an identifier, and it goes stale the
  way §9's prose does — except that nothing greps it, so it goes stale
  **silently** and then convicts the wrong thing.

  **AND ITS SPELLING HALF, which the naming rule does NOT secure** (pyc's
  3c-i-c; **ticketed — conditional on that landing**). A never-stepped-binding
  witness spelled `print(type(e).__name__)` would have **refused at `type`** —
  a builtin out of tier — and been **filed as evidence about `enumerate`.**

  > **A WITNESS MUST FAIL FOR THE REASON IT NAMES.**

  **Naming the row for its construct does not achieve that; the SPELLING has
  to be in tier too.** A row is a small program, and every token in it is a
  claim that the tier can run that token — so a witness written in the
  vocabulary a reader finds natural will report **the first thing the tier
  lacks**, which is rarely the thing the row is about.

  **The fix is the pattern to copy: MINIMAL SPELLING.** `print('bound')` —
  **reaching the `print` IS the observation.** Nothing in the row exercises
  anything except the binding under test, so there is no second construct to
  fail first.

  **And note how it was caught: by READING the builtin tables before the
  ticket, not by a red.** The failing version would have been **loud** — a
  refusal, not a wrong answer — and still wrong, because the refusal would have
  been **filed under the wrong subject.** *A loud failure attributed to the
  wrong cause is a silent one for every reader downstream*;
* a **`--compare`** mode against the committed JSON, because corpora that
  live in other repositories move on their own schedule and staleness must
  be mechanically detectable rather than merely possible;
* **and `--compare` REFUSES TO SUBTRACT DOCUMENTS THAT ANSWER DIFFERENT
  QUESTIONS** (Ada, `43926b0`). The envelope path **deliberately lacks
  `target_resolution` and SAYS SO in its own frontend field**, so a comparison
  across the two is refused rather than computed.

  > **A DIFF BETWEEN TWO CENSUSES IS ONLY A NUMBER IF BOTH ANSWERED THE SAME
  > QUESTION.**

  **The unit family, enforced at the comparison OPERATOR** rather than caught
  afterwards in a review: every earlier member of that family was a wrong unit
  discovered in a finished count, and **this is the first instrument that
  declines to produce the count at all.** Two documents with the same schema and
  different subjects **subtract cleanly and mean nothing** — which is exactly
  the shape a `--compare` mode is otherwise built to hide;
* **AND THE FAMILY REACHED A PROOF SOURCE, WHICH IS ITS FIRST NON-CORPUS
  INSTANCE** (Wasm's next-corner census, `0f44b74`, merged). The tier's ported
  material came from **a 13-lemma copy of an Isabelle development while the
  branch held 19** — *staleness in the thing being MIRRORED rather than in the
  thing being MEASURED.*

  > **RE-CENSUS EVERY BRANCH BEFORE PORTING. A proof source is a corpus, and it
  > moves on someone else's schedule.**

  **And the cost of not doing so is invisible in the usual place**: a stale
  corpus makes a number wrong and a reviewer can see the number, while **a stale
  proof source makes a PLAN wrong** — the lane prices a corner against lemmas
  that no longer bound it, and every downstream estimate inherits the error with
  nothing anomalous to notice. The census that fixed it also found **37 COMPLETE
  lemmas including `Subtyping_Theorem.thy` — the corner's own capstone.** *The
  lane had proved the properties underneath a theorem without knowing the
  theorem sat on top of them*, which is the absence family's most expensive
  shape: **not a wrong belief, an unopened file.**

  **AND THE PORTING RULE ITSELF HAS A NAMED FAILURE MODE, which is why the
  re-census is a standing rule rather than a one-off correction.**

  > **"ISABELLE-BEFORE-SCRATCH" SILENTLY DEGRADES TO "SCRATCH" when the
  > counterparts are incomplete.**

  A policy keyed to *a source's state* is only as good as the last time that
  state was checked — and this one degrades **into the default**, so **the lane
  keeps following the rule while receiving none of its benefit.** *A rule whose
  violation looks identical to its compliance has to be re-checked PER USE, not
  adopted once;* the general form is the one §5.4b keeps re-stating in other
  clothes: **a control that cannot fail loudly must be re-run, because nothing
  will tell you it stopped applying.**
* **every refusal path RUN, not admired** — a missing input, a zero-row
  parse (an empty census is an instrument fault, never a finding), and a
  rejected input. The third one was a real defect in the C instrument,
  found only by executing the fixture, and this charter's own instrument
  reproduced the lesson: its first answer was a plausible table produced
  by matching renumbered clauses (§2.1), and it was the spot-checks that
  caught it;
* **AN ENTRY POINT REFUSES UNKNOWN ARGUMENTS AT LINE ONE.** An instrument that
  **ignores** an unrecognized flag and proceeds to its default does not have a
  lenient interface; it has one that **converts every typo into its most
  expensive path**.

  > **Ignoring an unknown flag is how a self-test request became a full
  > build.**

  Measured (`docs/backlog/qol.md` `2026-08-23-qol-36`): `bash tools/ci.sh
  --self-test` — a request for the *cheapest* thing the tool does — ran the
  **entire CI**, because the flag was unknown and unknown meant *nothing*.
  `ci.sh` now takes **no arguments** and exits **2** before anything else runs;
  the guards sit at lines 31/51/58, **ahead of the first step at 129**, because
  a refusal that runs after the work has started is a report, not a refusal.

  **The allowlist is not the defect.** One flag (`--verify-guards`) is
  permitted and its handler cannot reach the CI body — that is fine, and it is
  worth saying because the obvious over-correction is *"never take a flag"*.
  The rule is about the **default on the unrecognized branch**: a tool's
  argument parser has exactly one safe fallthrough, and it is an error.

  This is §5.4's *every refusal path RUN, not admired* pushed one step earlier
  — **the argument parser is a refusal path**, and it is the first one every
  caller touches;
* **AN INSTRUMENT THAT SELECTS FILES BY CONTENT MUST EXCLUDE ITSELF BY
  IDENTITY, NEVER BY PATTERN — its own source re-matches the pattern by
  construction.** Measured in `tools/ci.sh` (`a9f7867`): a new step selected
  every tool carrying a `--self-test` with `grep -q -- '--self-test'`, and the
  **selector matched `ci.sh`** — the function doing the matching names the flag
  in its own text. CI **re-entered itself** and started an **UNTICKETED `lake`
  build** (§7.1 A9, A11). In the lane's words: ***"it hung, which is the only
  reason I looked."***

  > **Any content pattern you can select on, you will eventually WRITE DOWN in
  > the selecting file — so the file matches it. Only IDENTITY excludes.**

  **The proof is in the repair.** The selector was narrowed to match a
  *handler* rather than the flag — and the lane's own explanatory **comment**
  then contained the handler string, so the pattern re-matched and an explicit
  `ci.sh` exclusion had to back it. **The narrowing failed the same way twice,
  which is what makes this structural rather than a sloppy regex**: a
  description of the pattern lives in the file that applies it, always.

  **And note the detection channel, because it is the alarming part**: a
  self-selecting instrument fails by **recursion**, and recursion is silent
  until it is expensive. Nothing reported an error — the step **hung**. That is
  §5.4b's topology point arriving from the other side: the gate set had no
  pointer aimed at *"did this instrument select itself"*, so the only signal
  left was the clock;
* **`#guard` IS NOT A KERNEL ORACLE — it attests the RUNTIME.** It runs
  unsafe `evalExpr`, honours `@[extern]` / `@[implemented_by]` / `opaque`,
  and **passes identically whether a declaration reduces or has no body at
  all.** Measured here on the pinned toolchain, three propositions, all
  `#guard`-PASS and kernel-FAIL:

  ```
  -- (illustrative — probes, not tree files)
  #guard Nat.sqrt 49 == 7                  -- PASSES
  example : Nat.sqrt 49 = 7 := by rfl      -- FAILS: unsolved goals
  example : Nat.sqrt 49 = 7 := by decide   -- FAILS
  #guard (2.75 : Float).toInt64 == 2       -- PASSES
  example : (2.75:Float).toInt64 = 2 := by rfl     -- FAILS
  ```

  So **"run, not admired" via `#guard` is RUNTIME attestation** — a claim
  about the *compiled* semantics. For pure, extern-free code the **value**
  agrees with the kernel; but **KERNEL-REDUCIBILITY is certified only by
  `rfl` / `decide`** (or `#guard_expr` with `=~`). **Any claim of
  "kernel-reducible runs" resting on `#guard` alone is overstated**, and
  this document made one (§3.4, now corrected).

  **THE PAIR IS A DIFFERENTIAL, and that is the constructive half.**
  `#guard` attests the **C runtime**; `rfl`/`decide` attest **core's
  model**. A float-touching row therefore carries **both**, and
  **disagreement between them is a FINDING** — the two oracles have
  genuinely diverged, which is exactly the kind of fact a family of
  language models exists to surface rather than to average away.

  **Placement relative to the decide ladder (§0.1 II(a)): the ladder's
  rungs are KERNEL tactics. `#guard` is BENEATH the ladder, not on it.**
  It is not a cheaper rung-2; it is a different kind of evidence, and the
  receipts rule applies to it too — a row attested by `#guard` says so.

  **Re-attestation owed, cheaply**: the rebuild's *"9 `#guard`s decide real
  runs in the kernel"* (re-attest **one run per half with `decide`**); the
  **~50 ES `#guard`s** under `Examples/es`, FPU-attested today; and
  `harness/es/float_probe.lean`, which **mis-describes `#guard` as kernel
  evaluation** — the ES lane's fix.
* **EVERY PROBE THAT READS A CORPUS REFUSES WHEN THE CORPUS IS NOT THE
  RECORDED STATE — not only the revision probe.** Measured on ES: the
  census's `esmeta` field stored
  `{ignore_entries: null, ignore_file_present: false, workflows: []}`.
  That is not a measurement of the pin; it is **a measurement of an ABSENT
  REPO** — a bare fetched `spec.html` has no `.esmeta_ignore` and no
  `.github/workflows`. The truth at the pin is **11 ignore entries and 3 CI
  workflows.**

  **`rev()` had been hardened to refuse exactly this, and it did.
  `esmeta` was the quiet half that got through**, because nobody had
  hardened it:

  > **A `null`/`false`/`[]` measured on ABSENCE is the flattering
  > direction with the volume off.**

  A wrong revision is loud — it names another commit. An empty list is
  silent, and it **reads as a finding**: *"this pin has no ignore
  entries"* is a sentence a reader will believe. **Absence and zero are
  different, and most encodings conflate them**, so the refusal has to be
  in the probe rather than in the reader. Hardening one probe and not its
  siblings leaves the quiet ones as the whole remaining exposure;
* **A PIN BY REVISION IS A CLAIM ABOUT A SERVER'S HISTORY; A PIN BY CONTENT IS
  A CLAIM ABOUT THE BYTES** (C inch 6, merged `add6ad9`) — **and only the second
  survives the server.** The blob sha1 is **recomputed locally**, so the check
  **does not trust the transport.**

  > **A revision is a name somebody else can re-bind. A hash is the thing
  > itself.**

  **This is the generalization of the re-pinning rule below**, which said *the
  hash is the anchor; a tag or a date is a hint.* The sharper form is that a
  revision pin's failure mode is **not staleness but SUBSTITUTION** — the name
  still resolves, the fetch still succeeds, and **nothing in the pipeline
  notices** that the bytes changed. *Recomputing locally is what makes the pin a
  measurement rather than a citation;*
* **AND A SAMPLE RULE MUST NAME ITS POPULATION, NOT ONLY ITS ORDERING** (C inch
  6). Two tools **both saying "first 300 by name" differed by 24**, because
  `execute/` **has subdirectories.**

  > **Reproducible and still ambiguous is the WORST combination** — each tool
  > gives the same answer every time, and the two answers differ.

  **The sibling of the sort-order law** (§5.4b): that one says *a sample whose
  ORDER differs from its label's order is a different sample*; this says **the
  same of its POPULATION**, and the two together are the whole of what "first N"
  can hide. **Settled the only way that survives re-reading: by LISTING the 300
  with hashes** — *when a rule cannot be stated unambiguously, the extension is
  the statement;*
* **RE-PINNING IS RECOVERY, NOT DERIVATION: find the commit that
  REPRODUCES THE RECORDED HASH.** ES's `ecma262` pin was recovered by
  taking the annotated tag `es2026-errata` → `d89c03f2` and confirming its
  `spec.html` **sha256 is byte-identical to the census's recorded
  `spec_sha256`**. The hash is the anchor; a tag, a date or a changelog is
  a *hint* toward the commit, never the pin itself. **Reconstructing a pin
  from provenance metadata is a guess that looks like a citation** — the
  reproduction is what makes it a fact;
* **AND A PIN THAT DESCRIBES A GROWING ARTIFACT IS MAINTAINED IN THE LANDING
  THAT GROWS IT.** First routine application, recorded because routine is the
  point: the Wasm port's pin was **updated 5 → 9 declarations as the port
  grew** (queued; conditional on that landing). A coverage pin is a **claim
  with a shelf life** — it is true when written and quietly under-claims from
  the next inch onward — and the cheap form is to move it **in the same commit
  that moves the artifact**, which is the model-matches-code discipline applied
  to a number. **A pin updated later is a re-measurement; a pin updated with
  the work is bookkeeping**, and only the second is free.

  **This bullet is that rule's DURABLE HOME, and how it got here is the point.**
  It reached the tree as a **coordination instruction to one lane** — carrying
  no name, living only in dispatches. That is precisely the state §7.1a's
  register exists to end: **a rule that lives only in the message that carried
  it is one purge from gone, and every lane that never received the message
  never had it.** Confirmed with the coordinator rather than assumed;
* **double-run byte-identical**, verified;
* **every quoted number is paired with the STATE it was taken from**, per
  the provenance law below;
* it stamps the frontend FAMILY and the profile, because both are INPUTS
  to the result and not decoration;
* **not wired into CI when its corpus is out-of-tree** — a gate that is a
  permanent SKIP is a check pretending. `maybe` is where it belongs once
  the corpus is in-tree.

#### 5.4a THE PROVENANCE LAW — a measurement is only as good as the state it was taken from

Three lanes hit this independently, in three different disguises, which is
why it is stated once rather than three times:

| instance | the trap | found by |
| --- | --- | --- |
| **`#print axioms` on a failed declaration** | a statement-elaboration error prints *"does not depend on any axioms"* — **cleaner than the truth** — even when the proof is `sorry` (§0.1 II(a)) | rebuild lane |
| **a timing measured on a twin** | 568 ms against the shallow twin; the faithful interpreter does not close at ~14 minutes (§3.4) | rebuild lane |
| **a red from a torn tree** | a rebase under a running build yields `Unknown constant` against a healthy master (§7.2) | Go lane |
| **a `#guard` batch quoted as KERNEL evidence** | `#guard` attests the runtime and passes where the kernel cannot reduce at all (§5.4) — so a batch cited for kernel-reducibility is quoting the wrong oracle | SoftFloat lane |
| **an INSTRUMENT'S OWN RUNTIME** | `laws.sh` measured 54 s, 1m23, 1m55, then past two minutes on the same input — it was **spawn-bound**, so its cost was a reading of *other lanes' builds* | QoL lane |

**AND THE SAME LAW APPLIES TO FINDINGS, measured: the VERIFIER LAYER
EARNED ITS COST.** The first full audit ran every candidate finding
through a re-read before publishing, and the re-read was not a formality:
**8 of 64 were REFUTED**, and **many of the confirmed were confirmed WITH
CORRECTIONS** — **severities moved in both directions** and
**consequences were replaced outright.**

> **A finding un-re-read is a claim, not a finding.**

Both halves matter. Publishing the 8 would have sent lanes to fix
non-defects; publishing the corrected ones uncorrected would have sent
them to fix real defects **for the wrong reason**, which is worse because
it survives the fix. And the severities moving **both** ways is the tell
that the verifier was doing work rather than rubber-stamping — a layer
that only ever downgrades is a filter, not a check.

**AND THE AUDIT-RESPONSE NORM, from the SV lane's dispositions**, which
closes an incentive loophole this audit creates by existing. **An audit
that demands provenance applies pressure to MANUFACTURE provenance** —
a dangling citation is embarrassing, and a plausible reconstructed table
makes the embarrassment go away. SV had two citations resolving to
nothing and the backing Xcelium host unreachable. They corrected the
citations to **unreproducible-pending-access** rather than rebuilding the
table:

> **Fabricating rows to satisfy a provenance audit would be that audit's
> own defect, one level up. A dangling pointer replaced by an honest
> 'lost, and here is what would restore it' is a real fix; a fabricated
> table is not.**

> **The remedy for a provenance gap is PROVENANCE, never
> RECONSTRUCTION.**

The reconstructed table is strictly worse than the dangling pointer it
replaces, and the audit is what makes it so: **a dangling pointer
announces its own failure**, while a fabricated one **passes every future
check** and is indistinguishable from a measurement until someone tries to
act on it. An honest *lost, and here is what would restore it* keeps the
gap **visible and closeable** — it names the access that would reopen it.
Closing a finding is not the goal; **the finding is closed when the claim
is true**, and *"we cannot currently reproduce this"* is a true claim.

> **A NUMBER CARRIES THE STATE IT WAS MEASURED IN. Quote both, or quote
> neither.**

**AND THE SAME DISCIPLINE FOR A PARTIAL THEOREM CLAIM — the standard, from Go's
closed loop (`cd14591`).** The landing's claim is one sentence and it does two
different things:

> **The LOOP is correct, PROVED. The FUNCTION is correct, CHECKED** — on 35
> inputs against two independent standards.

Proved: the arithmetic bracketed both ways, the bridge lemma (the interpreter's
`>>= 1` **is** the spec's `/2`), one turn, and the loop. Checked: the
prologue/epilogue composing the loop theorem up to `callFunction`. **Neither
half is hedged and neither is inflated**, and the reason that was achievable is
the part worth copying:

> **WRITE THE PROVED/CHECKED BOUNDARY BEFORE YOU CAN CLOSE EITHER HALF. A
> boundary drawn after a proof lands is drawn BY the proof.**

The distinction was written into the file at **§G6**, when *both* halves were
open; closing one of them **did not move the other half's words.** A boundary
written afterwards is written by an author who now knows which side won, and it
drifts in one direction only — the proved side quietly annexes whatever sits
next to it, because at that moment the annexation feels like precision.

**AND THE COMPANION RULE FOR WHEN THE PROOF FINALLY LANDS: ONLY THE ROWS IT
SUBSUMES BECOME CORROBORATION.** Measured on the same exemplar (`4bda5af`).
With `bitLen_correct` proved, the **35 SPEC rows are demoted** — they are
instances of `bitLen_eq_spec` now. The **35 ORACLE rows are NOT**, and the
reason is one sentence:

> **`bitLen_correct` proves the model computes `bitLenSpec`; it cannot prove
> `gc` does.**

> **A PROOF DEMOTES THE ROWS ABOUT THE RELATION IT PROVED, AND NO OTHERS.**

The oracle rows stay at full weight because they are **the only thing tying the
model to what the compiled function actually printed**. A theorem about the
model is **silent about the world**, however strong it is about the model.

**The trap is that a landed theorem creates pressure to retire the tests it
"covers", and the covering feels total** — the theorem quantifies over all
`v < 2⁶⁴` where the rows are 35 points. But **strength along one relation is not
coverage of another**, and the two row sets are indistinguishable in the table:
same inputs, same expected values. **Only their ADJUDICATOR differs**, and the
adjudicator is exactly what a row's data does not show.

So the demotion decision is made by asking **which relation each row
adjudicates** — never by comparing values, and never by counting. That is *the
adjudicator is the ORACLE, never the TABLE* (below) in its second direction:
**when a window's adjudicator retires, its rows must be re-anchored; when a
THEOREM arrives, only the rows whose adjudicator it replaces may be demoted.**

**This is §0.1 II(a)'s receipts rule at the granularity of a CLAIM rather than a
tactic**: a theorem statement carries how it was established, and *"checked on
35 inputs against two independent standards"* is a strictly better sentence than
either *"correct"* or an apologetic silence. **A checked half is a result; it is
only a weakness when it is described in the vocabulary of the proved half.**

**A FOURTH INSTANCE, and it is the one that flatters hardest: the SEARCH
that agrees with you.** A name collision made a `grep` confirm a prior —
`DRAIN` in `VCGen.lean` is the *generator drain*, 47 occurrences, and not
the short-circuit `DRAIN` trick the searcher was looking for. The hits were
real, numerous, and about something else.

> **A grep that agrees with your prior is the one to re-run.**

**AND THE INGESTION-REWRITE AVAILABILITY RULE, STATED FROM A ZERO** (pyc inch
2, branch `pyc-del` @ `485e7a3`, ticketed and pending green).

> **An INGESTION REWRITE is available exactly when the construct's meaning is
> decided by SYNTAX.**

Measured: `iter(d)` extracts as **a plain `Call` with ZERO extractor sites**, so
the previous inch's shape — fuse at ingestion, on the `ListComp` precedent —
**does not transfer.** *The envelope proves the negative*: there is no syntactic
site to rewrite, because the construct is a call like any other and its meaning
is decided by **what it is called on**.

**A rule stated from a zero is worth more than the same rule stated from a
success**, and this is the second time this register has said so (§9.0b's `+0`).
A rewrite that *worked* tells you it was available **here**; a census returning
**zero sites** tells you **what property made it available there** — and the
property is the transferable part. **The previous inch's shape was never about
`ListComp`; it was about syntax deciding meaning**, which nobody could have
known while it kept working.

**AND THE CHURN REGIME IS TWO CPYTHON RULES, NOT ONE — a SAMPLING-POSITION
hazard.** The for-loop census **sampled one rule from one cursor position**, and
the refusal the lane wrote is honest to **both**.

> **A census that samples from ONE POSITION measures the rule that position is
> subject to, not the construct's rule.**

**This is the unit family with the sampling frame as the unit.** Every earlier
member had a wrong *unit of counting*; this one has a **correct unit counted
from a privileged vantage** — and the number is right about what it saw. **The
tell is a census whose sites are all structurally alike**, which reads as a
clean population and is a sampling artifact.

**AND A CROSS-LANE INSTRUMENT FIRING ON ANOTHER LANE'S CODE IS THE INSTRUMENT
WORKING — the temptation is to narrow it** (SoftFloat). The census caught **7
float sites in ES's new `Ordinary.lean` within one rebase of their appearing**,
and the lane **MEASURED rather than assumed**: `Nat.toFloat` is an **abbrev over
`Float.ofNat` and REDUCES** — `rfl` closes it — **so ES crosses nothing.**

> **The alternative reading — *"my gate is noisy about other lanes' code"* —
> invites narrowing it to own-lane files, and that narrowing would have hidden a
> REAL crossing had those sites been `Int64.toFloat`.**

**Recorded because the narrowing is the natural response and it is
unrecoverable**: a filter scoped to *my files* removes an entire class of
finding **without ever reporting that it did.** The rows would simply stop
arriving, and **nothing distinguishes "the other lanes are clean" from "I stopped
looking."**

**The discipline that made the noise tolerable is the same one §5.4a already
prescribes**: the hits were **candidates, resolved by reading**, and the reading
produced a *reduction proof* rather than an opinion. **A cross-lane instrument
is affordable exactly when its hits are cheap to adjudicate** — so the answer to
a noisy cross-lane gate is a **better adjudication path**, never a narrower
scope.

**AND THE GATE'S OWN SPEC WAS REFUTED BY RUNNING IT — my *"token in a
declaration slot"* generalization ACCUSED 60+ KNOWN-GREEN SITES** (analog's
fourth-attempt green, merged). Docstrings **legally precede fields,
constructors, `#guard_msgs`.**

> **A WHITELIST of what a docstring MAY precede is a claim about LEAN'S
> GRAMMAR. A BLACKLIST of what it may NEVER precede is a claim about a few
> commands. Only the second is checkable without a parser.**

**That is the generalization's real cost, and it is mine**: the whitelist form
is **shorter to state and unboundedly larger to defend** — every legal position
in the grammar is a case it must know, and the grammar is not a thing a gate
has. **A blacklist is bounded by the incidents that produced it**, which is
exactly the register's own standard for minting a law: *the cases you have
measured, not the cases you can imagine.*

**AND PARSE VALIDATION WITHOUT A TENURE — a proxy that is honest about being
one.** Nesting-depth count, plus a gate, plus a **PRECEDENT CHECK**: every
doc-comment follower in touched files must be **∈ the 169 distinct followers in
green master.**

> **MEMBERSHIP IN THE GREEN CORPUS AS A PARSER PROXY — cheap, sound for its
> purpose, and stated as WEAKER than parsing.**

**The third clause is what makes it admissible.** A proxy sold as equivalent is
a lie; **a proxy sold as a proxy is an instrument with a stated scope** — it
cannot admit a construct the tree has never seen, which is a real limitation and
**exactly the right one for a gate whose job is to catch a regression rather than
to bless novelty.** *Every new legal follower is a deliberate widening someone
must add — which is a feature in a guard against an accident.*

**AND THE OTHER HALF OF THAT RULE ARRIVED FROM THE ANALOG LANE, so the two must
be read together: FALSE positives on another lane are a different thing
entirely** (verify at its landing). A gate's **own first draft accused Go and SV
lines where `/--` sat inside STRING LITERALS** — and

> **the two tiers most likely to trip this check are the two whose LANGUAGES
> CONTAIN THE TOKEN.**

> **A gate whose FALSE POSITIVES land on other lanes is worse than no gate — it
> spends someone else's attention.**

**AND THE COMPLEMENT OF *FIXES LIVE IN GATES*: THE FIX LIVES WITH THE GATE'S
OWNER** (C lane; **nothing pushed, by its own rule**). The lane **measured a
shared gate wrong**, found itself blocked, **filed the INBOUND to the gate's
owner — and did not touch the gate.**

> **"MY LANE IS BLOCKED" IS THE WORST REASON TO MOVE A SHARED SAFETY LINE.**

**AND THE FAMILY'S THIRD MEMBER, FROM THE OBEYING SIDE — DECLINING AN OPEN
DOOR** (R-track, `4ed731e`). `--iterate` **refused on genuine pressure**, and
**plain scratch mode WOULD have run.** The lane did not take it.

> **When a guard refuses, the question is whether the GUARD IS WRONG — not
> whether ANOTHER DOOR IS OPEN.**

> **Picking the mode that skips the check is GAMING a courtesy protocol rather
> than OBSERVING it.**

**The three members now cover the whole decision**: *read the mechanism* (§7.2)
tells you **whether the guard is wrong**; *the fix lives with the gate's owner*
tells you **who repairs it if it is**; and this tells you **what to do while it
is right** — which is the case that arises most often and has the least
guidance, because a correct guard blocking correct work feels like a defect from
inside.

**And the compliant shape is named rather than left to taste**: a **retry loop
with a loud 40-minute giveup.** *A protocol that depends on voluntary compliance
needs its obedient form to be as specific as its violation* — otherwise the lane
that wants to comply has to invent one, and the cheapest invention is the open
door.



**It is the worst reason because it is the most persuasive one available in the
moment**, and it is **always** available: the lane is stopped, the line is the
thing stopping it, and the edit is one character. **The reasons that should move
a safety line — a measurement showing it wrong, an owner agreeing — are exactly
the ones a blocked lane has no time to gather.**

**Note the shape it shares with the instrument-artifact ruling above**: there,
the cheap repair was to loosen the line rather than fix the reading; here, the
cheap repair is to loosen the line rather than file the finding. **Both times
the line was innocent**, and both times **the lane that stopped short produced a
better artifact than the lane that would have edited.**



**The discriminator between the two rules is TRUE versus FALSE, and it decides
who pays:**

| the hits | who can settle them | verdict |
| --- | --- | --- |
| **TRUE positives on another lane** (SoftFloat's 7 float sites) | the finding is real; adjudication is **cheap and conclusive** | **the instrument working** — fix adjudication, never scope |
| **FALSE positives on another lane** (`/--` inside a string) | the accused lane **cannot fix what is not broken** | **worse than no gate** — the cost is levied on someone with no remedy |

**The asymmetry is that a false positive on your OWN lane costs you a
re-read, and one on another lane costs THEM a re-read plus the doubt.** A lane
that receives a wrong accusation has to disprove it, and **disproving is
strictly more expensive than the check that should have prevented it.**

**Which is why this gate was born with its false-positive control from the first
draft** — the accused cases became the control fixtures. *A cross-lane gate ships
with the cases it must NOT fire on, or it is an unfunded claim on other lanes'
time.*

**AND A REFUSAL'S REMEDY IS PART OF THE REFUSAL, WHICH THIS FAMILY HAD NOT SAID**
(QoL item 15). The guard printed a fix; **the fix did not work.**

> **A REFUSAL NAMING A FIX THAT DOESN'T WORK IS WORSE THAN NO REFUSAL.**

**The cost lands exactly where the table above says it does** — on someone with
no remedy — **except that here the lane has been told it HAS one**, so the
expensive part is not the block but **the time spent trusting the instruction.**
*A wrong accusation is disproved by reading the code; a wrong remedy is disproved
by running it, which costs a tenure.*

> **EXECUTE THE REMEDY BEFORE SHIPPING THE REFUSAL. A printed fix is a claim, and
> the gate that prints it is the natural place to test it.**

**This is *a check that exists and isn't run* pointed at the message rather than
the check** — and it is cheaper to satisfy than it looks: the remedy is a command
the author already ran while developing. *What is missing is not effort; it is
the habit of treating the error string as an artifact that can be wrong.*



**AND A CONCESSIVE-PROSE GREP FINDS PROVED THEOREMS AS READILY AS OPEN ONES**
(analog census). `Spice/DramDifferentialSenseUnbalanced.lean:1899` reads as an
open obligation — *"admit a uniform positive regeneration-rate certificate"* —
and is a **docstring on a theorem that is proved two lines below.**

> **PROSE THAT SOUNDS LIKE AN OBLIGATION IS AS COMMON IN A DOCSTRING AS IN A
> TODO.** Any *"open obligations"* census that greps for hedging language is
> counting a **register of English**, not a state of the tree.

The instrument-design corollary: **an open-obligation census reads the
DECLARATION, not the commentary** — `sorry`, `axiom`, `partial`, an admitted
constant — because those are states the elaborator knows about. **Concessive
prose is a writing style**, and the tiers that write the most careful docstrings
will score worst on it, which is the ranking exactly inverted.

This document supplied its own instance: `grep -rl '\bRun\b'` returned
three SystemVerilog files and **confirmed the expectation that `Run` was
shared substrate** — the hits were the English word opening a docstring,
and the true count was zero (§3.1). Both searches were *correct*; both
answered a question narrower than the one being asked; and in both cases
**agreement is what stopped the search.** A disagreeing grep gets
investigated. That asymmetry is the provenance law again, pointed at
retrieval rather than at measurement.

**AND ITS CONSTRUCTIVE HALF, minted on a third hit and corroborated the
same day.** The rule above says *re-run the search*; this one says **what
to count**:

> **A COUNT THAT PRICES A DECISION MUST COME FROM THE PATTERN POSITION,
> NEVER FROM THE IDENTIFIER.**

An identifier count answers *"how often is this name written?"* — which
includes mentions, docstrings, other lemmas' statements and the doc you are
reading. A decision is priced by *"how many places must change?"*, and
those are **pattern positions**: match arms, clause slots, the actual
branch points. Four instances, three of which moved or nearly moved a
plan:

| instance | what went wrong | direction |
| --- | --- | --- |
| §L49's `\.usub` grep | missed every `cases op with \| usub =>` arm **by one character** — the leading dot | **UNDER**-counted |
| §L53's walker price | landed at **19** because **catch-all arms were load-bearing**: the arm count was not the case count | **UNDER**-counted |
| today's VCGen price | **26 lemma NAMES** priced a **9-arm** change at **35**, and nearly moved a date | **OVER**-counted |
| the rebuild's `DRAIN` | generator drain vs the short-circuit trick — a name collision confirming a prior | over-counted, and *agreed* |
| `substrate.sh`'s `REF_LOCAL` | `\| unsupported` **match arms inside proofs** counted as **declarations**: Python **82 → 4** | **OVER**-counted ~20×, and **published** |

**The two directions are both live, which is why the rule names the
POSITION rather than saying "count carefully."** Identifiers over-count
because names appear where no work happens. Pattern searches under-count
when the syntax differs by a character, and **catch-all arms defeat arm
counting entirely** — a single `| _ =>` can absorb a dozen cases, so even a
correct arm count can be the wrong price.

The practical form: **price a change by enumerating the positions the
change must visit, and check that enumeration against the thing that
dispatches** — the `match`, the clause list, the table — not against the
name index.

**AND THE LAW REACHES THE INSTRUMENT'S OWN COST, which is the one number a
lane never thinks to distrust (`7a4876f`).** `tools/laws.sh` was timed at
**54 s, then 1m23, then 1m55, then past two minutes** on an input that had
barely changed. It was **spawn-bound** — roughly **8 000 process spawns**, four
to six per law — and spawn latency scales with machine load, so:

> **The instrument's cost was a measurement of somebody else's work.**

The provenance law pointed at the tool that audits the tools. Two things in the
response are worth copying more than the fix.

**It was PROFILED FIRST, and the profile refuted the author's guess.** The
suspicion was a pathological subset of laws; three slices (rows 1-30, 150-179,
300-329) came back **uniform at ~1.15 s**, and the same per-law work over a
pre-read file took **13 s** against the real script's minutes. *No subset was
pathological; the spawns were.* A fix aimed at the guess would have optimized a
part that was already fast — §5.4a's flattering direction wearing performance
clothes.

**And the optimization was accepted on OUTPUT EQUALITY, not on the clock:**
**231 cited / 118 NO GATE / 1 ungateable, byte-identical before and after**,
with the runtime falling to 62 s.

> **An instrument optimization is proved by OUTPUT EQUALITY, never by speed. An
> optimization that changes a count has changed the instrument, not its cost.**

**THE SHARPEST PART IS THE BOUNDARY THAT SURVIVED, because the faster algorithm
was also the SIMPLER one.** Counting with `index()` would have been faster
still — and would have **dropped the whole-token rule**, which is *exactly how
`§9` came to match `§9.5`* and mis-credited a law to seven tools (§9.7). The
awk escapes and anchors each token instead, and **a self-test row pins the
distinction**: `§9` counts **0** against a ledger that says `§9.5` twice, while
`§9.5` counts **2**.

> **The optimization that is also a SIMPLIFICATION is the dangerous one: it
> deletes a distinction the previous version was paying for. Pin the
> distinction in a self-test row before you take the speed.**

A comment saying *"careful, whole tokens"* would not have survived the next
rewrite; a row that fails does.

**AND THE CONSTRUCTIVE HALF, from the fuelMono lane** (**LANDED**, `6b91a8d`;
this paragraph carried a conditional stamp until then, and the discharge is
recorded rather than quietly deleted). The instance above diagnoses the
disease — an instrument's runtime
is partly a reading of the machine. This one prescribes the **unit**:

> **HEARTBEATS ARE A DETERMINISTIC STEP COUNT; WALL TIME IS NOT. On a shared
> box, report the deterministic half and SAY WHY the other half was dropped.**

Measured on the `+jp` question: **both arms time out at 1M heartbeats against
the REAL tree** — a number that does not move when another lane starts a build.
It **replaces the spike's `VOID` headline**, and the method decision (judgments,
not `mvcgen`) now rests on a **tree-level** number instead of a spike's.

**Dropping wall time is not the same as hiding it.** An unexplained omission is
what makes the surviving number ambiguous — a reader cannot tell a dropped
measurement from one that was never taken — so the report **names the drop and
its reason**. That is the state-stamp rule (MEAS-10) applied to what is *absent*
rather than to what is quoted.

**RIDER — A PROBE CANNOT CERTIFY ITS OWN DEFINITIONS.** A probe that **errors**
prints `sorryAx`, so its axiom line describes the error recovery and not the
tree.

> **The certification comes from the TREE's green build ledger, never from the
> probe's own axiom print.**

MEAS-11 restated with the artifact named — the same move as §7.1a's
one-second-build rule: *name the artifact whose existence success would have
produced*, rather than reading success off the absence of complaint.

**AND THE DIAGNOSIS HALF, measured THREE TIMES IN ONE RUNG: A PERFORMANCE
SYMPTOM IS A MODELLING QUESTION** (Go rung 4, `a991f22`). §8's line —
*raising heartbeats trades a WRONG answer for a SLOW one* — says what **not**
to do with a timeout. This says where to look instead, and the evidence is that
**each time, the faithful shape was also the cheap one**:

* **Strings.** Once a Go string was bytes, every run-time panic forced
  `String.toUTF8` through the kernel and **four guards timed out**. Chasing the
  cost surfaced a **faithfulness bug**: Go's run-time panics carry a
  `runtime.Error`, **not a string**. `GoVal` gained `runtimeErrorV` — the
  faithful shape and the cheap one.
* **Conversions.** A conversion had landed as a **branch inside `evalExpr`'s
  `.call` arm**: measured **0 timeouts without it and 4 with it**, and moving it
  to the `none` path recovered nothing. **The fix was the DESIGN, not the
  budget** — a conversion **is a different construct** that Go's grammar merely
  *spells* like a call, so it became `Expr.convert`, emitted by the frontend
  from the predeclared-name list. **No heartbeat bump was needed.**

> **A PERFORMANCE SYMPTOM IS A MODELLING QUESTION. When the faithful shape
> keeps turning out to be the cheap one, the cost was reporting a conflation,
> not a budget.**

**The mechanism is worth stating, because it is not luck.** A model that
conflates two things must **decide between them at run time**, in the
interpreter, on every visit — and a kernel pays for that decision every time it
reduces the term. **Un-conflating moves the decision to the frontend, where it
happens once.** So a cost spike is evidence about **where a distinction lives**,
and *"the interpreter is doing work that a compiler-side split would have done
once"* is a hypothesis a lane can check directly.

**This is also the frontend un-conflating what `go/ast` conflates** — the same
boundary as the parser-unit law above, seen from the other side: the AST merges
`[N]T` with `[]T`, and it merges a conversion with a call. **The census reads
those merges as a measurement hazard; the interpreter feels them as a cost.**
Both are the same fact, and the ruling for the second is already written in
that lane's charter: **anything type-dependent is decided by the frontend.**

**AND A DIAGNOSTIC THAT KEEPS TWO ADJACENT-LOOKING BLOCKERS APART: IS THE
BLOCKER IN THE VALUE, OR IN THE REFERENCE?** (Go, `4618380`.) The `strings`
package did **not** start paying after the value model was fixed, and the reason
is exact: `strings.Index(…)` is a **SELECTOR call** — measured at **52.4% of
call sites** and ruled `go/types` work.

> **§G15 changed what a string IS; it did not change what `pkg.F` MEANS.**

**The two look adjacent and are unrelated.** One is a **value model** — how the
tier represents a datum — and the other is **name resolution** — how a
reference is resolved to the thing it names. They fail in the same place, on the
same line of source, and a lane that has just fixed the first will reach for it
again when the second bites.

> **Before pricing a blocker, decide whether it lives in the VALUE or in the
> REFERENCE. They have different owners and different work.**

Here the value model was **this lane's to fix**; the selector resolution is
**the extractor's**. That is §5.2's mis-scheduling law in a second dimension:
the refusal *class* says which lane owes a construct, and this says which lane
owes a **blocker** — and both are wrong in the same way when a plausible
adjacency is allowed to stand in for a measurement.

**A FIFTH INSTANCE, AND IT CARRIES A DIRECTION THE OTHERS DO NOT: THE COUNT
HAD BEEN PUBLISHED.** `tools/substrate.sh`'s `REF_LOCAL` matched any line
beginning `| unsupported` — **including `match` arms inside proofs** — and
reported them as *locally-declared constructors*. Corrected by tracking the
inductive block: **Python 82 → 4**, **Sv 17 → 11**, **C 2/6 → 1/7**, and
`REF_CORE` **6 → 5** (`12386db`; the audit row is
`docs/quality-audit-2026-08-23.md` `tools/substrate.sh:143`, HIGH).

**The position was the right KIND and the wrong SCOPE**, and that is the
sharpening this instance adds: a constructor and a match arm are **the same
characters**, so "count the pattern position" is not yet enough.

> **A pattern position is a position IN A DECLARATION, never a shape in a
> file. The same characters in a different scope are a different fact.**

**And then the part that is genuinely new: the gate had already PUBLISHED its
number.** The wrong figure sits in a dated ledger entry —
`docs/backlog/qol.md` `2026-08-23-qol-21`'s live table, *"6/82"* — and
**fixing the instrument does not fix that.** The tool corrects the next run;
the record keeps the number, and every reader of the record keeps copying it.

> **A number a gate PUBLISHED is a SECOND ARTIFACT. Correcting the instrument
> corrects the next run; the published figure is corrected where it was
> published, or it stands.**

That is *the fix is the stamp, not the refresh* (`docs/backlog/architecture.md`
`2026-08-23-architecture-24`, F2) extended from a hand-written number to a
tool's output, and the correction is made under §5.4b's annotation norm:
**annotate the published row with the re-measured number and the sha that
re-measured it**, never silently refresh it. The QoL lane published the
correction **against itself** — *"the correction is large and it is mine to
own"* — which is the honest half and the reason this is a norm rather than a
reprimand. The residue is `qol-21`'s own table, still reading `6/82`, filed
back to that lane as INBOUND (§9.5a).

**A FIFTH WRONG UNIT, AND IT IS THE FIRST ONE IN A PRICE FOR WORK NOT YET
DONE** (pyc successor's 3c-i-c census, branch `pyc-3cib2` at `0014d6d`;
**re-gate queued**). `for k in d` and `for i, k in enumerate(d)` **look like one
construct and are two.** The predicted cost — a `Kont`-record maintenance charge
under the fuelMono rule — **never fires**, because `enumerate` is a **`GenFrame`,
not a loop cursor**. The census **refuted the prediction outright: "the paying
case" was free.**

> **A PREDICTED MAINTENANCE COST INHERITS THE UNIT ERROR OF THE CONSTRUCT IT
> WAS PREDICTED FOR.**

**AND A REPRICING IS A MEASUREMENT AND OWES A CENSUS EXACTLY LIKE THE FIRST
PRICING DID** (analog A11, ticketed). Its own **8-of-11 repricing corrected to
3** by censusing the other decks — and the error ran **both ways at once**:

> **Wrong in the FLATTERING direction for the lemma and the PESSIMISTIC
> direction for the tier — both halves, which is what extrapolation from ONE
> instance produces.**

**That is the sharpest statement of the extrapolation hazard this register
has.** A single instance does not bias a estimate in one direction; **it
replaces the population with itself**, so every quantity derived from it moves
in whichever direction that one case happens to sit. *A repricing feels like
diligence — it is a second look — and it inherits the first pricing's exemption
from measurement unless someone says otherwise.*

**And the remaining sites split BY THE SHAPE OF THE WORLD, not by the
certificate** — a blocked-on taxonomy **keyed to the hypothesis's quantifier
domain.** *What blocks a site is a property of what must be true for it, not of
what one wanted to prove about it.*

**AND AN INFERENCE-BUILT CONSUMER TABLE OVER-PRICES THE COMPONENT** (SoftFloat).
**Four SV cells retired** that were **the lane's own inference from R1-exit, not
SV's request.**

> **A consumer table built from INFERENCE prices a component against demand
> nobody expressed.**

**The lift-pricing law's mirror.** There a lane under-priced by counting **its
own call sites** instead of the definition's surface; here a lane **over-priced
by inventing consumers** on another tier's behalf. *Both errors come from
answering a question about someone else's needs without asking them* — and the
correction in both directions is the same: **the population is not yours to
infer.**

**AND A PROBE THAT RETURNS "THIS VOCABULARY DOES NOT APPLY" HAS DONE ITS JOB**
(analog A11). `exists_isMinOn` gives a minimiser that **cannot be evaluated**;
the rate is **one quotient, one `div_le_div₀`.**

> **The probe-pays law does not require the probe to FIND something.**

**A negative probe result is a measurement of the SEARCH SPACE**, and it is the
cheapest kind to bank: the alternative to a probe returning *not applicable* is
**a lane discovering the same thing halfway through building on it.** *An
instrument that reports "the tool you were reaching for is the wrong tool" has
saved exactly the work it cost to run.*

**AND A THIRD, WHERE THE PREDICTION WAS EXACTLY RIGHT ON THE HALF THE LANE
OWNED** (C's seam lift, merged). `c-12` priced **5 theorems / ~40 lines**;
reality was **12 / 183.** But **the seam half was EXACT** — the entire gap is
**primitive rows the C tier had never used.**

> **A LIFT IS PRICED FROM THE LIFTING TIER'S USE OF THE THING, AND THE THING
> BELONGS TO THE FAMILY.**

> **Price a lift against the DEFINITION's surface, not your own CALL SITES.**

**What makes this instance instructive is that the lane's estimate was not
sloppy — it was ACCURATE about everything it could see.** A lane prices what it
touches, and a lift's cost is set by **what the definition offers**, most of
which the lifting tier has never called. **The error is invisible from inside
the lane's own usage**, and no amount of care about one's own call sites reaches
it.

**Same family as the predicted-maintenance-cost row**: a cost estimate is wrong
**whenever its population is the wrong one**, however right the per-item figure
is. Here the per-item figure was **right** and the population was **the lane's
call sites instead of the definition's surface** — *a residue priced without its
population* (§9.0), arriving in an estimate rather than in a count.

**AND ITS SECOND INSTANCE NAMES THE UNIT FOR A WHOLE CLASS OF ESTIMATE**
(R-track chain document). Rung 6's cost was priced at **221** and is **57**,
because the population was taken as *every statement in the affected files*
(**558**) rather than the ones a re-founding actually touches (**200 across
three files**).

> **A RE-FOUNDING'S SIZE IS THE COUNT OF STATEMENTS THAT NAME THE INTERPRETER.**

**That is SV's honest-denominator law pointed at COST rather than at COVERAGE**,
and the two are the same defect wearing different clothes: a denominator that
includes rows which could not have disagreed, and a cost estimate that includes
statements which could not have been affected. **Both inflate while looking
conservative** — and "conservative" is the word that stops the re-measurement,
because an over-estimate feels like the safe error to make. **It is not: a 4×
over-estimate kills the work outright**, which is exactly what it nearly did
here, and a killed inch produces no correction because nobody measures what was
never attempted.

**The other members of this family mis-count things that EXIST; this one
mis-prices work that does not exist yet**, which is worse in one specific way:
**there is nothing to re-measure.** A wrong identifier count can be re-run
against the tree the moment someone doubts it. A wrong cost prediction is
checkable only by **doing the work** — or by censusing the construct it names,
which is the cheap half and the one that was skipped.

A cost prediction has the form *"each X costs Y"*, and it is wrong **whenever X
is the wrong unit, however right Y is for real X's.** So the check is not
*"is the estimate reasonable?"* but **"is the thing being estimated one
construct or several?"** — census-first (§9.0a), pointed at a price rather than
at a lemma.

**Recorded with its provenance, because the direction matters: the refuted
prediction was the COORDINATOR'S.** A prediction made in the open and killed by
a census is the cadence working — §9's *a census that could have overturned the
plan* is evidence when it does **not** overturn, and it is a **result** when it
does. **The failure mode this avoids is not a wrong estimate; it is an estimate
nobody could have checked**, which is what an unpublished one always is.

**A FOURTH WRONG UNIT, AND IT WAS HANDED TO THE LANE BY THE PARSER: AN
UPSTREAM REPRESENTATION'S UNIT IS NOT YOUR UNIT** (Go, `69ea58a`). `[N]T` and
`[]T` — **fixed array and slice** — are **one `go/ast` kind**, separated only by
whether a `Len` field is present. So a census counting AST kinds reported
**`ArrayType` at 48.0%**, a figure that **summed two semantic objects**. Split
properly: **slices 46 188 (85.4%), fixed arrays 7 923 (14.6%) — slices outnumber
fixed 6 : 1.**

> **The files-vs-sites family INSIDE THE AST: an upstream representation's unit
> is not your unit.**

**And the direction is what makes it worth a paragraph.** The sizing question
was whether the tier could **skip slice semantics** because the tables it needed
are fixed-size — the working assumption ran **the opposite way** from the
measurement, and the conflated number could not have corrected it, because
**both objects were inside the one figure that looked like an answer.** When the
rung comes, **slices are the weight, not the tail.**

**AND THE RULING THAT KEPT THE SAME CENSUS FROM MINTING A SECOND TRUTH — ruling
(c) on the never-stepped `enumerate` object.** A construct can be **admitted**
without being **stepped**, and the temptation at that boundary is for the model
to decide what the opening *should* mean. It does not:

> **An OPENING is WITNESSED with the oracle's expectation — never turned into a
> second decision site.**

Two decision sites about one behaviour is the shape every law in this section
exists to prevent: the interpreter decides, and then a table decides again,
and **nothing fails when they diverge** (§5.2's *one execution, two
projections*; §5.3's *the oracle writes its own column*). Admitting a construct
whose semantics the tier has not built is legitimate — **claiming to know what
it does is not**, and the difference is exactly whether the row's expectation
came from the oracle or from the lane.

The general form, and it is cheap to apply: **a parser's kinds are a
convenience of the parser.** Before pricing anything by them, ask **which
distinctions the upstream representation declined to make** — those are exactly
the distinctions your census cannot see, and they are invisible precisely
because the tool that produced them had no reason to care.

**MEASURED AGAINST ITSELF — and it caught a THIRD wrong unit: IMPORTS.**
A bound on the breakage from a payload change was taken as the count of
**direct importers** of `Core.Outcome` — **2 files**. That is neither the
identifier nor the pattern position; it is a unit that cannot see the
thing at all, because **a consumer reaches a constructor's shape without
naming its module.** The convicting case *was* `guards.lean`'s
`refusalOf` — **and the current file refutes both halves of how this
document described it.** It now reads

```lean
-- Examples/go/rung1/guards.lean (excerpt: the destructurer, at HEAD)
def refusalOf (stmts : List Stmt) : Option (RefusalCause SpecRef) :=
  match (execSeq [] 64 stmts) ({} : GoWorld) with
  | .error (.unsupported c _ _) => some c
```

— a **three-field** pattern, not `.unsupported m`, and a return type that
**names `Core`'s `RefusalCause` outright**. The example was true when
written and **the Core payload landing invalidated it**, which is the
version of this document's own drift law that bites hardest: *the artifact
a claim cites keeps changing after the claim is filed.*

**The point survives the example, restated so it cannot be refuted by a
signature change:** a consumer **reaches a constructor's shape by
destructuring it**, and a module-import census cannot see that — whether
or not this particular consumer also happens to name the type. And **the
row's own count needs the same correction**: the doc's recommended grep
(`.error (.unsupported`) finds **11 lines across FIVE files**, not three —
`Go/Spec.lean`, `Core/Outcome.lean`, `Monadic/Substrate.lean`,
`Examples/go/bitlen/guards.lean`, `Examples/go/rung1/guards.lean`.

The calibration, five units on one change:

| unit counted | value | what it is |
| --- | ---: | --- |
| direct importers of `Core.Outcome` | **2** | **not a bound at all** — misses every non-importing destructurer |
| transitive reachers | **128** | true, useless: bounds nothing |
| **sites that DESTRUCTURE the constructor** | **11 lines / 3 files** | **the right unit** — a tight upper bound |
| actually broken | **1** | what the change cost |
| build-reported | **6** | five `#guard`s downstream of **one** cause |

> **The blast radius of a constructor change is bounded by the sites that
> DESTRUCTURE it. Grep the PATTERN POSITION — `.error (.unsupported` —
> not imports, and not the API's identifiers.**

**AMENDED — the grep MIS-COUNTS IN BOTH DIRECTIONS, and the law as first
written warned about only one.** Calibrated by the C tier, which had
already moved `unsupported` **out of `ρ` and into `Halt`**:

* **`.error (.unsupported` returns ZERO there.** The pattern was written
  for tiers where refusal still rides the **error channel**; a tier that
  moved it is invisible to the very grep that is supposed to bound it —
  an **under**-count of the worst kind, because it reads as *"no work to
  do."*
* a naive `.unsupported` grep **OVER-counts by 4** — `Ast.lean`'s
  `Expr`/`Stmt`/`Decl.unsupported` constructors, three unrelated types
  sharing a constructor name.

So the fix is neither "match the position" nor "match the name" but a step
before both:

> **The pattern position is the CONSTRUCTOR OF THE TYPE BEING CHANGED,
> WHEREVER THAT TYPE RIDES. Name the type first, then grep its
> constructor's pattern.**

The type is the thing that changed; the channel it happens to ride is a
fact about the tier, and a grep hard-coded to one channel is a grep with a
tier's design baked into it.

**AND THE COMPLEMENTARY DESIGN LAW — you can SHRINK the blast radius
before you measure it.** Two tiers priced their Core adoption and both
found the same mechanism doing the work:

| tier | touch points | actually matched | insulated by |
| --- | --- | --- | --- |
| **ES** | **198** "guards" as first framed | **5** destructure + **2** construct | four factored helpers (`yields`/`runs`/`throwsKind`/`refuses*`) — only the `refuses*` family matches `Halt` at all |
| **C** | **64** touch points | **8** construct + **8** destructure | **53 of 64 INSULATED at zero cost**, because every refusal routes through a **named primitive** |

ES's first framing over-estimated by roughly **40×**. The reason is not
carelessness; it is that **callers of a helper are not touch points at
all**, and only inspecting the helper says so.

> **Concentrate outcome-shape knowledge in helpers. A substrate change is
> then priced by the HELPERS, not by their callers.**

**C's 53-of-64 is §3.4's routing law paying for itself at adoption.** That
law — *never a bare polymorphic `throw`; route every refusal through a
NAMED primitive* — was adopted for uncatchability and for `@[spec]`
registration. It turns out to also be the thing that makes a substrate
change cheap, which is the useful kind of corroboration: a rule adopted
for one reason earning its keep in a second.

**One arithmetic note, because the law applies to its own evidence.** ES's
raw grep returned **8**, of which **3** were name collisions on other
types — and the honest total is **7**, not 5, because the two
**construction** sites match a *different* pattern than the destructuring
ones. **No single grep produced the number.**

**AND THE FULLER RE-MEASUREMENT SHARPENS IT: the ES price was RIGHT AND
INCOMPLETE.** Its **7 destructure sites were exactly right** — but the same
adoption carried **22 CONSTRUCTION sites across five modules**, which a
grep for `.unsupported` alone never sees. The type's price was **not 7**;
7 was the price of *one half of one direction*.

> **A price grepped for ONE CONSTRUCTOR is not a price for the TYPE. Price
> CONSTRUCTION and DESTRUCTURING separately, and SUM.**

This is the same failure the ladder has now shown four ways — imports,
identifiers, one-channel patterns, and now **one direction of use** — and
it is the most seductive of the four, because the destructure number was
**correct**. A right answer to half the question reads exactly like a right
answer.

That is the law's own
prescription arriving in its own calibration: enumerate the positions, and
expect more than one pattern to be needed.

**AND THE SHAPE SET HAD A FOURTH MEMBER, measured — ANNOTATION** (QoL,
`b2150ae`, on master). `runIndetRaw : … Halt …` is a **type annotation**: it
names the **type** and **no constructor**, so every channel in `sites.sh` — all
of which grep `\.$CTOR` — was **structurally blind to it.** The C successor
counted value constructors and destructures, called the change priced, and
**RED A TENURE on the signature that survived.**

**Live on this tree, full scan, no PARTIAL: DESTRUCTURE 13, CONSTRUCT 18,
ANNOTATE 20 — and all 20 name NO constructor.**

> **The type has MORE ANNOTATION SITES THAN DESTRUCTURE SITES, and the old
> census could see none of them.**

**The failure is one of KIND, not of threshold**, which is what makes it the
sharpest instance in this family: *no cutoff on the old channels could have
found these*, because the thing being counted never appears in them. The
ladder's earlier members were **wrong counts**; this one was a **missing
column**, and a missing column is invisible to every check that reads the
table.

> **A CHANNEL THAT GREPS THE CONSTRUCTOR CANNOT SEE THE TYPE. Enumerate the
> KINDS of position — destructure, construct, ANNOTATE — before enumerating
> the positions.**

**RIDER, and it had to be learned mid-landing: A LEADING DOT AND A QUALIFIER
ARE DIFFERENT DOTS.** Excluding every preceding `.` rejected
`LeanModels.C.Halt`, the qualified spelling the tool already treats as the
type; allowing every dot would accept `.Halt`, an **anonymous constructor**.

> **What PRECEDES the dot decides.**

A discrimination this fine is the ordinary case in a positional matcher, not
the exception — and it is why *"just grep for the name"* keeps producing
numbers that are wrong in both directions at once (§5.4a's under/over pair).

**And one note on cost, because it cuts against the usual expectation**: the
first cut called the comment stripper **a second time per file** and went
PARTIAL at file 5040 of 9825. The stripper is the expensive part and **does not
depend on the pattern**, so the second regex now **rides the first traversal** —
same 45 s budget, baseline 3 626 files, two channels **3 732**. **The channel is
free.** A new *kind* of position usually costs a pass over the corpus; it costs
nothing when the expensive work is shared, which is worth checking before a
channel is refused on performance grounds.

**AND THE MOTIVATED-ERROR RULE, from a census that was wrong TWICE before
it was right — and both errors flattered** (and see §9.7 for the instance where
this rule, written down in advance, **caught its own lane's later error before
it was paid for**). SoftFloat's consumer count ran
**319 → 170 → 13 candidates → 0 qualified crossings.** The two wrong
numbers came from the identifier trap in its purest form: **bare member
names are English words and other types' members**, and `.exp` / `.log`
were **Mathlib's `Real.exp` / `Real.log`**.

**What makes this more than a third instance of the identifier law is the
DIRECTION.** A bigger consumer list is **a bigger mandate for the lane
that is counting**. The error was not random with respect to the
measurer's interest:

> **When an instrument's error would ENLARGE ITS OWNER'S MANDATE, treat the
> number as FLATTERING until a recall-preserving narrowing reproduces it.**

That is §5.4a's asymmetry with a cause attached. The provenance law
observes that misleading numbers tend to read clean; this says **where to
expect it**: at any measurement whose overstatement would justify the
measurer.

**AND THE FIX IS THE INSTRUCTIVE PART — it was not a cleverer regex.** A
sharper pattern would have been one more guess. What worked was a
**narrowing that CANNOT LOSE RECALL**: *a file with no `Float` token in
code cannot contain a `Float` crossing.* The narrowing is justified by an
argument about the domain, so it is safe by construction rather than by
being careful.

And the leftovers were handled by **not counting them**: dotted rows were
kept as **CANDIDATES, never merged into the count**, and **resolved by
reading**. **13 candidates became 0 qualified crossings** — a number that
only exists because the ambiguous rows were held apart from the total
instead of being folded in with a plausible assumption.

**AND THE NARROWING'S RESIDUAL CLASS SURFACED ON THE NEXT DRIFT — the THIRD
disguise of the name-collision family** (SoftFloat, re-ticketed `9e3c235`;
verify at landing). The coordinator's hypothesis was **`Basic.lean` edits**; the
measurement said otherwise: **two `Nat.log2` rows matching the opaque-set member
`log2`.**

**The sharp part is that the sound narrowing's PRECONDITION WAS SATISFIED.** The
file **genuinely contains the `Float` token** — it opens `Float.Model` — so the
recall-preserving filter admitted it correctly, **and the candidate was still
spurious.**

> **A SOUND NARROWING HAS RESIDUAL CLASSES. Being safe by construction bounds
> what a filter can LOSE; it says nothing about what it still ADMITS.**

> **Each kill teaches the next disguise.**

**Which is why the candidate-versus-count discipline above is load-bearing and
not merely tidy**: the narrowing is what makes the candidate set small enough to
read, and **holding candidates apart from the total is what keeps the residue
visible** while its classes are learned one at a time. *A filter that folded its
survivors into the count would have retired this class as a number.*

**AND THE REPAIR WAS A RULE, NOT A REGENERATION — with an acceptance test worth
copying.** The rule: **an uppercase receiver is a NAMESPACE; a namespace that is
not a float owner is a DEFINITE non-crossing** (`Nat.log2` cannot be
`Float.log2`); **lowercase receivers stay candidates**; and **excluded rows are
LISTED, never dropped**.

**It self-validates against prior manual work.** Of **15 candidates it excludes
exactly the 7** the lane had resolved **by hand** in the decimal census — *the
instrument now derives what previously needed a human read.*

> **WHEN A HUMAN RESOLVES INSTRUMENT ROWS BY HAND, THE RESOLUTIONS ARE TRAINING
> DATA FOR A RULE — and the rule's ACCEPTANCE TEST is reproducing them
> EXACTLY.**

**Exactly is the operative word**, and it is what makes this a test rather than
an impression: a rule that reproduces *most* of the manual resolutions has
**found a different rule** and hidden the difference in the rows it disagrees
about — which are precisely the interesting ones. **A regeneration would have
produced a fresh number nobody could check against anything; a rule produces a
number that must agree with work already done.**



**Read the last two rows together, because they are the practical point.**
The destructure count (11) **over**-estimates real breakage (1) — it is an
upper bound, which is what you want for planning. The build report (6)
**over**-states *sites* by amplification: five of the six are `#guard`s
downstream of a single cause. So **neither the plan nor the build log is a
count of causes**; the destructure grep bounds the work, and the log
locates it.

**And the grep must DISCRIMINATE.** Two correct exclusions in this change
were `.unsupportedDevice` — a constructor of a **different type** whose
name shares a prefix. A pattern-position grep that matches on the
constructor name alone re-imports the identifier law's failure; matching
the **position** (`.error (.unsupported`) is what excludes them.

#### AND THE THIRD OF THE FAMILY — when a VERDICT VOCABULARY must grow

**THE RE-FOUNDING COROLLARY, and it is now the FOURTH instrument this lane
has had to teach a legitimate new state:**

> **During a re-founding, every two-sided check needs a vocabulary for
> "these differ ON PURPOSE" — and the default vocabulary never has one.**

The four: `DIVERGE`/`DIVERGED`, the census's grammar column, the gate's
`OPENED`, and now `MONO_OPENED`. Four is no longer a run of bad luck; it is
**a property of re-founding**. Any check built when there was one model
will need this word the moment there are two, and it will not have it.

**THE HONESTY SPLIT that keeps this from becoming whitelisting:**

> **The census RECORDS intent and never adjudicates. The gate
> ADJUDICATES.**

A census may say *"these differ on purpose"* — that is a claim about
**intent**, and recording it is what makes the difference visible. Only the
**gate** may decide whether the difference is acceptable, and it decides
**from the oracle**: `OPENED` counts **only when the rebuild matches
CPython**. Separating the two is what stops "extend the vocabulary" from
degrading into "record that we meant it" — the failure the *adjudicator is
the oracle, never the table* rule names.

**AND THIS VOCABULARY IS WINDOW SCAFFOLDING — it retires with the window.**
The two-model window (§3.4) is what creates the need for a
differ-on-purpose word; when the window closes the word has nothing to
name. The resolution is ruled **DELETE**, not deprecate: the successor's
landing **deletes `monadic_gate.py`**. A vocabulary kept past its window
becomes a permanent invitation to record intent instead of measuring
agreement.

**BUT DELETE HAS A PRECONDITION, and missing it inverts the ruling.**
`MONO_OPENED` could not simply be deleted. Its own comment recorded why
the table was safe: it *"cannot become a silencer BECAUSE `monadic_gate`
adjudicated its rows against the oracle."* **Delete the adjudicator and
keep the table, and you have built the silencer** — the rows survive with
nothing checking them, which is precisely the whitelist the honesty split
forbids.

> **When a window's ADJUDICATOR retires, every row it adjudicated must be
> RE-ANCHORED to the surviving oracle — never left merely recorded.**

Done here by moving the rows `expect:unsupported → match`, so
**`diff_test` adjudicates them against CPython**. The adjudicator changed;
the adjudication did not lapse.

**And the re-anchoring is not optional bookkeeping — dropping the rows
would have been worse than keeping them.** Four census rows carried
`mono=MATCH` against `expect=REFUSE`, where the `REFUSE` was **the retired
trunk's answer**. Dropping them checks the rebuild against **a retired
interpreter's expectation**; keeping them un-adjudicated checks it against
nothing. **Only re-anchoring to the surviving oracle is a check at all** —
which is §5.3's *agreement with the ORACLE* rule, arriving at the moment a
window closes rather than while it is open.

The two rules above are about **counting**. This one is about **verdict
vocabularies**, and it is the third instance minted this session:

> **A CHECK WHOSE VOCABULARY CANNOT EXPRESS A LEGITIMATE NEW STATE WILL
> EITHER BLOCK THE STATE OR BE SWITCHED OFF — both wrong. Extend the
> vocabulary, and make the new word EARN ITS VERDICT FROM THE ORACLE,
> NEVER FROM THE TABLE.**

The failure has two exits and a check reaches for one of them
automatically. **Blocking**: the state is legitimate, the gate says no, and
correct work cannot land. **Switching off**: the gate is disabled or
loosened, and now nothing is checked. Neither is a decision anyone makes on
purpose; both are what happens when a vocabulary runs out of words and
nobody notices that is what happened.

Three instances, and the third is the sharp one:

| instance | the missing word |
| --- | --- |
| `DIVERGE` / `DIVERGED` (§9.4) | a **display name drifting with its selector** — the same state under two spellings |
| the census's `mono=` expectations | a **two-interpreter scoreboard needing a second column**, and reporting one |
| **`monadic_gate.py`** | exits non-zero on **ANY** non-frontier divergence — so a **RULED** divergence (trunk refuses, rebuild returns `1`, **CPython AGREES with the rebuild**) **literally could not land green** |

**The fix, and the guard that makes it safe.** `monadic_gate.py` gained
`OPENED` — **counted only when the rebuild matches CPython.** That
qualifier is the whole rule:

> **The adjudicator is the ORACLE, never the TABLE.**

**AND ITS TOOLING FORM, measured on two protocol tools that disagreed about one
file (`f5b35a0`).** `check.sh` read `lakefile.toml` and called a repo-root
`.lean` **scratch** (correct — `Examples.+` matches no root module);
`triad.sh` hard-coded `LeanModels/*|Examples/*` and warned **"unstaged Lean
under a lake glob"** about the same file. It warned rather than refused, so
nothing broke — **but two protocol tools disagreeing about one file eventually
gets trusted in the wrong direction**, and the lane fixed it before it did.

> **When two tools disagree about a fact, neither is the authority. Find the
> artifact that DEFINES the fact, and let exactly one reader parse it.**

`tools/lakeinfo.sh` now holds the reader and both tools source it (MEAS-28: a
second parser is a duplicate that will drift). **And the fix had to go deeper
than the classifier**, which is the transferable half: the warning came from
`lean_glob_offenders`, whose predicate asked *"is this not-docs?"* — and a
repo-root `.lean` **is** spine, which is not-docs, so the guard was answering a
different question from the one its message announced.

> **A guard must ask the question its MESSAGE claims to be answering. "The
> warning names a lake glob, so the LAKEFILE decides it."**


A new verdict word is not a place to record what you have decided is
acceptable; it is a place to record **what the oracle says**, under a name
the old vocabulary could not pronounce. Without that guard, "extend the
vocabulary" is just whitelisting with better manners — which is why this
is the same prohibition as the standing ban on `"expect": "unsupported"`
rows that silence a mismatch, generalized from one harness to every check.

**And the wrong fix was named and refused rather than merely not taken**:
switching the gate off would have turned a vocabulary problem into a
coverage hole, and a coverage hole reads green. That is §5.4a's flattering
direction, reached by a route that feels like pragmatism.

**This is also what §5.1's membership ruling was**, recognized late: *the
DIVERGE test is not equality at every site* extended a verdict vocabulary
so it could express a legitimate state — two conforming implementations
disagreeing — that the old one could only call DIVERGE. Same law, applied
before it was named.

Every instrument output, triad line, coverage count, `#guard` batch, axiom
print and timing is reported **with the state that produced it** — clean
elaboration, faithful subject, untorn tree. The failure mode is not that
these numbers are noisy; it is that **at least two of the three read
CLEANER than the truth**, so the error is silent and flattering, and a lane
that trusts them stops looking. This is the same instinct as §5.4's *every
refusal path RUN, not admired*, pointed at the evidence instead of at the
code.

#### 5.4a-i INCREMENT GREENS — a green may rest on a NAMED green, and must say so

A branch that is already green is charged again for every tenure taken on
top of it: `--classify` diffs the whole branch against `github/master`, so a
two-file docs commit stacked on a freshly-certified branch re-elaborates work
that was certified an hour earlier. The pyc lane withdrew such a ticket and
proved its increment's class by hand (`git diff --name-only <green-sha>
HEAD`, two docs files). This makes that mechanical, under the provenance law
above: **a green that rests on another green must carry the one it rests on.**

**A GREEN CERTIFIES A TREE, NOT A COMMIT.** The tenure stamp hashes the
**WORKING TREE** — what `lake` actually reads — plus HEAD. (It hashed the
INDEX until `22ed755`; that blind spot is its own entry below.) So a green can
certify content that is not any commit, whenever uncommitted work was in the
tree. A green is therefore **citable** as an increment base only when its
working tree equals its HEAD commit's tree; otherwise the sha names what the
green did not certify. This is the provenance law applied to the evidence's own identity.

**AND THE LADDER HAS A THIRD RUNG, MEASURED THE EXPENSIVE WAY: A GREEN
CERTIFIES A TREE, NEVER A TITLE** (Ada successor's reconstruction; the adoption
redo is `342a1f5`, tenure queued). A prior *"adoption tenure"* came back
**GREEN** — true lock line, clean gates, **exit 0** — certifying a tree
(`ea56aea`, identical to the ticket commit's tree) that contained **only
backlog-doc changes.** The adoption it was enqueued **for had never been
implemented**: `Value.lean` still carried **all 8 `ADOPT` markers**.

> **THE GREEN WAS TRUE AND ANSWERED A DIFFERENT QUESTION THAN THE TICKET
> ASKED.**

**This is the exact DUAL of the enqueue-tree stamp** (§7.2), and the pair is
worth reading together: the stamp stops the tree **changing after enqueue**;
**nothing checked that the tree ever CONTAINED the work the ticket's title
promises.** One guards the interval, the other guards the premise, and a tenure
can satisfy the first perfectly while failing the second completely.

> **A verdict certifies a TREE, never a TITLE. The reader of a green compares
> the CERTIFIED TREE against the CLAIM — the title is not evidence about the
> tree, it is evidence about intent.**

**AND THE SAME LAW APPLIES TO THE WORD "VERIFIED" — including in a
coordinator's own note** (Go §G24, `eb1e8b0`). The dispatch claimed §G24 was
*"on master (verified)"*; **the shas that had actually been verified were
§G23's.** The lane **flagged it rather than quietly acting on it.**

> **A stale note never authorizes — and that applies to the note's AUTHOR's
> authority, not only to its age.**

> **A verification claim carries WHAT was verified. A sha-less "verified" is a
> TITLE.**

**Which is this section's own ladder, one level up from the artifact**: a green
certifies a tree and not a title; **a "verified" certifies the specific objects
someone looked at, and not the sentence it appears in.** The failure mode is
identical — *the word is true of something, and the something is not what the
reader will assume.*

**And the lane's response is the transferable part**, since a dispatch from the
coordinating role arrives with standing: **it flagged rather than acted.**
*Claims, not claimants* covers who may be wrong; this covers **what to do about
it in the moment** — neither obey a note you cannot verify nor silently work
around it, but **say which shas you checked.**

**AND THE LAW HAS AN AFFIRMATIVE USE, now on its THIRD instance** (R-track;
after SV declined a rebase and this lane's own `-55` recorded the negative
case). The R-track lane **committed the INDEX rather than the working tree**,
because post-certification **verdict prose** would otherwise have changed the
tree the green certified.

> **A lane that understands *the verdict certifies a TREE* will sometimes commit
> something other than what is in front of it — and that is the law being
> USED, not worked around.**

**The negative and affirmative readings are worth keeping side by side.**
Negatively, the law catches a green that answered a different question.
Affirmatively, it tells a lane **which of several honest commits preserves the
certification** — decline the rebase, decline the fold-in, commit the index.
**Three lanes have now taken the affirmative branch independently**, which is
the convergence standard (§9.3) applied to a law's *use* rather than to its
statement.

**AND THE DESIGN WAS TESTED BY A FLEET-WIDE DEATH — TWELVE AGENTS, ZERO WORK
LOST** (the 529 storm, 2026-08-24). Worktrees, pushed branches, ledgers and
detached runners **carried everything.**

> **DURABILITY LIVES IN ARTIFACTS, NOT IN AGENTS.**

**And the one in-flight gap was recoverable BECAUSE OF THE STAMP v2 FIX** —
R-track's **certified-but-uncommitted staged state**. The certificate hashes the
**working tree**, so `index tree == certified tree` was **verifiable after the
death of the agent that produced it**, and the work was committed on the lane's
behalf (`4ed731e`, merged `d681a89`; both on master, verified here).

> **A CERTIFICATE OVER THE WORKING TREE MAKES EVEN UNCOMMITTED STATE
> RECOVERABLE.**

**That is a payoff the fix was not designed for.** It was built to close an
integrity hole — *the stamp must hash what `lake` reads* — and the property it
bought is **a different one entirely**: uncommitted work becomes **identifiable
by a third party**, because there is a hash of it that somebody else can
recompute. *An integrity fix that makes state addressable makes it recoverable,
and nobody planned the second half.*

**AND A SMALL IDENTITY ROW FROM THE SAME RECOVERY**: the classifier **blocked an
explicit `-c` identity override** on that commit, and **plain config was the
right form.**

> **COMMIT PROVENANCE COMES FROM THE ENVIRONMENT, NEVER FROM A FLAG SOMEONE
> TYPES.**

**A typed identity is an assertion; a configured one is a fact about the clone**
— and the difference matters precisely in the case that produced it, where **one
party commits on another's behalf.** *The attribution a recovering party should
produce is the one the environment already knows, not the one they believe is
correct.*

**AND A FIFTH, AT PUSH GRANULARITY** (SoftFloat's `roundQ` landing, merged —
`52c5d35` is **the GATED sha**). The lane **refused to call its clean rebase
gated.**

> **A rebase that changes nothing still produces a DIFFERENT COMMIT, and the
> certificate names the one that was BUILT.**

**The certificate discipline at the smallest granularity yet** — not a merge,
not a ticket, but **which of two shas a clean rebase produced.** *Nothing was at
stake and the lane held the line anyway, which is the only time a discipline is
cheap to keep.*

**AND A FOURTH, AT MERGE GRANULARITY, ARRIVING UNPROMPTED** (Ada). The lane
**pre-declared** that the merge was *"the gated Lean landing, not a docs commit
bundled into it"* — **separate shas, said before the merge rather than
reconstructed after.**

> **The certified-tree boundary is expressed at MERGE GRANULARITY: what was
> gated is one sha, and what rode along is another.**

**A bundled merge is the wrong-tree failure with the evidence pre-mixed**: after
the fact, *"the green covers this"* becomes a claim about a commit that contains
both the gated tree and whatever was folded in beside it, and **no reader can
separate them from the merge alone.** Declaring the split **before** costs a
sentence; recovering it afterwards requires the tree comparison this section
exists to make unnecessary.



**AND THE LADDER'S SUBJECT, STATED PLAINLY — "THE RUN IS CORRECT" AND "THE
CERTIFICATE IS CORRECT" ARE DIFFERENT CLAIMS** (Lean tier, closing its own
wrong-stamp hazard: dequeue by verified-parentage kill, commit, FF to v2,
triple-verified banner).

> **Only the SECOND is what a green IS.**

**That is what the three rungs above have been circling** — not a commit, not a
title, and now the general form: **a tenure produces a certificate, and every
rung of this ladder is a way the certificate can be true of something other than
the work.** A run that did the right thing under a stamp that names the wrong
tree has **done correct work and issued a false certificate**, and only one of
those is the artifact anybody downstream will read.

**AND THE INCIDENT'S OWN LESSON IS SHARPER THAN THE HAZARD.** The lane **wrote
the evidence of its own hazard into its report without acting on it** — the
finding was filed while it was live in the filer's own tenure. Its formulation:

> **A finding about the TOOL that is also true of your OWN IN-FLIGHT TENURE is
> not a finding — it is an INCIDENT.**

> **Check a finding against the finder's own in-flight state BEFORE filing it.**

**The two have different urgencies and different actions**, which is the whole
point: a finding goes to a register and waits for a lane; **an incident stops
what you are doing.** Filing an incident as a finding is not a clerical error —
**it routes a live problem into a queue**, and the queue is exactly where it
will not be looked at until after the tenure it was about has finished.

**TWO WITNESSES, RANKED, and the ranking is the transferable part.**

* **PRIMARY — tree identity.** The verdict **is** about a tree, so the tree is
  the only witness that speaks in the verdict's own terms. Everything else is
  circumstantial.
* **CORROBORATING — build duration.** **4 seconds cannot be a Mathlib-rooted
  adoption.** It is decisive in practice and it is still second, because a
  duration is a fact about *this run* and the claim is about *this tree*.

**AND A THIRD RESOLUTION OF THE FAST-GREEN AMBIGUITY — THE STRONGEST OF THE
THREE** (Lean tier's 2/27, fork `1dc1dfc`). The coordinator's **warm-cache
hypothesis was corrected**: there was **NO authoring build.** The lane's own
discipline — *all Lean inside the tenure* — means the **801 ms gate line was the
file's FIRST AND ONLY elaboration.**

> **That is what makes the 1 s honest — not a warm cache.**

> **A FAST GREEN IS HONEST WHEN THE FIRST ELABORATION *IS* THE CERTIFIED ONE.**

**Three resolutions now, and they are ordered by what they need**: **tree
identity** needs the stamp; **`Built`/`Replayed`** needs the log's right phase;
**this one needs a fact about the lane's PROTOCOL** — that no Lean ran outside
the tenure. **It is the cheapest to check and the only one available before the
log exists**, and it is unavailable to any lane that elaborates while drafting.
*A discipline adopted for lock hygiene turned out to be the thing that makes a
fast green legible.*

**AND A COVERAGE STATEMENT CAN SUBTRACT WHAT IT DID NOT RE-ESTABLISH.** `Test`
was **`Replayed`**, so the landing says: *the 22 goldens' green is **carried
forward from `b23e892`**, not re-established here.*

> **A green states what it covers AND what it is carrying — a re-used verdict is
> a citation, not a result.**

**This is the §5.4a coverage statement doing subtraction rather than
enumeration**, and it is the harder half: listing what ran is routine, while
**naming what did not run and is nonetheless being relied on** requires reading
your own log for absences. *The `Replayed` token is where a carried-forward
claim announces itself, and a coverage statement that ignores it silently
re-asserts somebody else's tenure.*

**AMENDED — DURATION DROPS TO THIRD, AND THE SECOND WITNESS IS `Built` vs
`Replayed`** (Ada, merged `44ae259`; the lane applied this section's own
forensics to **its own honest 2-second build**). **The predecessor's dishonest
4 s and this lane's honest 2 s look ALIKE in the summary and OPPOSITE in the
full log.**

> **DURATION IS A CORROBORATOR, NOT THE WITNESS.**

> **`Built` vs `Replayed` is the primary witness that a module ELABORATED — a
> fact the summary line does not carry.**

**Ruled witness order: TREE IDENTITY first, `Built`/`Replayed` second, CLOCK
third.** Recorded as an **amendment, not an erratum** (MEAS-181): the original
ranking was **right that duration is not primary and right about why** — a
duration is a fact about *this run* while the claim is about *this tree*. What
it got wrong was **treating duration as the best available second witness**,
when a stronger one was in the log the whole time. **Both halves stand.**

**AND THE SECOND WITNESS MUST BE READ FROM THE RIGHT PHASE — a log is not a bag
of lines** (Go, `6c7a2b3`). That triad log carried **330 `Replayed` lines** —
**from the GATE phase's runner, not the build.** The build's own lines were
**30 `Built` / 2 `Replayed`, with all eleven tier modules `Built`.**

> **Reading the gate phase's lines as the build's witness would have been the
> available mistake.**

**AND THERE IS A THIRD STATE, which makes the pair a TAXONOMY** (Go §G24). A
module **named in the target list emitted NO LINE AT ALL** — **current from the
authoring build of the same tree** — while **its dependents `Built` against
it.**

> **The witness taxonomy is `Built` / `Replayed` / SILENT-CURRENT, and only
> reading the DEPENDENTS disambiguates the third.**

**"All Go modules `Built`" would have been wrong**, and the interesting part is
that the third state is **invisible to any check that reads the module's own
lines** — there are none. **Absence is the signal**, and this register has
convicted absence-reading four times already (a `null` on an absent repo, a
zero-row census, a `sed` with no input, a negative row that never ran).

**Here the disambiguation is structural rather than heuristic**: a silent module
whose **dependents built against it** was current; a silent module **nothing
built against** was not in the build at all. *The witness for a module that says
nothing is the testimony of the modules that used it.*



**Which is this section's own unit family arriving inside a log**: `Replayed` is
a correct token counted from the wrong region, and **the wrong region is the
larger one** — so the mistake is both easy and flattering-in-reverse (it makes
an honest build look replayed). **A witness is a token PLUS the phase it was
read from**, and a grep over a whole log has already discarded half of that.



**Keep them in that order.** A lane that leads with duration will one day meet a
warm cache and conclude nothing is wrong, and a lane that leads with the tree
never needs the clock. **The cheap mechanical aid — noted for the tools lane —
is a diffstat-vs-master line in the triad header**: a doc-only tenure would then
announce itself, and the 4-second green would have been **self-evident** rather
than reconstructed.

**CLASSIFICATION IS COMPUTED AGAINST THE CHAIN ROOT, NEVER THE PARENT.** Two
increments classified against their immediate predecessors can be `tier A`
and `tier B`, with neither build covering their interaction — a tier green
already declares that it does not cover modules that IMPORT the ones it
built. Chaining against parents compounds an admitted partial into an
unstated one. Chaining against the root does not: the union of everything
since the root is what gets classified.

**THE MERGE BAR.** An increment green satisfies it **iff the chain root is a
FULL (spine) green and every increment in the chain was classified against
that root**. A chain whose root is scoped does not satisfy it, and the
coverage line says which case it is rather than leaving the reader to
reconstruct it.

**THE LEDGER IS PER WORKING DIRECTORY, AND THAT IS THE POINT.** Greens are
recorded in `.git/triad-greens` — untracked, so it can never conflict; inside
the git directory, so it survives rebase and checkout. A green recorded in one
working directory is invisible in another because it is not VERIFIABLE there:
the build cache, toolchain and tree state that produced it are not present.
**Evidence does not travel by assumption.** Its absence is honest, not a
limitation.

**AND THE SCOPING IS `--git-dir`, NEVER `--git-common-dir` — "per-clone" is the
wrong unit and this sentence used to say it.** A **linked worktree shares the
common git dir and has its OWN `.lake`**, so a ledger scoped to the common dir
would offer clone-wide greens to a worktree that cannot reproduce them.

> **THE CACHE IS PART OF WHAT PRODUCED THE GREEN.** Scope the evidence to the
> directory that holds it.

That is the unit family (§5.4a) arriving in git plumbing: **`--git-dir` and
`--git-common-dir` differ on exactly the case the feature exists for**, and the
plausible-looking one is wrong. A worktree is the standard way this repository
takes a pristine baseline (§5.4b's re-baseline norm), so the wrong scope would
have misfired precisely where lanes are most careful.

**AND ONLY GREENS ARE RECORDED — REDS RECORD NOTHING.**

> **A LEDGER OF ATTEMPTS IS A LOG, AND A LOG IS NOT EVIDENCE OF A VERDICT.**

The ledger's entire purpose is to be **citable as a base**, and only a green can
be cited; an attempt history answers *"what happened here?"*, which is a
different question with a different consumer (the build log, §7.2, which is now
identified and attributable). **Mixing them would make the ledger's own name a
claim it cannot keep** — a reader who found reds in a file called `triad-greens`
would be right to distrust everything else in it.

**AND THE MODEL'S FIRST THEOREM, which survived its own implementation bug:**

> **A FULL BUILD IS ITS OWN ROOT, HOWEVER IT WAS REACHED.**

An increment whose build was **not narrowed** is a full build, whatever flags
produced it — so it starts a new chain rather than extending an old one.
Measured the hard way: such a run was recorded **at `depth=1` under an older
root** until the full-build test was moved **first**. **The invariant was right
and the implementation asked the questions in the wrong order** — which is the
distinction worth keeping, because the fix is a reordering rather than a
rethink, and a lane reading only the bug report would have concluded the model
was wrong.

**The ordering rule generalizes past this test**: when one predicate
**subsumes** another, it is asked first, or the subsumed one answers on its
behalf and the answer is quietly narrower.

#### 5.4b GATE TOPOLOGY — a gate set is a set of POINTERS, and coverage is what they point AT

The transcription incident above (§5.4) has a second half, and it is the more
general one. The lane that shipped the rotted copy was **not** running without
gates. It had four, they were all green throughout, and the file was saying the
opposite of the truth the whole time.

> **Every gate was green while the file said the opposite of the truth,
> because none of them was pointed at the claim that had rotted.**

The topology, enumerated — which is the only way it becomes visible:

| gate | pointed AT | blind to |
| --- | --- | --- |
| `probe_es_unblock.lean` is **EXPECTED TO ERROR** | that the two pre-unblock rows still fail | **everything else the file says** — its verdict is invariant under the prose |
| `probe_es_unblock_axioms.lean` is **expected CLEAN** | that the routed rows elaborate | the same |
| `tools/docs_check.py` | **marked blocks in `.md`** | a transcription living in a `.lean` **comment** |
| `harness/softfloat_consumer_census.py` | **call sites** | **citations** |

Four gates, four elsewheres. Nothing failed, because nothing was asked.

> **ENUMERATE WHAT EACH GATE IS POINTED AT. A CLAIM NO GATE POINTS AT IS
> UNGATED, HOWEVER GREEN THE NEIGHBOURHOOD.**

**The trap is that greenness reads as coverage**, and a DENSE gate set is worse
than a sparse one here: the more gates surround a claim, the more gated the
claim looks, and the inference runs from *neighbourhood* to *claim* without ever
touching the pointer. That is §5.4a's flattering direction aimed at gates rather
than at measurements — **a gate set's coverage is itself a claim about the
world, and therefore itself needs measuring.**

**And it is not measured by running the suite again.** Re-running re-answers the
questions already asked; the missing question is not in the suite by
construction. **A gate set is audited by ENUMERATION, never by execution.**

**The practical form, and it is three lines of work.** For each gate write
(a) what it would CATCH and (b) what it CANNOT SEE — **in the gate's own words
wherever it states them**, since a gate that documents its scope has already
done half the enumeration:

```python
# tools/docs_check.py (excerpt — the gate's own statement of what it is pointed AT)
Scans README.md, AGENTS.md, and docs/**/*.md. Exit 0 when every checked
block matches; exit 1 listing every drifted or broken block. Python >= 3.9,
...
A fenced code block is checked against the tree iff it carries a path
marker, in one of two forms:
```

Then read the file's claims against that list. **The claims with no pointer are
the exposure**, and they are found by reading the list — never by watching the
lights.

**THIS SECTION HAS AN INSTRUMENT NOW: `tools/laws.sh --gate-set` (`8fb27db`),
landed one day after the section was written.** It enumerates the pointers
rather than running them — *a gate set is audited by enumeration, never by
execution* — and **44 gates are declared, 2 UNRESOLVED** (`ea6f667`; the
first run said **16**, and the missing 28 were the anchor defect corrected
below — the count is stamped here because it moved once already).

**Its honesty clause prints FIRST, and it is a rider this section owes:**
enumeration reads **declarations**, so a gate whose target is **computed at
runtime** is listed `UNRESOLVED` and never guessed.

> **A guessed pointer is worse than a missing one, because it makes a claim
> look COVERED.**

`UNRESOLVED` is the only honest value for a runtime-computed target. A missing
pointer is a hole a reader can see; a plausible one closes the question. This
is *the remedy for a provenance gap is provenance, never reconstruction*
(§5.4a) arriving at a gate set — **an unresolvable target named honestly keeps
the hole visible and closeable.**

**AND THE "GATE'S OWN WORDS" CLAUSE ABOVE IS NOW MEASURED, not merely
recommended.** Reading only the *declaration* — `python3 tools/docs_check.py`,
which names a script and no scope — left `.md` looking **orphaned** while
`docs_check` was pointed squarely at it. Reading the declaration **and the
script's own header** *("Scans README.md, AGENTS.md, and docs/\*\*/\*.md")* took
the orphan list from **five kinds to one**. **Four of five orphans were the
enumerator's blind spot, not the tree's.**

**A defect on the way, and its DIRECTION is why it was caught.** `gate_rows`
emitted five tab-separated fields with **two empty placeholders**, and a tab is
whitespace — so bash collapsed them and every declaration landed in the wrong
variable, making **every kind look orphaned**. Three fields now.

> **An empty field in a whitespace-separated record is not a field.**

Recorded beside MEAS-12's asymmetry: this error erred toward **alarm**, and an
alarming number gets investigated on sight. Had the same collapse quietly
*attributed* gates instead of losing them, it would have read as coverage and
survived — **the flattering direction is the one that ships.**

**THE SECTION'S FIRST TWO CATCHES, one mechanical and one by hand.**

* **Mechanical, and CORRECTED WITHIN A DAY — see the correction below, which
  is the more valuable half.** `harness/sv_round_trip.py` **exists and appeared
  in `ci.sh` ZERO times**, against **18 `.sv` files** in the tree and 21
  committed envelopes — the SV lane's own gate was never in CI, and it is now
  wired (`ea6f667`). **But the headline it was first reported under —
  *".sv has no gate"* — was an INSTRUMENT ARTIFACT**, and the surviving claim
  is narrower.
* **By hand** — the Wasm lane ran the enumeration on its own four gates
  (`886ede9`) and found its **headline claim** — *"5 live obligations"* —
  pointed at by exactly one gate, **a text scanner that cannot see whether the
  file ELABORATES**. It was ungated **in precisely the dimension that later
  refuted it**: a compiler found the file does not build, making one of the
  five unreachable. Three censuses, all green, all deterministic, all with
  executed refusal paths — **the dense-neighbourhood trap, literally.**

**Both catches are the same shape as the incident that minted the section**,
which is the useful part: the law did not need a new failure to prove itself,
it needed someone to write the pointer list down.

**THE CORRECTION, AND IT IS THE SHARPEST THING IN THIS SECTION: THE
ENUMERATION'S FIRST FINDING WAS ABOUT THE ENUMERATOR** (`ea6f667`, correcting
this document's own `f587ec2`). `gate_rows` anchored its match **at column 0**,
so every **host-gated** gate — declared inside a function or an `if`, hence
**indented** — was invisible. **16 gates enumerated; 44 after the fix**,
including **`lake-build` itself**. An auditor reading the 16-row list would have
concluded *CI does not gate the build*.

**The counterfactual was RUN, not assumed**: the new `laws.sh` against the
**OLD** `ci.sh` reports **43 gates and NO orphan kinds**. `sv-harness` and
`sv2-harness` had been pointing at `.sv` all along; the anchor hid them.

> **A new instrument's FIRST finding is the one to re-run against the old
> input.**

**And the flattering direction here is not the usual one — it does not flatter
the TREE, it flatters the INSTRUMENT.** A day-old tool reporting a dramatic gap
in somebody else's work is the single output its author is least likely to
doubt: it is the tool justifying its own existence. That is *a finding
un-re-read is a claim, not a finding* (§5.4a) pointed at the enumerator, and the
scope-inheritance rule from the same section — *a measurement that CORRECTS a
claim must not take its scope from the claim it corrects* — is what the
counterfactual implements. **Running the new tool on the old input is the
output-equality discipline (§5.4a) used in the correction direction: it is the
only way to separate what the FIX changed from what the TREE changed.**

**WHAT SURVIVES, and it is a real finding in a narrower form.** Both `.sv` rows
are **simulator-gated and SKIP on a stock runner**, so **on CI, `.sv` had no
gate that RUNS** — and the round-trip gate is the one that can, which is why
the wiring was right for a reason different from the one first given. *The
disposition was correct; its justification was not, and only the second was
published.*

**SO THE POINTER LIST HAS FOUR STATES, NOT TWO, and "green" reports only the
last.** A gate can be **DECLARED**, **CALLED**, **RUN ON THIS HOST**, and
**POINTED AT THE CLAIM** — and each step loses members:

> **A DECLARATION IS NOT A CALL.** A gate declared inside a never-called
> function still enumerates perfectly.

> **A CALL IS NOT A RUN.** A gate that SKIPs for an absent simulator, package
> or host is a gate the claim does not have *here*.

Enumeration reads declarations, so **it can only ever establish the first
state**; the call site is pinned separately — by a `--verify-guards` row, in
this tree — and the host question is answered by the skip discriminator (*a
tracked file is not optional; an untracked one may SKIP*). **A gate set audited
only by enumeration over-reports, and one audited only by execution
under-reports**, which is why §5.4b asks for the pointer list *and* why the list
is not the whole answer.

**AND *A FIXTURE IS NOT ENFORCEMENT* (§9.7) EXTENDS TO DECLARATIONS**: the
`--verify-guards` region is cut before matching, **inside `gate_rows`** rather
than inside the citation counter whose numbers were not that inch's to move.
The same rule, at a second site, with the blast radius deliberately bounded.

**AND THE ENUMERATION ITSELF MUST BE BY DISCOVERY, NEVER BY LIST** (QoL,
`95849db`, on master). A spin the Go lane paid **31 minutes** for was
reproduced, and it was **not one arm — it was the SHAPE**: `${2:-}` accepts a
missing value, `shift 2` then fails with one argument left, and the loop
re-enters on the same argument. **28 value-taking flags across ELEVEN tools**,
every one of which spins if written last. One guard, `tools/argv.sh`, sourced by
all of them — the one-source rule again (§5.4a's *let exactly one reader parse
it*).

The new `ci.sh` `argv-guards` step probes **every value-taking flag found by
READING the tools**, and the reason it is written that way is the law:

> **A LIST WOULD BE MAINTAINED BY THE SAME ATTENTION THAT WROTE THE UNGUARDED
> ARM.**

**A hand-maintained scope inherits exactly the failure it exists to catch.**
The lane that forgets to guard a new flag is the lane that forgets to add it to
the checklist, and the two omissions are the *same* omission — so the checklist
cannot see it, by construction. This is MEAS-19's *generated and checked, never
hand-maintained* aimed at a **gate's scope** rather than at a manifest, and it
is the sharper half of §5.4b's practical form: **enumerate the pointers by
discovery, or the pointer list is a second place to forget.**

**AND THE GUARD REFUSES RATHER THAN DEFAULTING, because the near-miss is worse
than the spin.** The spin is loud in the wall clock and silent in the log; but a
run that merely **lost its `--gates` value completed and reported GREEN on the
default floor** — *less coverage than the lane believed it bought, with nothing
in the log to say so.* **A spin costs an hour; a silent floor costs the
verdict.**

**AND A CHECKABLE CLASS THIS TREE HAS BEEN LEAVING TO READERS: THE SECTION
CITATION.** `docs/python-monadic-rebuild.md` cites **`§8.5` in four places** and
**has no §8.5** — verified here. The lane had already noticed and written *"the
anchor dangles"* at its head, which is honest and is **not a control**: prose
noting a defect is prose (§5.4).

**And the sharper reading is that an existing law already rules it.** MEAS-30
says **inside a `.md` an untagged `§` is an INTERNAL reference** — so those four
citations are not merely dangling, they are **untagged cross-document
citations**: the intended referent is *this* charter's §8.5, and the spelling
says *that document's*. **The defect is a missing filename, not a missing
section**, which is a different fix and a much smaller one.

> **A SECTION CITATION IS MECHANICALLY CHECKABLE — same class as the
> `docs_check` anchors.** For every `§N.N` in a `.md`: either the same document
> carries that heading, or the citation names the document it belongs to.

**Why it belongs in the gate set rather than in a reviewer's habits**: a
citation is the one kind of prose whose referent is **resolvable without
judgement**, so leaving it unchecked is leaving free coverage on the table —
and the failure mode is exactly the transcription family's (§5.4), since a
section number is **a copy of another document's structure** and rots when that
structure moves. The fix is routed to the owning lane; **the shape is the
register's.**

**AND THE READER LAW, owned TWICE in one landing by the lane that had just
written the rules it broke:**

> **A NEWLY WRITTEN READER DEFAULTS TO UNDER-READING, AND UNDER-READING IS THE
> DIRECTION THAT REPORTS "ALL CLEAR".**

Both instances are already-minted laws firing on their own author. **Matching
one line missed `sites.sh --channel`, a two-line arm** — the same column-0
anchoring that had `--gate-set` reporting **16 of 44** — and the next pass then
**discovered `--flag` from `ci.sh`'s OWN fixtures**, which is *a fixture is not
a tool*: the mirror of §9.7's *a fixture is not enforcement*, and the same
self-selection hazard (§5.4) arriving through test data rather than through
source.

**Read the direction, because it is what makes a new reader dangerous rather
than merely immature**: a reader that under-reads finds **fewer** sites and
therefore reports **fewer** problems, so its first run looks like good news.
**The failure mode of a new instrument is congratulation.**

**AND A SAMPLE CAN BE SYSTEMATICALLY UNABLE TO CONTAIN THE THING IT IS SAMPLED
FOR** (QoL item 9, merged). *"First 8 of 46"* sampled in **STRING order**, and
`spec.lean:102` **sorts before `:24`** — so **the causal first error was not
merely missing from the preview, it was UNREACHABLE by it.** The eight lines
contained it **zero times**, and would have on **no** run.

> **A SAMPLE WHOSE ORDER DIFFERS FROM ITS LABEL'S ORDER IS A DIFFERENT SAMPLE
> WEARING THE LABEL.**

**"First" is a claim about an ordering**, and `sort -u` supplies one silently.
The failure is **not probabilistic** — which is what separates it from an
unlucky sample and makes it a defect: *no number of reruns would have surfaced
the row*, because the ordering that hid it is the ordering that produces it.

**AND THE SELF-TEST ROWS THAT SHOULD HAVE CAUGHT IT CHECKED THE CAPTION.** Two
rows asserted **that the preview is LABELLED `first 8 of 15`** — *precisely the
promise being broken* — and **passed while the output lied.**

> **A ROW THAT CHECKS THE CAPTION WHILE THE PICTURE IS WRONG IS NOT A TEST OF
> THE PICTURE.**

**The repaired rows assert CONTENT — and that a sorted sample WOULD HAVE DROPPED
IT**, so **the fixture exercises the trap rather than resembling it.** That
second clause is the transferable part: a fixture built from the incident's
*shape* passes for the same reason the original code did; **a fixture built to
fail under the defect is the only kind that stays a test after the fix.**

**AND THE RESTRAINT RIDER — the pre-existing double-listing was FLAGGED, NOT
DE-DUPED.**

> **A DE-DUPE COULD SILENTLY SHRINK A SET.**

An instrument auditing a set must not **repair** that set: de-duplication is an
edit made by the reader, on data it does not own, and a wrong equality test
removes a member while the count moves in the direction that looks tidy. **The
census RECORDS and never adjudicates** (§5.4a) applies to a reader's own input,
not only to its verdicts — **flag the anomaly, and let the owner decide whether
two entries are one.**

**AND A RUNG CAN BE POINTED AT THE CLAIM BY ACCIDENT, which the ladder's four
states do not distinguish** (Ada, 2026-08-24). **`LeanModels.lean` does not
import `LeanModels.Ada`** — the tier reaches the default build **only through
the `Examples` glob.** It is a **live, pointed** gate whose liveness is supplied
by **an example file happening to import it.**

> **A gate reached by ACCIDENT is a gate that retires when somebody tidies an
> unrelated file.**

**This is *a dependency satisfied by a NEIGHBOUR is not a dependency met*
(§7.2) pointed at a gate's REACHABILITY rather than at a tool's inputs**, and it
is worse in one specific way: the neighbour case fails **loudly, elsewhere**,
while this one fails **silently, here** — deleting the last example that imports
the tier removes the tier from the build and **nothing in the gate set notices,
because the gate did not change.** The pointer list would record this rung as
green and pointed on the day it stopped running.

**So the enumeration owes one more question after "what is it pointed at":
WHAT MAKES IT RUN?** A gate whose answer is *"another file's import"* is
**held up by something that was not written to hold it.** The fix is with the
owning lane — one line, next ticket; **the shape is the register's.**

**AND THE DRIFT FAMILY'S MISSING CASE: THE GUARDED ARTIFACT LEGITIMATELY
CHANGING** (Wasm, `6bd3ca1`). O5's prerequisite `ais_empty_typing` **is one of
the six broken baseline declarations** — errors **371 and 380** live inside its
**295–412** span — so repairing it **takes the pin 6 → 4**. The lane **declared
the future baseline change BEFORE writing the fix.**

> **A pin move is DRIFT or a DELIBERATE CHANGE, and the only thing that
> distinguishes them is PRIOR DECLARATION plus NAMED DEPARTURES.**

**This completes the family.** §5.4b already had *a guard that never fires*, *a
guard that always fires*, and *a re-baseline that must report no published fact
moved*. All three assume the guarded artifact **should not** move. This is the
case where **it should** — and after the fact, a legitimate repair and a silent
regression **produce the same diff in the baseline file.**

**Declaration is what converts one into the other**, and it is cheap **only
before**: afterwards, *"that change was intended"* is unfalsifiable and arrives
from the one person with a motive. **Name the departures, then make them** —
which is the re-baseline norm's second half (§5.4b) moved from *report what did
not move* to *predict what will.*

**AND THE MOMENT A GATE MOVES UP THAT LADDER IS A DECISION WITH A BILL
ATTACHED** (SV, `b499afa`; instance found while wiring the round-trip gate
`ea6f667` made unconditional):

> **AN UNCONDITIONAL BYTE-COMPARING GATE INHERITS EVERY UNPINNED INPUT OF THE
> ARTIFACT IT COMPARES. Arming the gate arms the pins it does not have.**

The mechanism is that a **byte comparison has no tolerance**, so it silently
promotes every input of the compared artifact into a **pin requirement**.
Measured: all **21 SV envelopes stamp pyslang's POINT version**, `ci.yml`
installed it **unpinned**, and the newly-unconditional `sv_round_trip` would
therefore **turn every PR red at pyslang's next release** — *for a reason
unrelated to anyone's change.*

**It is green today only because the resolver happens to match**, which is not
the same thing as being pinned:

> **A green that holds because nobody has released yet is evidence about the
> WORLD, not about the pin.**

**AND THIS IS MEAS-9's DUAL, which is why it belongs beside it.** A gate that is
a permanent SKIP is *a check pretending*; a gate that goes red **for reasons
unrelated to the change** is a check being **ignored** — it trains a team to
re-run rather than to read, and it burns the credibility of every honest red
beside it. **Both failures are the same defect — the gate is not about the
change — pointed in opposite directions**, and arming an under-pinned gate is
how a tree moves from the first to the second in one commit.

**THE COMPOUND, and it is the part worth a cadence change: A FLAGGED WART PLUS
A NEW GATE IS AN ARMED BOMB.** The half-applied family stamp was **already
recorded** in the lane's own dormancy note — *"DONE for the census; the
envelope still stamps 11.0.0"* — an honest, correctly-filed, entirely dormant
wart. It stayed dormant only while nothing compared those bytes unconditionally.

> **Arming a gate re-prices every deferral the artifact is carrying. Re-read
> the DORMANCY RECORDS before a gate goes unconditional** (§9.7).

Disposition, recorded so the interim is not mistaken for the fix: an **interim
pin** (`pyslang==11.0.0`, **marked temporary**) is dispatched to the tools lane,
and the **durable fix** — a **family** stamp plus regeneration, **validated by
the same gate** — rides the SV lane's Landing A. *A pin is a schedule, not a
design; the design is the artifact not caring about the point release.*

**AND THE SHARPENING THAT RELOCATES THE OBLIGATION** (QoL, `582529d`;
`docs/backlog/qol.md` `2026-08-23-qol-43`). The unpinned input was **harmless
for as long as the gate sat unwired**. Nobody edited it; nothing about it
changed; what changed was that something started **comparing** it.

> **Wiring a comparison changes the blast radius of inputs NOBODY EDITED — so
> the PIN AUDIT belongs to the ARMING COMMIT, not to the gate's author.**

That is the useful reassignment, because the gate's author is the person least
able to see it: they wrote a correct comparison, and the defect is in a
`ci.yml` install line they never touched. **The arming commit is where the two
facts meet**, and it is the only commit in which both are visible.

**And it has a checkable form**, which is what keeps it from being advice — for
each **unconditional comparing** gate, `--gate-set` asks:

* does the **compared artifact embed a version string**? and
* is that version **pinned at every install site** — **both arms of any `||`
  fallback**, since the second arm was unpinned here too?

The `||` clause is the part discovered rather than designed: a fallback install
path is an install site that **only runs when the first one failed**, which is
exactly when nobody is watching. **A pin audit that reads only the happy path
audits the arm that was already fine.**

**A SMALL INTERFACE LAW FROM THE SAME INCIDENT, minted against a line twenty
minutes old: THE SKIP BRANCH'S INSTALL HINT WAS ITSELF UNPINNED.** The gate
skipped politely and told the reader how to enable it — with the **unpinned**
command.

> **A hint is an INSTRUCTION, and an instruction that reproduces the defect IS
> the defect.**

So **error and skip messages that tell a user what to run are part of the
gate's surface, and are audited with it.** A message is not commentary on the
tool; for the reader who follows it, the message *is* the tool. This is §5.4's
argument-parser rule pointed at the other end of the interface — **the refusal
path is a surface in both directions: what it accepts, and what it tells you to
do next.**

**AND ONE NOTE LEFT STANDING BY NAME, because it is another lane's document:**
`docs/sv-charter.md:138` carries a **dated venv measurement** that will quietly
stop being true. It is **flagged to the SV lane through the register** rather
than edited across lane lines (§9.5a) — naming it here is the durable half, and
the edit is theirs to make. **A dated measurement in someone else's document is
NAMED, never corrected in passing**: correcting it silently would take a record
of their moment and make it a record of mine.

**AND A CONVERGENT NOTE ON WHY THE SV LANE KEPT ITS NEW LEMMAS OUT OF THE
GLOB**: an unverified `rfl` inside `LeanModels/` would have turned `lake build`
red, *"and a red build means the gates never run — which would have cost the
proof evidence as well as the build."* The Wasm lane reported the same shape
from the other side (its fork build *"when red hides every gate behind it"*,
`886ede9`). Two tiers, independently:

> **A RED BUILD IS NOT ONE FAILURE — IT IS AN OUTAGE OF EVERY GATE BEHIND IT.**

Which makes *build-red* a **gate-set** event rather than a build event, and
makes staging an unproven definition outside the glob a **gate-preserving**
move rather than timidity.

**A GATE THAT CAUGHT ITS OWN AUTHOR ON ITS FIRST RUN (`6b91a8d`) — and the
shape of the failure is the reusable part.** A new census gate compared the
model's `class` field against `refusal_census`'s `WHITELIST_CLASS` and produced
**109 confident `DRIFT` lines**. Every one was the same conflation:
`WHITELIST_CLASS` names **which GAP** a row is; the model's class names **what
KIND** of refusal it made.

> **TWO FIELDS WITH THE SAME NAME ARE NOT THE SAME FIELD.**

Seven further lines flagged boundary-freeze refusals for **lacking a class the
same commit's own documentation says they must not have** — *a gate
contradicting its own specification.*

> **THE TELL IS THE UNIFORMITY, NOT THE COUNT. A check that suddenly convicts
> most of a corpus is far likelier to be reading the wrong column than to have
> found a systemic bug.**

A systemic bug in a mature corpus is **ragged** — it hits the rows that share a
cause and misses the rest. **Uniform, confident, and everywhere is the signature
of a MISREAD, not a discovery**, and the instinct it should trigger is *"which
column am I actually comparing?"* before *"how did this get so bad?"* Note the
direction: this error was **alarming**, not flattering, which is the only reason
it was chased on sight (MEAS-12's asymmetry, again).

**AND THE ARGUMENT FOR LANDING IT AS A `--gates` ADDITION RATHER THAN SHIPPING
IT UNEXERCISED:**

> **An unexercised gate is not a gate; it is a claim.**

The same rule as *a check that has never failed is a design, not a control*
(§5.4), sharpened by the best possible instance — **its first real run convicted
its author**, and the two defects it surfaced were both **in the gate**. A gate
whose first execution is on someone else's landing has been tested by nobody.

**AND THE MIRROR OF THE VACUOUS GATE, measured by a lane on its OWN guards at
standdown** (Lean tier, `38766b4`, on master). **Two of four fired, and both
were self-inflicted**: the baselines were pinned to **the lane's own branch
commit** (`71829bf`), so **every future commit would re-fire them.** The
obligation census drifted **raw 138 → 141 with real 113 → 113** — the movement
was the lane's own docstring prose in `ProjParam.lean`.

> **A GUARD THAT ALWAYS FIRES IS EXACTLY AS USELESS AS ONE THAT NEVER CAN.
> Either way the lane learns to ignore it, and the drift it was watching for
> arrives unnoticed.**

**AND THE LADDER HAS NOW BEEN TRAVERSED END-TO-END INSIDE A SINGLE RED, which
is the strongest thing this section can show** (SoftFloat, `9e3c235`). **The
drift guard that fired was the lane's OWN, on the lane's OWN edit.**

> **A drift guard firing on its own author's edit is the guard WORKING.**

The full arc, in order: **the guard fires → the first hypothesis is WRONG → a
rule is extracted from the measurement → the rule SELF-VALIDATES against seven
prior hand resolutions → the self-test is extended to include the exact
defect.**

**Every rung of that arc is a law in this document, and they were traversed
without anyone consulting the document.** That is the convergence standard
(§9.3) at its most useful: not two lanes agreeing on a decision, but **one lane
independently walking a path this register had already mapped** — which is what
distinguishes a set of laws that describe practice from a set that merely
records incidents.

**AND THE DIRECTION OF THE REPAIR IS THE PART TO CHECK IN FUTURE INSTANCES.**
The repair **strengthened the instrument** — a rule, a self-validation, a new
self-test row — rather than **suppressing the row.** The suppressing repair was
available and cheaper at every step: widen the filter, drop the candidate, mark
the row known-noisy. **The tell that an instrument ladder is being climbed
rather than dismantled is that the self-test gets LONGER at the end of it.**

**AND THE SILENT-INSTRUMENT SHAPE REACHED THE ONE FLAG WHOSE PURPOSE IS TO
WIDEN A CLAIM** (crunga Rung A). `--build-target` is a **SILENT NO-OP** —
parsed in the arg loop, and **the initializer resets it afterwards.**

> **A WIDENING FLAG THAT SILENTLY DOES NOTHING PRODUCES AN HONEST LANE MAKING A
> FALSE COVERAGE STATEMENT.**

**Third instance of the silent-instrument family, and the worst-placed one.**
The others made a check weaker than believed; this one **makes a CLAIM larger
than the run** — the lane asked for more coverage, was told nothing, and
reported the coverage it asked for. *An honest lane plus a silent widener
produces a false statement that no one in the chain intended.*

**And the self-test could not see it because it exercised the FUNCTION, not the
FLAG PATH** — **caption-versus-picture in a different tool, in the same week.**
The row proved the thing the flag *would* have called; **nothing proved the flag
called it.**

**AND THE GAP IT CAUSED WAS CLOSED, NOT CARRIED.** The unbuilt importer **was
elaborated under A17 after the green**, and recorded **as what it is — a
different check from a build.**

> **The honest-disposition ladder applied to a coverage hole: close it if you
> can, and if the closure is weaker than the thing it replaces, SAY WHICH
> CHECK YOU RAN.**

**The available alternative was to carry it as a known gap** — legitimate, and
strictly worse here, because the closure was cheap. *A gap carried is a debt; a
gap closed by a weaker check is a measurement with a stated scope.*

**AND A NEW INSTRUMENT'S FIRST ASSIGNMENT IS REPRODUCING A NUMBER THE TREE
ALREADY DEFENDS.** The Python mirror said **156 call sites** until it
reproduced the landed **`indirectCalls == 19`.**

> **An instrument earns a NEW number by first reproducing an OLD one that is
> already gated.**

**Because a new instrument's first output has nothing to be wrong against.**
Every calibration law in this register so far has been about **predictions
scored later**; this is the cheap version available immediately — **a
already-defended number is a fixed point the instrument either hits or does
not**, and the 156 was not a small error, it was a different question being
answered confidently.

**AND THE SIMPLEST WAY OF ALL, SELF-CAUGHT: A CHECK WIRED WITH `;` INSTEAD OF
`&&`** (SoftFloat, corrected in `1b526bc`; verify at landing). The
verify-then-push chain **printed `DRIFT` and pushed anyway.**

> **A CHECK WHOSE FAILURE DOES NOT STOP THE NEXT STEP IS NOT A GATE — IT IS A
> COMMENT.**

**AND THE CHEAPEST MEMBER OF ALL, one step earlier: THE CHECK THAT WAS NEVER
INVOKED** (SV's red). The lane's **own clash checker** — built after one red,
**vindicated at the next landing** — **was not run on the new file**, and **five
of six errors were the one collision it detects in seconds.**

> **A CHECK THAT EXISTS AND ISN'T RUN IS NOT A CHECK; IT'S A NOTE ABOUT A
> CHECK.**

**The stuck-channel family's members all fail while running**; this one **never
starts**, and it is the only member with **no artifact at all** — no green, no
red, no line in a log. *Its absence is indistinguishable from a session in which
the check was never written.*

**And the aggravating detail is that the tool had already PROVED itself**: the
checker was not speculative, it was **vindicated** — which is precisely the
condition under which a lane stops thinking about it. *A tool that has worked
becomes invisible faster than one that has not.* **The cure is the gate set, not
the memory** (§5.4b's ladder: a check at `declared` is not at `called`).

**AND ONE STEP LATER STILL — THE CHECK THAT RAN, POINTED AT THE WRONG SUBJECT**
(C, `b57e983`; the lane's own red, owned with its law). The fast loop **was
invoked**: it verified **the small edit** and **skipped the rewrite.**

> **THE FAST LOOP IS ONLY WORTH WHAT YOU POINT IT AT. A cheap check run on the
> file you were LEAST WORRIED ABOUT is a cheap check you did not run.**

> **A CAPABILITY IS NOT A PRACTICE.**

**This member leaves the family's worst artifact, not its best.** The
never-invoked check leaves **no green to mislead anyone**; this one leaves **a
green that is true about the wrong file.** *An unrun check is silent; a misaimed
check testifies.*

**And the misaiming is ANTI-correlated with risk by construction, which is why
vigilance is the wrong cure.** A lane points a cheap check where it feels
uncertain — and **the rewrite is the edit it has just finished thinking hardest
about.** *Confidence is manufactured by attention, so the file understood best is
the file verified last.* The fix is therefore **a rule about COVERAGE** — *every
file the tenure touched, cheapest check first* — **not a resolution to
remember**, which is the same conclusion the never-invoked member reached one
step earlier.

**AND A THIRD BITE FROM ONE CHECKER GAVE THE FAMILY ITS GENERAL FORM** (pyc,
`79fcd3b`, queued). Three separate incidents, one mechanism:

> **A GREP-BASED EXISTENCE CHECK ANSWERS "IS THIS STRING HERE?" WHEN THE
> QUESTION WAS "IS THIS THING DECLARED?"**

**This is the always-fires member's precise cause**, and it explains why
tightening kept failing to fix it: each repair made the *string* harder to match
by accident while leaving the checker answering **the wrong question**. The
working repair changes the question — **require the `def` AND the `#guard`, and
STRIP COMMENTS FIRST.**

**The comment-stripping is the part that had to be learned by being bitten**:

> **ANCHORING ALONE IS INSUFFICIENT. `^\s*def` matches happily INSIDE A BLOCK
> COMMENT — which is exactly the deleted-declaration case.**

*A declaration commented out is the failure the guard exists for, and it is the
one shape where the guard's own evidence survives the deletion.* **So the
stripping is not hygiene, it is the check**: any existence check over source text
must first reduce the text to **the part the compiler reads.** *A grep sees a
file; a declaration lives in a language.*

**AND THE FIXTURE PROBLEM SOLVED ITSELF, WHICH IS WORTH COPYING** (same
landing).

> **The string proving the bug is the GUARD'S OWN NAME, sitting in the register
> file that names it.**

**A fixture that needs no fixture file, because the tree already contains the
counterexample.** *A synthetic fixture is a guess about what the wild case looks
like; a real-repo fixture IS one* — and it has the property a synthetic one
cannot buy: **it stays true as the repo changes, or it fails and tells you the
convention moved.** The general move is cheap and under-used — **before writing a
fixture, grep the tree for the pathological string**; a checker whose adversary
is *text this project actually writes* usually has its adversary already
checked in.

**AND A BLAST-RADIUS CENSUS HAS A SCOPE RULE OF ITS OWN, LEARNED ACROSS THREE
ATTEMPTS — TWO OF THEM ON THE LANE'S OWN CENSUS** (pyc's `except_builtin`, merged
`b5c63e8`).

> **A BLAST-RADIUS CENSUS MUST SPAN EVERY CORPUS THAT RUNS THE LANGUAGE — and
> this repo has THREE, IN THREE SHAPES.**

Typed-call files; **grammar witnesses as INLINE SOURCE STRINGS inside the census
tool itself**; and whole scripts. **Scoping to the file finds one; scoping to the
obvious corpus finds most; only all three finds them all.**

**The middle shape is the one that will keep being missed**, and it is worth its
own sentence: **source held as string literals inside an instrument is code that
runs, and no file-extension glob will ever see it.** *A census that enumerates
`.py` files is enumerating a FILESYSTEM CONVENTION, not the language's
occurrences* — which is the grep-versus-declaration defect above, met at corpus
granularity rather than at line granularity.

**And the standing form is a question, not a longer glob:** *where does this
language RUN in this repository?* **Answer it by naming the shapes — files,
embedded strings, generated text — and the glob follows.** *Two of the three
attempts were spent rediscovering that the instrument itself is part of the
corpus it measures.*



**AND A COUNTING RULE FOR WHICH PROSE TO PROMOTE** (SV, `$finish` layer-order).

> **PROSE REPEATED FOUR TIMES IS EXACTLY THE PROSE WORTH TURNING INTO A
> GUARD.**

The claim — `$finish` lives in `ρ` because `SvWorld.out` carries the verdict
line — became a **`#guard` whose inverted nesting reads `none`**: *the error
that would silently discard the answer every conformance test exists to
produce.*

**Repetition is the cheapest available signal that a claim is load-bearing**,
and it is one a lane already has: **nobody restates an incidental fact four
times.** This register has said *a claim needs a check* many ways; **this says
which claim to check first**, without a census — *count the restatements.*

**And the guard's content is the right one because it is the INVERTED nesting**:
not *"the layer order is as documented"* but **the specific wrong order, and what
it destroys.** *A guard that asserts the design passes when the design is
accidentally right; a guard that exhibits the catastrophe fails only when the
catastrophe is reachable.*

**AND A RULE ABOUT WHEN TO INSTALL A DISCRIMINATING GUARD** (C, `b57e983` —
**exit-as-oracle reads success only when every exit peels to a literal `0`**,
adopted after measuring that **all 36 qualify**).

> **THE TIME TO INSTALL A DISCRIMINATING GUARD IS WHEN IT HAS NOTHING TO
> DISCRIMINATE.**

The guard **costs nothing today** — it excludes no test — so it is adopted
**because it makes the reading honest rather than lucky**, with no case pending
and no interest on the other side. **Installed later, the IDENTICAL guard arrives
as a breaking change with a constituency against it**: it now *subtracts from a
published number*, and the argument about whether `exit(f())` ever meant what
`exit(0)` means gets held **in front of the row it would delete.**

**This inverts the usual instinct, which is to write a guard when something slips
past it.** *A guard adopted at zero cost is adopted on principle; the same guard
adopted at a cost is adopted against an interest* — and **the second conversation
is decided by the size of the number, not by the soundness of the reading.**

*Free is not the same as unnecessary.* **A guard with nothing to discriminate is
a guard whose price has not arrived yet** — the same trade §5.0a already makes
with declared divergences: **register the debt while naming it is still
cheap.**

**AND THE SHARPEST TARGET AN ACCEPTANCE TEST CAN HAVE IS THE MODEL THAT READS
ALMOST THE SAME AND IS WRONG** (SV's `slotStep`, in tenure).

> **The loop is a RECURSION, not a sequence. A one-pass-per-region model reads
> almost identically and drops §4.4's iteration rule EXACTLY.**

**Point the gate at the near-miss, not at the design.** A test written against
the intended semantics passes for both models — *the wrong one satisfies every
property the right one has, minus the one nobody thought to state* — so the only
discriminating test is **the one built from the wrong model's specific
consequence.**

**And this is the inverted-nesting guard's rule generalized from a guard to a
MODEL.** *A guard that exhibits the catastrophe fails only when the catastrophe
is reachable*; here the catastrophe is **an entire alternative reading of the
spec**, and the acceptance test's job is to be **the sentence that distinguishes
them.** *When a lane can name the wrong model, the test writes itself; when it
cannot, a green means the lane and the code agree — which was never in doubt.*

**AND EVIDENCE-ISOLATION AS A TICKET-COMPOSITION PRINCIPLE** (SV, same tenure).
The new `Prim.lean` was **held OUT of the build and elaborated via gates**, so
**a red build could not take the retirement evidence down with it.**

> **Compose a tenure so that its EVIDENCE does not share a failure domain with
> its RISK.**

**This is *a red build is an outage of every gate behind it* used in advance
rather than diagnosed after.** The lane had two things in one tenure — a risky
addition and the proof that a debt was paid — and **put them in different
failure domains on purpose.** *A tenure carrying both a bet and a receipt should
not let the bet decide whether the receipt is readable.*

**AND A GUARD SPLIT BY WHAT EXISTS AT THE MOMENT OF THE QUESTION** (QoL items
12-14, merged `40c093c`).

> **A REPORT HAS NOTHING TO SPEND, SO IT HAS NOTHING TO GUARD.**

The plan guard was refusing the tool's **own report mode** — and the fix is not
an exemption but a **re-derivation of what the guard is for**: it protects a
*commitment of resources*, and a report commits none. **With the lane's own spec
still validated in report mode BECAUSE IT IS DISPLAYED THERE** — which is the
half that keeps this from being a hole: *the guard follows the resource, and the
validation follows the claim, and they are different questions asked of the same
invocation.*

**AND ITS SECOND GENUS-MEMBER, SELF-REPORTED: A RETRY LOOP THAT REBASES MUST
RE-RUN THE CLOSURE CHECK ON EACH NEW BASE** (ES, pushed `c49c244`+`6e85d56`).
The fetch-rebase-push loop **re-based without re-running the transfer test**,
pushing atop **Core's 183-insertion seam lift on a stale check.** The lane's own
words: *"low risk, established afterwards, is not the transfer test."*

> **A LOOP IS A CHAIN, AND EVERY ITERATION'S GUARD MUST RE-FIRE — or the loop
> silently converts a VERIFIED push into an UNVERIFIED one.**

**Same genus as `;`-versus-`&&` and the more subtle member.** There the guard's
verdict was **never wired to the next step**; here it is wired correctly **and
computed against a base that no longer exists.** *The check ran, passed, and was
true of a tree nobody pushed* — which is the wrong-tree family (§5.4a-i)
arriving inside a shell loop, and it is invisible precisely because **every
individual iteration looks disciplined.**

**And the repair is the compliant shape**: the lane **fired a verification triad
on the pushed state** rather than leaving the gap open, or arguing it closed.
*A verification run after the fact does not restore the original guarantee — it
replaces it with a weaker, stated one, which is the honest disposition when the
stronger one has already been spent.*

**Every chain converted, and the corrective push itself `&&`-gated**, which is
the detail that makes it a fix rather than a repair.

**And the scope is the point: `tools/triad.sh` already gets this right.** The
defect lives in **ad-hoc shell chains that REIMPLEMENT a gate** — the wrapper is
disciplined, and every one-off `verify; push` written beside it is **a second,
undisciplined implementation of the same idea.** That is MEAS-28's duplication
law arriving in **shell control flow**, where the copy is three characters long
and does not look like a copy at all.

**It also completes this section's stuck-channel taxonomy from the cheapest
end**: a gate that never fires, one that always fires, a heuristic that always
answers safely, a negative row that passes on absence — **and now a gate whose
verdict was never connected to anything.** *The first four fail at deciding; this
one decides correctly and is not listened to.*

**AND A THIRD WAY A SIGNAL GOES DEAD, WITH THE PROPERTY THAT KEEPS IT ALIVE:
THE FAILURE THAT ONLY EVER COSTS TIME** (QoL `22ed755`). The tenure-class
heuristic hard-coded `{github,origin}/master`, so a fork whose default branch is
named otherwise **fell back to a full tenure** — *conservatively, therefore
silently.*

> **A HEURISTIC THAT FAILS CONSERVATIVELY IS EXACTLY HOW A HEURISTIC STAYS
> BROKEN: a full tenure every time and no one the wiser.**

**And the structural reason it survives is worth naming, because it is not
inattention:**

> **A failure mode that only ever costs TIME has NO CONSTITUENCY FOR FIXING
> IT.** Nobody is wrong, nothing is red, and the bill is paid in minutes spread
> across everyone.

**This completes the stuck-channel family** — a gate that never fires, a guard
that always fires, and now **a heuristic that always answers the safe way.** All
three carry **zero information**, and this one is the hardest to retire because
its symptom is **indistinguishable from correct caution.** The fix was to
**ask the remote which branch is its HEAD** rather than to guess better: *a
heuristic with a fallback nobody can see should be replaced by a question
somebody can answer.*

**It is MEAS-35's mirror, exactly**: the audit's defect class was *a `--compare`
that cannot exit nonzero*; this is **a `--compare` that cannot exit zero**. The
two failures look nothing alike — one is silent, one is noisy — and they end in
**the same place**, because a signal that is constant carries no information in
either direction. **A gate is a channel, and a channel stuck at one value is
off.**

**THE FIX NORM, and its second half is the part that keeps re-baselining
honest.** Baseline against **upstream**, never against yourself: `git worktree
add` gives a pristine master checkout (**2.1 MB**) without touching the branch,
and the correspondence now records **`e0e3f6bcccb8`, upstream master**, as its
base rather than one of the lane's own commits.

> **The re-baseline corrected WHAT THE GUARD WATCHES, not what we measured.**

**State that check as part of the norm, because re-baselining is the one repair
that can silently erase the finding it was meant to report.** *"We moved the
baseline"* and *"we moved the goalposts"* produce identical diffs, and only a
published comparison separates them. Here it is published: **no fact moved** —
`rules_by_relation` unchanged (**STUB 17**, so the *24%-maps-to-a-stub* headline
holds), **113** real obligations, **24** proof-layer.

> **A re-baseline is complete when it names what the guard now watches AND
> reports that no published fact moved. Without the second half it is
> indistinguishable from making a red go away.**

**AND A THIRD MEMBER OF THE never-executed FAMILY, from the same standdown:**
*a check that has never failed is a design, not a control* (§5.4); *an amendment
that has never fired is a design, not a control* (§7.1a); and now —

> **A DUTY THAT HAS NEVER BEEN EXECUTED IS A PLAN, NOT A DUTY.**

Which is why the lane's first act on entering WAITING was to **run** the guards
its waiting depends on, and why running them is what found the defect.

**AND A THIRD WAY A CHECK CAN BE HOLLOW — THE NEGATIVE ROW THAT PASSES BECAUSE
NOTHING RAN** (QoL, `ccdc839`; caught live, in the lane's own self-test).

> **A ROW ASSERTING THAT SOMETHING DID **NOT** CHANGE PASSES WHENEVER THE CODE
> NEVER RAN. It needs a SIBLING asserting the code DID.**

Measured: the sentinel row passed because `class_hint` was defined **after** the
self-test, so the call was **command-not-found** — and a variable that was never
touched is, trivially, unchanged. **Only its output-expecting siblings failed
(rc 127), and that is what exposed it.**

**The shape is §5.3's vacuity ruling inside a self-test**: *a check must not
report sameness where there was no content* — and a negative assertion is the
one row for which **absence of content is indistinguishable from success.** So
negative rows are never landed alone:

> **Pair every "did not change" with a "did happen". The positive row is what
> proves the negative row was watching.**

Note the ordering hazard that produced it, which is generic to shell: **a helper
defined below its caller does not exist yet**, and the failure arrives as a
missing command rather than as a wrong answer — loud in the siblings, silent in
the row that mattered.

**AND THE POINTER LIST APPLIES TO A TEST SUITE, WHICH IS WHERE IT IS HARDEST TO
BELIEVE** (QoL, `2b3d608`, on master). **Two bugs shipped past 27 passing unit
rows**, and the topology says why in one line:

> **The rows tested `record_green`'s ARGUMENTS, not what the CALL SITES pass.**

Every row was pointed at the function; **no row was pointed at the seam.** So
the suite could be exhaustive about the callee and blind to the caller, and
**the end-to-end run was the only thing that could see it** — which is §5.4b's
own claim (*a claim no gate points at is ungated, however green the
neighbourhood*) arriving in the place a lane is least likely to audit, because
**27 green rows read as thoroughness.**

**This is the fixture-vs-reality family at the INTEGRATION SEAM**, beside *a
fixture is not enforcement* (§9.7) and *a fixture is not a tool* (above): a unit
row supplies its own arguments, so **it tests the function against the author's
belief about the call**, not against the call. **Where a suite's inputs are
authored, the suite's coverage stops.**

**AND THE RIDER, which is absence in a new costume:** `targets=` came out
**EMPTY for a full build**, because `sed 's/^$/all/'` **does not fire on empty
INPUT** — *there is no line for it to match.* A substitution that rewrites an
empty **line** is not a substitution that rewrites empty **input**, and the two
are indistinguishable in the pattern.

> **A transform on nothing produces nothing, and reports success doing it.**

**AND THE FAMILY GAINED ITS PUREST MEMBER: A FIXTURE MISSING THE DECLARATION THE
FEATURE READS** (QoL, same tenure). The fixture's lakefile **declared no
`lean_exe`**, so the runner-naming row **passed and failed for the wrong
reason** — *the feature under test had nothing to read, and the row reported on
its absence.*

> **A FIXTURE MISSING THE DECLARATION THE FEATURE READS TESTS THE FEATURE'S
> BEHAVIOUR ON AN EMPTY WORLD, and reports it under the feature's name.**

**This is the vacuity family (§5.3) inside a fixture** — and it is worse than a
vacuous theorem, because **a fixture's verdict is a colour rather than a
statement**: nothing in a green row records which world it was green about.
*The cheap standing check is the one the tier already applies to censuses:*
**make the fixture FAIL first**, since a fixture that cannot be made to fail by
breaking the feature is not testing the feature.

**AND THE SAME DEFECT AT SIMULATOR SCALE, WHICH IS WHERE IT IS MOST EXPENSIVE**
(SoftFloat's sim, re-ticketed `ea69b8f`; **the coordinating role's rename
hypothesis was the fourteenth killed by lane measurement** — the cause was
SCOPE). The finding is not the cause; it is that **the verification method was
UNSOUND**: the concatenation sim **merged open scopes**, *supplying the very name
the real module lacks.*

> **THE SIM ERASED THE BOUNDARY AND WAS TESTING A FILE THAT DOES NOT EXIST.**

> **A SIMULATOR MUST PRESERVE THE BOUNDARIES IT SIMULATES.** A cheap stand-in
> may drop cost; it may never drop STRUCTURE, because the structure is what the
> question is about.

**Concatenation is the canonical example and every tier has one** — a merged
namespace, a flattened import graph, a single translation unit standing in for
several. *Each is fast precisely because it removes the seam, and the seam is
where the defects live.* **A stand-in that removes what the real artifact
enforces does not approximate it; it answers a different question quickly.**

**AND THE FIXED INSTRUMENT WAS VALIDATED IN BOTH DIRECTIONS, WHICH IS THE ONLY
WAY A REPAIRED CONTROL EARNS TRUST** (same landing). The old sim **passes the
broken code**; the faithful sim **reproduces the triad's exact 8.**

> **A CHECK THAT HAS NEVER FAILED IS A DESIGN, NOT A CONTROL.**

*Reproducing the known failure is the half lanes skip*, because a green on
correct input feels like the check working — **and it is exactly the observation
a check that cannot fail also produces.** **Both directions, or the instrument is
an assertion about itself.**

**AND THE INCIDENT ARGUES FOR ONE ROW THIS FAMILY'S INSTRUMENT INVENTORIES DO NOT
CARRY:** *"the triad was the only instrument pointed at the REAL artifact — which
is why that red was worth its tenure."*

> **AN INSTRUMENT INVENTORY MUST SAY WHICH INSTRUMENTS COMPILE THE ARTIFACT AND
> WHICH COMPILE A STAND-IN.**

**Speed and fidelity are inversely arranged in every inventory this family has**,
so the fast instruments are the ones a lane runs and the faithful one is the one
it defers — *and a fleet of green stand-ins reads exactly like a verified
artifact.* **The expensive instrument is not redundant with the cheap ones; it is
the only one whose green is about the thing being shipped.**

**AND THE FIXED INSTRUMENT WAS LOAD-BEARING ON ITS FIRST USE, WHICH IS THE
VALIDATION A REPAIR ACTUALLY WANTS** (SoftFloat, same thread). The new lemmas
**need exactly the name the old merged sim handed over for free.**

> **AN INSTRUMENT FIX IS VALIDATED BY ITS FIRST CUSTOMER, NOT BY ITS OWN TEST
> SUITE.**

**The repair's own suite can only check the cases its author imagined; the first
real consumer checks the one property that mattered** — *that the thing the
stand-in was silently supplying is now genuinely absent.* **A fidelity fix is
confirmed the moment downstream work becomes harder in the specific way the
boundary predicts**, and that is a strange but reliable signal: *the correct
instrument makes more work, and the work it makes is the work that was always
owed.*

**AND ITS COUNTERPART AT THE OTHER EXTREME: A TRANSFORM ON TOO MUCH, REPORTING
SUCCESS JUST AS QUIETLY** (pyc, `fcb1463`). A **non-greedy regex bounded by a
blank line** silently removed **TEN witnesses instead of one** — caught **only
by a printed count.** The fix **bounds by the next top-level call** and
**asserts `delta == −1`.**

> **A STRUCTURAL EDIT NEEDS A STRUCTURAL BOUND AND A COUNTED CHECK.**

**A blank line is a typographic accident, not a structure**, and every
regex-bounded edit is making a claim about a file's shape out of **whatever
punctuation happened to be nearby.** A structural bound — *the next top-level
call* — is a claim about the **language**, which reformatting cannot silently
invalidate.

**And the counted check converts the bound from a hope into a measurement**:
`delta == −1` fails on **both** directions of the same error — removing too many
**and** removing none — which is the paired-guard law arriving at a text edit.
*An edit that reports only "it ran" has told you about the tool, not about the
file.*

Every member of the absence family has now worn a different costume — a `null`
measured on an absent repo, a zero-row census, a negative self-test row that
never ran, and now a `sed` with no line. **The constant is that the empty case
takes the success path**, so the check is always the same: **name what the
non-empty case would produce, and assert that.**

**AND A VOCABULARY RULE THIS SECTION NEEDS, because it counts things: A
PROCEDURE IS NOT A GATE.** The tier's arena check is **recomputed by hand** from
a downloaded `results.json`, with **no `--compare` and no committed baseline**.
It **caught real movement** (nightly **66/67 → 67/67**), so it earns its place —
but calling it a guard **overstates it**.

> **A procedure earns its place by what it CATCHES; a gate earns its name by
> what it RUNS. Instrument it, or rename it.**

**The reason this is not pedantry is enumeration.** §5.4b's pointer list is
**counted**, and a procedure counted as a gate puts a row in the list that
**nothing executes** — it does not even reach `DECLARED` on the ladder above,
because there is no declaration for an enumerator to find. **A gate set padded
with procedures reads as coverage and is staffed by memory.**

**AND THE DURABILITY DESIGN HAS ITS FULL FORM NOW, measured under a purge**
(Ada; §L86 collecting). The scratchpad purge took **ACATS, the ARM texts and
adatools** — and **every number was re-derived from git-tracked,
content-pinned census JSONs.** The partition is the design:

* **4 of 5 instruments SELF-TEST PASS with no corpus** — they do not need it, so
  they do not fail without it;
* **the one that does need it REFUSES LOUDLY, with the acquisition path** — so
  its absence is a stated gap that names its own repair.

> **PARTITION INSTRUMENTS BY CORPUS DEPENDENCE. The ones that do not need the
> corpus must not fail without it; the one that does must name its own
> re-acquisition.**

**Both halves are required and they are usually confused.** An instrument that
*could* run corpus-free but reads the corpus anyway converts an outage into a
tree-wide red; an instrument that genuinely needs it and merely **skips** turns
an outage into **silence** (MEAS-9). **The purge is the test that separates
them**, and this is the first time this tree has had one run over a full
instrument set.

**AND THE CENSUS ARTIFACT PAID A DIVIDEND — a trap caught FOR FREE** (Ada inch
3, `1260af7`). The **zero-arg `AssocList`-as-leaf** trap is **inch 2's encoding
trap RECURRING**, and it was caught **from the census artifact** rather than
re-discovered.

> **Inch 2 paid to learn it once; inch 3 gets it free — which is what the census
> artifact is FOR.**

> **A census artifact's value includes EVERY FUTURE INSTANCE of the traps it
> recorded.**

**Which is the argument for the artifact over the finding.** A trap written into
a landing message is learned by whoever reads that message; **a trap encoded in
the census output is applied by whoever runs the census** — and the second
population is the one that keeps growing.

**AND THE WEIGHT IS NOT WHERE A READER WOULD GUESS.** **6.4.1 Parameter
Associations (51 ¶, 271 135 nodes)** outweighs **Subprogram Calls (32 ¶)** and
**Returns (35 ¶)**:

> **The work is in the ARGUMENTS, not the CALL.**

**And BOTH standing-empty refusal classes** — `orderDependence` and
`undefined`/Erroneous — **get their first real sites at the same subclause,
exactly as inch 2's statable-empty predicted.**

> **A gate empty FOR A STATABLE REASON named, in advance, the inch that would
> fill it — and the prediction is now fulfilled.**

**That is the statable-empty disposition earning its keep.** An empty gate
recorded with *"the subject is refused elsewhere"* is a **pointer forward**; the
same gate recorded as *"no content yet"* would have been **rediscovered from
scratch** when the sites arrived. *The difference is one sentence at the time,
and a whole re-derivation later.*

**AND A +0 STATED ACROSS A MULTI-INCH CHAIN, with a NECESSITY argument.** Inches
**3, 4 and 5 are each NECESSARY and none SUFFICIENT**; the row moves at **6** —
and **each inch's zero is pre-stated.**

> **The `+0`-in-plan control extended from one inch to a CHAIN: every rung
> discloses its own zero, and the chain discloses where the number moves.**

**Which is the only honest way to run three consecutive zero-reach inches.**
Each one alone looks like a lane not delivering; **the necessity chain is what
distinguishes three inches of no progress from three quarters of a rung** — and
it is falsifiable, because *if the row does not move at 6, the chain's claim was
wrong and the plan owes an explanation.*

**AND A GATE CAN BE EMPTY FOR A STATABLE REASON, which is a fourth thing an
empty gate can mean** (Ada inch 2). The `orderDependence` gate **has no
content** — because **the only effectful form is refused calls** — and it is
recorded **with the reason AND the debt**: inch 3 owes the answer.

> **"Empty for a statable reason" is a THIRD kind of zero at a gate**, beside
> *empty because the corpus does not reach it* and *empty because the API cannot
> build it* (§5.2). This one is **empty because the subject is currently
> refused elsewhere.**

**And it is the only one of the three that RETIRES BY SOMEONE ELSE'S WORK** —
the gate fills when the refusal that hides its subject is lifted. **So the debt
belongs on the refusal, not on the gate**, and a lane reading the empty gate
without the pointer would price the wrong inch.

**AND A14 APPLIES TO A DEFERRAL, NOT ONLY TO A TENURE** (Ada). The spine import
waits because **`swap` fails the line by 8× while `load` passes** — *both
required, both measured* — and the deferral is recorded as **POINTED-vs-DECLARED
still open** (§5.4b's ladder), riding the next quiet window.

> **A deferral carries its LADDER POSITION for the same reason a law does: "we
> will do this when the machine is quiet" is a plan; "declared, not yet pointed,
> waiting on A14" is a state with a trigger.**

**Two measurements and not one is what makes it a deferral rather than an
excuse** — a single failing number would leave open whether the whole move is
infeasible; **`load` passing and `swap` failing localizes the blocker to one
half**, which is what a later lane needs to know whether the window has arrived.

**AND THE HONEST GAP BESIDE IT, recorded rather than glossed**: the spec census
**cannot run** — its LaTeX corpus was purged — but **its baseline is committed
and its instrument is pinned, so re-fetching restores it.** *"Armed and not
runnable, and here is what restores it"* is the provenance remedy (§5.4a)
applied to a gate: **a gate that cannot run today is a stated gap; a gate
quietly dropped from the list is a coverage claim.**

**COROLLARY — AN EXPECTED-TO-FAIL ARTIFACT IS THE WEAKEST GATE IN ANY SET**,
because its verdict is invariant under everything the file says. A file expected
to error is green while it errs, whatever it errs *about*, and whatever prose
surrounds the failing rows. **So pin the COUNT** — SoftFloat now pins **two** on
`probe_es_unblock` and **nine** on `probe_walls`, and the count is the only part
of an expected failure that moves when the file does.

**AND THE CLEANEST LIVE DEMONSTRATION THIS SECTION HAS — a red build in which
the thing that mattered went GREEN** (Wasm, `f657041`, on master). O1 is proved,
with **four pinned predictions and four matches**. The build was **red**, and:

> **The build is red and the thing that matters went green; ONLY THE PINNED
> COUNT SEPARATES THEM.**

Without the pin, that landing has exactly two readings — *"the build is red, so
nothing is known"* and *"the failures are the expected ones"* — and **no
artifact distinguishes them.** With the pin, the red is **partitioned**: four
predictions were made in advance, four matched, and whatever else is red is
outside the claim. **That is the whole value of pinning a count, demonstrated
positively rather than as a near-miss.**

**AND THE COMPLETE EXHIBIT ARRIVED TWO INCHES LATER — the pin catching BOTH
DIRECTIONS across consecutive tenures** (Wasm O3, `fd96fce`, on master).

**Exit code was `1` on ALL FOUR tenures.** Nothing in the exit status separated
*"the port went green"* from *"the port regressed"* from *"unchanged"* — only
the **pinned shape** did:

| tenure | pinned shape | verdict |
| --- | --- | --- |
| **85489** | `SubtypingPort` **errors**: 1 (arity) | **MISS** |
| **69357** | `SubtypingPort` **built**, 12 s, **0 errors** | **MATCH** |

**A guard that fires in only one direction is half a guard**, and this is the
first exhibit in the tree where the same pin **convicted and then cleared** the
same artifact across successive runs. If one table is wanted for *a drift guard
must baseline against the artifact it watches*, it is this one: the baseline is
`SubtypingPort` built/errors and the failing-module count, **not the tenure's
exit code**, because **the exit code was constant across every outcome the guard
exists to distinguish.**

> **When the ambient verdict is constant, EVERY bit of information is in the
> pin.**

**But the count BOUNDS the drift; it does not IDENTIFY it.** Two errors a probe
was built to have and two it has acquired are the same number, so an
expected-error file carrying a transcription still owes the transcription
tripwire. Pinning the count is necessary and is not sufficient — and a control
whose sufficiency is assumed is the §5.4a failure one level up.

**RIDER — THE ANNOTATION NORM: A DATED RECORD IS ANNOTATED, NEVER REWRITTEN.**
The lane's fix reached a dated backlog entry (`2026-08-22-softfloat-1`), and it
**annotated** the entry instead of editing it:

> **The measurement was right as taken; only its tense was wrong.**

Rewriting would have destroyed the evidence for the very law being minted:
**that the text was TRUE WHEN WRITTEN is the entire finding.** A rewritten entry
reads as a lane that simply got it wrong, which is a different — and less
useful — story than a lane whose correct measurement expired in six minutes. The
split to carry:

> **Present-tense prose is FIXED. A dated record of a past measurement is
> ANNOTATED.**

This is the stamp discipline (MEAS-10) applied to the record rather than to the
number, and it is the same instinct that makes §7.1a's register carry two rows
marked **LOST** rather than two plausible reconstructions: *the remedy for a
provenance gap is provenance, never reconstruction* (§5.4a). A register, a
backlog entry and a census row are all dated records, and all three are worth
less the moment they can be silently improved.

**AND THE SAME SECTION'S RULES WERE BROKEN BY A SENTENCE REFUTABLE FROM THE LOG
IT WAS PRINTED IN** (pyc, merged; QoL item 16 landed the fix). **1 056 axiom
lines sat ABOVE the words "NO Lean was elaborated."**

> **The CLASSIFICATION drove the coverage sentence while the GATE LIST drove the
> work, and the two were never reconciled.**

**Two derivations of one fact, diverging silently** — the defect this register
keeps meeting as *the model always matches the code*, arriving in a place with no
compiler to notice. **And the safe direction is what made it invisible**: the
sentence understated, so nobody was harmed enough to file it.

> **CLAIMS-LESS ERRORS ACCUMULATE. A wrong statement that costs its reader
> nothing is a wrong statement nobody will report.**

*This is the counterpart to the false-positive asymmetry below* — a gate that
over-fires is reported within the hour by the lane it accuses; **a report that
under-claims is reported by no one**, and the two failure modes therefore have
completely different discovery times. **A number that can only be too low still
needs an owner.**

**The fix is the shape to copy, and it has two halves.** The sentence now
**derives from WHAT RAN**, and the classification-time sentence is **LABELLED A
PROJECTION** — *nothing has run at that point.* **Neither half alone would have
worked**: deriving from the run leaves the early sentence lying, and labelling
alone leaves two derivations in the tree. *Where a fact is stated at two times,
the later statement is the measurement and the earlier one owes a word saying it
is not.*

Incident and dispositions: `docs/backlog/softfloat.md` `2026-08-23-softfloat-11`;
this lane's landing, `docs/backlog/architecture.md` `2026-08-23-architecture-26`.


### 5.5 Coverage by clause — the manifest

Where a spec exists, the tier maintains **one manifest per (language,
edition)**:

    docs/<lang>-<ver>-clause-manifest.json

One row per clause the tier CLAIMS:

    clause        the edition's own number
    title         the edition's own title, verbatim
    status        stated | refused | out-of-tier | not-applicable
    declarations  the Lean declarations that realize it
    gates         the #guard / battery rows that check it
    layer         neutral | scoped        (which directory it lives in)

Coverage is `stated / (stated + refused + out-of-tier)`. It is
**generated and checked, never hand-maintained** — the tree already
demonstrates why (§2.5: three of five hand-written citations were an
edition out of date). For an algorithmic spec like ECMAScript's, `clause`
is the abstract operation and its step number; the shape is unchanged.

The manifest is the single artifact that serves three of this charter's
deliverables at once, which is why it is worth its cost: it is the
per-edition **reader's view** promised in §2.4, the **cross-edition diff
gate** that polices the neutral layer, and the **coverage-by-clause**
scoreboard. It starts at ~30 rows for C23's value layer and grows with the
tier.

**AND THE MANIFEST'S `status` COLUMN NEEDED A FOURTH VALUE AT THE ARM LEVEL,
SUPPLIED BY THE ES LANE'S SELF-DEMOTION** (`7ea36e7`, ticketed).

> **NOT EVERY REFUSAL IN AN ARM IS A BOUNDARY.**

An `internal-malformed` guard defends against **an AST that cannot occur**, so
counting it as a refusal reports a limitation the tier does not have. The
classification the lane landed is **STATED / PARTIAL / REFUSING**, with

> **PARTIAL OUT OF THE NUMERATOR.**

**And the reasoning is §5.0a's, one level down.** *Calling it stated claims a
construct the tier half-evaluates; calling it absent denies real work.* **A
half-implemented arm is a declared divergence at arm granularity** — it has a
site, a known difference, and a retirement condition — and the numerator rule
follows from the register's: **a debt is beside the number, never inside it.**

**The discipline generalizes past ECMAScript**: wherever a tier's unit of work is
smaller than its unit of counting, **the intermediate state exists and will be
rounded in one direction by whoever writes the table.** *Naming the third status
is what stops that rounding from being a matter of mood.*

**AND THE TABLE WAS MADE LOAD-BEARING RATHER THAN DESCRIPTIVE** (same landing).
The dedicated-clause table **verifies its handlers exist**:

> **Delete `evalCatchClause` and the file goes RED, rather than silently keeping
> the kind in the numerator.**

**A coverage table whose rows are load-bearing is the only kind that cannot rot
in the safe direction.** The usual failure is not a wrong row but **a row that
outlives its handler** — and nothing in a descriptive table notices, because a
table's rows are true about the day they were written. *Wiring the row to the
declaration converts the coverage claim from prose into a build dependency.*

**AND THE LANE THEN REMOVED ITSELF FROM ITS OWN NUMBER'S PATH:** *"from then on
§9.0 comes from the instrument rather than from me."*

> **A LANE THAT REPORTS ITS OWN COVERAGE IS A SINGLE POINT OF FAILURE IN ITS OWN
> SCOREBOARD. The fix is not more care; it is removing the lane from the path.**

*This is the register's oldest rule — the oracle writes its own column (§5.3) —
arriving at the one number the family reads most.*

---

### 5.6 SUITES drive SCOPE; ONE EXEMPLAR drives the PROOF LIBRARY

A tier needs corpora for two different jobs, and conflating them is how a
repository acquires pet programs. The split below is **measured, not
sentimental**, and it is §0.1's principle II — the library grows by demand
— given an actual selection rule.

**SUITES DRIVE SCOPE, because they walk the spec systematically and a
single program cannot.** The evidence is the C tier's own numbers, and they
cut against the program: `ctwin/sunfish.c`'s **accidental** 45-kind
vocabulary already clears **357 of 431 freestanding suite tests — 83%**
before a single construct is added. Read carefully, that is an argument for
the suite, not for the program: the suite finds *the same vocabulary* the
flagship happened to use **plus the remainder**, and it finds the remainder
in the standard's own order rather than in one author's. A driver program
can only ever discover its own vocabulary.

**The counter-evidence is in the tree too, and it is the Python tier.** Its
coverage grew **sunfish-shaped**: `>>`, `^`, unary `+` and `~` were absent
not because they were hard — they landed in the session that censused them
— but because nothing the flagship needed had asked for them, and three of
the four were *recorded as deferred in three different places*, none of
which was where a person looks to ask "which operators run?". It took
`print(5 ^ 3)` — a census, not a program — to find them. That is the cost
the completeness workstream exists to correct, and it is what scope-by-
driver-program buys you.

**THE CARVE-OUT, and it is why one exemplar is still required.** Suite
scoring exercises the **DEFINITION**: a verdict runs the interpreter and
compares an observable, and **no theorem is involved**. It therefore cannot
find a gap in the proof **LIBRARY**, because it never asks the library for
anything. Library gaps surface only under **deep end-to-end theorems about
one real program**, and every law this repository has minted traces to
exactly that:

* the **altitude lemmas** — prove it once at the chain with every operand
  symbolic — and their price tag, 259+ VCs unfolded against 12;
* **computed-shape / residue-spelling**: index premises must be spelled in
  the interpreter's own residue, not in the reader's preferred normal form.
  **`cbv` is the tactic for that residue** — a core tactic on the pinned
  toolchain (verified) that closes computed-shape goals which `grind`,
  `simp`, and `unfold`-then-`grind` all fail on, in **one token**. Its
  bound is `maxRecDepth` on heap-walking residues, so it is the right first
  attempt and not a universal one;
* the **vacuity catches** — a carried-over receiver shape makes every
  statement about it vacuous and cannot break a build;
* `Bracket.SubtreeWrites`, whose docstring records an arm **"UNINHABITABLE
  at the shipped code"** — a distinction only a real program's heap can
  draw;
* `settle_needs_futility`, a **countermodel** exhibiting the schedule that
  refutes the theorem-without-its-premise.

Not one of those could have come from a single-construct witness, and that
is not an accident of history: **single-construct witnesses are shallow by
design.** A witness that exercises one production establishes that the
production is reachable; it cannot produce a law about *composing twenty of
them under a heap*, because it never composes anything.

**AND A SEQUENCING DECISION EARNS A CENSUS THAT COULD HAVE OVERTURNED
IT.** Go's charter deferred concurrency; the walker census then found
concurrency constructs in **<1% of rung-1-reachable files** — **agreeing
with the decision, after the fact.**

The agreement is worth recording precisely because **it was a real test**:
the census was run after the decision, over the corpus, and **could have
come back the other way.** That is what separates it from the retrieval
family's failures (§5.4a) — *a grep that agrees with your prior* is
worthless when it could only ever have agreed; a census that **could have
overturned the plan and did not** is evidence.

> **A sequencing decision earns a census that could have overturned it.**

**AND THE EXEMPLAR WAS FOUND BY SEARCH, not by nomination** —
`bigmod.bitLen`, chosen on FIPS provenance, out of the corpus. The
consequence is the policy working exactly as designed:

> **The exemplar chose the operators.**

Scope came from the corpus and the theorem came from the exemplar, in that
order — which is what "suites drive scope" means when it is actually
followed rather than asserted.

**And the bitwise family was DELIBERATELY NOT DECLARED.** The reasoning is
deferral hygiene (§5.2) applied to vocabulary rather than to refusals:
**declaring an operator the walker refuses would be a vocabulary claim the
tier cannot honour.** A declared-but-refusing operator reads as coverage
in every table that counts declarations; leaving it undeclared keeps the
tier's stated surface equal to its actual one.

**THE POLICY.**

> **Suites drive scope. ONE theorem-worthy EXEMPLAR per tier drives the
> proof library. The exemplar is chosen for its THEOREM — never for its
> authorship — and no program is commissioned as a driver for its own
> sake.**

**AND THE RULE HAS ITS FIRST COMPLETED INSTANCE OUTSIDE PYTHON — the milestone
this section existed to produce** (Go, `4bda5af`, on master):

> **`bitLen_correct`: `callFunction … "bitLen" [v]` returns `bitLenSpec v` for
> EVERY `v < 2⁶⁴`.** The family's **first full function-level theorem about a
> real vendored program** outside the Python tier. **22 theorems**, axioms
> `propext` / `Quot.sound` / `Classical.choice` at worst, no `sorry`, no
> `native_decide`.

**IT IS A WAYPOINT, AND §9.0 IS WHY THAT WORD MATTERS**: this describes an
**exemplar**, never the **tier**. Go's completion is measured by its stdlib
reach instrument, and that number is elsewhere and much smaller.

Read against what this section asks for, it is the whole shape: a **suite** set
the tier's scope, **one exemplar** drove the proof library, and the exemplar was
**chosen for its theorem** — a function-level statement about a program the tier
did not write and cannot edit. **The theorem is about the vendored source, which
is the property that makes it a milestone rather than a demonstration**: nothing
in it can be arranged by choosing a friendlier subject after the fact.

**AND THE COMPOSITION FORCED A GENERALIZATION, which is the benign direction of
the quantifier family (§5.4a).** `body_step`, `cond_eval` and `loop_computes`
were stated with `[]` as the program table because the loop calls nothing;
`callFunction` passes the **real** table, so they are now stated over an
**arbitrary `P : FuncTable`**. *The loop genuinely does not care, and now says
so.*

> **GENERALIZATION BY COMPOSITION: when a consumer forces a lemma's quantifier
> wider and the proof does not change, the narrow statement was an accident of
> its first use.**

The quantifier family's other members are failures — a count under the wrong
unit, a census naming a language where it measured a tier. **This is the same
mechanism with the sign reversed, and it is worth naming so a lane recognizes
it as a result rather than as churn**: the composition is what discovered that
the loop's independence from the table was a *fact* and not a *convenience*. A
lemma widened by its consumer and re-proved with no new work has been **measured
to be more general**, which is strictly better evidence than being written
general by an author who guessed.

**AND THAT PRECEDENT WAS THEN CONSUMED BY A SIBLING TIER AS A DESIGN ORACLE,
WHICH IS THIS DOCUMENT'S FIRST MEASURED DIVIDEND OF THAT KIND** (Ada, building
inch 3). Two design questions, **both settled by citation rather than by
judgement** — and, decisively, **they were settled in OPPOSITE directions:**

* **Go's mutual-on-fuel shape ADOPTED** — *"answered by precedent rather than by
  my judgement."*
* **C's `termination_by` REJECTED, with the reason carried**: well-founded
  recursion takes **kernel reduction**, which is inch 2's own recorded trap.

> **A FAMILY DOCUMENT PROVES ITSELF WHEN A LANE DECLINES A SIBLING'S CHOICE FOR
> THE SIBLING'S RECORDED REASON.**

**Adoption alone would be weak evidence** — a lane copying whatever it finds is
not consulting a register, it is following the last thing it read. *The rejection
is what shows the register was READ rather than obeyed*, because declining a
precedent requires the thing only a written record can supply: **the cost that
made it wrong somewhere else.** **Two siblings, one reused and one declined, both
by citation** is the shape to ask for when a lane claims it designed by
precedent.

**AND THE SAME PRECEDENT SETTLED A TAXONOMY QUESTION EVERY TIER WILL MEET.**
Ada's subprogram table is **PROGRAM TEXT, NOT WORLD STATE** — parameterised like
Go's `FuncTable`, not carried in the world.

> **A TABLE THAT THE PROGRAM CANNOT CHANGE IS A PARAMETER. The world holds what
> EXECUTION mutates.**

*The test is one question a lane can answer before writing anything:* **can the
running program alter it?** If not, putting it in the world costs every lemma an
irrelevant hypothesis and every proof a frame condition it does not need — the
narrow-statement accident above, **manufactured on purpose.** This is the line
for every tier's table-like structure: **function tables, type tables, constant
pools and layout maps are text; heaps, stacks, channels and file descriptors are
world.**

**AND THE SPLIT'S DIVIDEND IS MEASURABLE, WHICH IS WHY IT IS WORTH THE COST**
(Go, `§G25`). A settled proof survived its **second** walker refactor **by
HYPOTHESIS RESTATEMENT ALONE** — no re-proof.

> **STABILITY UNDER REFACTOR IS THE SPEC-HALF / INTERPRETER-HALF SPLIT'S
> MEASURABLE DIVIDEND — and the second instance is what makes it a property
> rather than a coincidence.**

**The first survival is luck until it repeats**, and the metric is available for
free at every refactor: *count what had to change.* **A proof that needs its
hypotheses restated is reading the interpreter's shape through a stated
interface; one that needs re-proving was reading the interpreter directly.**
*That is a cheap, standing test of whether a tier's split is real or only
declared.*

**AND THE RIDER THAT DECIDES WHICH ACCEPTANCE CASE TO TAKE — take the
DISCRIMINATING one, and take it NOW** (Go rung 4, `a991f22`, on master). Two
functions were vendored. **`Len8` would have passed under any string
representation**; **`rev8tab` holds 128 bytes ≥ `0x80` of its 256**, and a Lean
`Char` at code point 200 is **two bytes in UTF-8** — so that table, and only
that table, could tell a wrong value model from a right one. It did:
`GoVal.stringV (s : String)` was **refuted by the spec's own words** — a Go
string value is a sequence of **bytes**, and `s[i]` yields a byte — and became
`stringV (bytes : List UInt8)`. **Blast radius 7 sites, checked before the
change.**

> **Choose the acceptance case that can FAIL under the wrong model, and take it
> NOW rather than defer it. The alternative is rebuilding the model after the
> rung has been built on it.**

**The trap is that the non-discriminating case is the attractive one**: `Len8`
is simpler, lands sooner, and passes. A rung accepted on it would have been
**green on a wrong value model**, and every subsequent inch would have added
weight to the thing that had to be replaced. **An acceptance case that cannot
fail is a demonstration; one that can is a measurement** — the same distinction
§5.3 draws for verdicts, applied to the choice of subject rather than to the
row.

**GENERALIZED ONE RUNG LATER, AND THE UNIT IS NOT WHAT IT LOOKED LIKE** (Go's
slice census, `e2af807`, on master). The rule above says *take the case that can
fail under a wrong model*. The next rung went looking for such a case and
**could not find one**, which is the finding rather than a setback:

* **60 candidates** used a slice expression plus a write through an index;
* tightened to require a **MIDDLE slice `a[i:j]`** — *the only place `cap` and
  `len` come apart, since a tail slice has `cap == len`* — it collapses to
  **8**, every one of which needs interfaces, `clear`, `append`, or
  range-over-struct-slice.

**So no small vendored function exercises both properties.** The pick was
`runtime.itoa` (**57 nodes, no external calls**) — which, called on a **middle
slice**, discriminates both: `mid := base[2:6]` has len 4 cap 6, `itoa(mid, 42)`
returns `"42"` with len 2 cap 4, `base` shows `"....42.."`, `out[0]='X'` makes it
`"....X2.."`, and `out[:cap(out)]` reaches **past `mid`'s end**.

> **A DISCRIMINATING ACCEPTANCE CASE DOES NOT HAVE TO BE A DISCRIMINATING
> FUNCTION. The case that can fail under a wrong model is `(FUNCTION,
> ARGUMENT)` — not the function alone.**

**The tightening is what proves the unit**, and it is worth reading twice: a
**tail** slice cannot discriminate `cap` from `len` **at all**, so the
argument's *shape* is part of the discriminator. A search over functions was
searching the wrong space, and it returned the honest answer for that space —
**none**.

**AND THIS DOES NOT REINTRODUCE THE PET-PROGRAM TAX §5.6 EXISTS TO REFUSE.** The
subject is still vendored and unedited; what the lane chose is **the call**, and
*a chosen call site is not a commissioned program — it is how a caller would use
the function.* The line to hold: **choosing an ARGUMENT is selection; writing a
SUBJECT is commissioning.** The first is what a suite does every time it picks
an input; only the second manufactures the thing it then measures.

**AND THE HIERARCHY THIS COMPLETES — three tiers of acceptance row, and the top
one is qualitatively different.** Against a naive *list-copy* slice model, the
four rows sort:

| row | the wrong model's response |
| --- | --- |
| the return value (`itoa(mid,42) = "42"`) | **PASSES** |
| the two aliasing rows (`base` shows the write) | **FAILS** |
| `out[:cap(out)]` reaching past the value's own length | **CANNOT BE STATED** |

> **Rows the wrong model PASSES < rows it FAILS < rows it CANNOT STATE.**

**A row the wrong model cannot express is the strongest evidence an acceptance
case can carry**, for two reasons worth separating. It fails at **design
time, not run time** — you discover it while *writing the row*, before anything
is built on the model. And it **cannot be argued away as a bug**:
inexpressibility is a property of the **representation**, not of the code, so
there is no patch that answers it. *A value reaching beyond its own length into
a longer array has no representation in a copy* — that sentence settles the
value model, and it settled this one **up front: backing array + offset + len +
cap.**

**The practical procedure is the inverse of how it reads.** You do not first
know the right model and then find the row; you **try to write the row under
the candidate model and fail** — and the failure is the finding, in exactly the
sense §9.7's blocker-naming norm means it. **An acceptance row you cannot write
is a specification of what the model is missing.**

**AND TWO RIDERS FROM THE FIRST RESOLUTION RUNG, both about what an acceptance
case must CONTAIN** (Go E1, `4a9f9ec`).

**A DISPATCH TABLE WITH ONE ENTRY IS INDISTINGUISHABLE FROM A HARD-CODED
ANSWER.** The walker half vendored **two** functions, not one, for exactly that
reason.

> **A mechanism's acceptance case needs enough entries to show it is a
> MECHANISM.** One row proves an answer; two prove a lookup.

That is §5.3's vacuity ruling applied to **dispatch** rather than to a verdict:
a single-entry table passes every test a correct table passes, and **nothing in
the result distinguishes the two** — the same shape as a check that cannot fail,
one level down in the implementation.

**AND THE GATE LANDED WITH THE CAPABILITY, NOT AFTER AN INCIDENT.** The lane
added its resolver self-test to the **triad gate list** in the same landing that
built the resolver, so **the shadowing discipline is enforced by the gate rather
than by the operator.** *Fixes live in gates* is usually retrospective — a rule
minted from something that went wrong. **Applied at birth it costs nothing and
skips the incident**, which is the cheapest form the rule ever takes and the
easiest to forget while the capability still feels well understood by the person
who wrote it.

**And one convergence worth a clause**: the rung's discriminating arguments
**pull in opposite directions on the same input** — `ntz64(0) = 64` against
`log64(0) = -1` — which is the four-tier hierarchy's top row (below) arrived at
independently, on a mechanism rather than on a value model. **The pattern
generalizes past the case that minted it**, which is the test this document
applies to everything it promotes.

**AND AN EXPECTATION MAY BE REGISTERED BEFORE THE INSTRUMENT THAT COULD TEST IT
EXISTS — the falsifiable version of a TODO** (Ada, `43926b0`). The lane left an
expectation **explicitly UNASSERTED** for the stronger instrument to check: **all
six `CallExpr` targets should resolve to indexed components** under Ada's
legality rules —

> **and if one does not, that is the finding.**

**A TODO says work is owed. This says what the world will look like if the work
is right**, which costs the same to write and is **worth something even if
nobody returns to it**: the next lane building that instrument inherits **a
prediction to score**, not a task to schedule.

**And it is the honest form of a gap**, because it is refutable while remaining
unasserted: the expectation is **not claimed as a result**, and it **cannot
quietly become one** — a reader meeting it finds a named number, a named
condition, and an explicit statement that nothing has checked it. *An
unfalsifiable TODO ages into a chore; a registered prediction ages into
evidence, in whichever direction it turns out to go.*

**AND THE HIERARCHY HAS A COMPANION METHOD, now on its SECOND instance and
worth its own name: ASK WHAT THE WRONG MODEL WOULD *PERMIT*** (Go §G23,
`9a6d6ad`; after §G20's array-as-slice-header). A `GoVal.tupleV` **would accept
programs `gc` REJECTS** — *"assignment mismatch: 1 variable but … returns 2
values"*. **Multi-valuedness is a property of the CALL SITE, never of a value.**

> **To choose between two model shapes, ask which one ACCEPTS A PROGRAM THE
> ORACLE REJECTS.**

**This is the acceptance hierarchy's dual, and it applies EARLIER.** The
hierarchy ranks rows by what a wrong model **fails or cannot state** — it needs
a candidate row and a run. This asks what a wrong model **admits**, and it can
be answered **from the shape alone, before any row exists**: *the over-permissive
model is refuted by a program that should not typecheck.*

**And over-permissiveness is the failure a differential corpus is worst at
finding**, which is why the method earns a row rather than a mention: a corpus is
made of **valid** programs, so **a model that accepts too much passes every one
of them.** Nothing in the suite is shaped like the counterexample; **only the
question is.**

**AND ACCEPTANCE POWER IS NOT ROW COUNT — the flips measure which rows do the
work.** Measured on the same rung: the carry-dropping wrong model **passes 5 of
8 `add128` rows**, and **only the ripple rows discriminate.** All three flips
were run.

> **A ROW COUNT IS NOT ACCEPTANCE POWER. The non-vacuity flips are what
> distinguish a row that does work from a row that keeps it company.**

**Eight rows sounds like a battery and behaves like three.** The other five are
not waste — they document the construct and they would catch a *different* wrong
model — but **a lane reading "8 rows" as strength has read the wrong number**,
and the number that answers the question is *how many rows change verdict when
the model is perturbed.* **§5.3's non-vacuity discipline, used as a measuring
instrument rather than as a hygiene check.**

**AND A ROW CAN BE DESIGNED AGAINST AN IMPLEMENTATION THAT HAS NOT BEEN WRITTEN
YET** (ES, node-verified). Two discriminators for object destructuring, **both of
the passes-every-value-test-and-fails-this-one shape:**

* **the default fires on `undefined`, NOT on absence** — §8.6.3 tests **after
  the `Get`**, never `HasProperty`, so **the natural absence-based
  implementation fails `{a=5} = {a:undefined}`**;
* **the default is LAZY** — observable only through **side effects**, so **a
  compute-then-override implementation passes everything else.**

> **Rows built to kill the TWO MOST NATURAL WRONG IMPLEMENTATIONS, before either
> is written.**

**This is *ask what the wrong model would permit* run FORWARD.** That method
picks between two candidate shapes a lane is holding; **this one enumerates the
shapes a lane is LIKELY TO REACH FOR and pre-loads the rows that refute them.**
The cost is the same census either way — *and the difference is whether the
discriminating row exists before or after somebody writes the plausible thing.*

**The tell that a discriminator is of this kind**: it is the row that **cannot
be derived from the spec's happy path**, only from asking *"what would I have
written?"* — `{a:undefined}` and a side-effecting default are both **shapes no
value-oriented test suite produces**, which is exactly why the natural
implementation survives every other row.

**AND A FOURTH TIER SITS ATOP IT — THE ROW THAT KILLS TWO WRONG MODELS AT ONCE,
IN OPPOSITE DIRECTIONS** (Go, `da9a7bc`, on master). `runtime.printuint`'s array
never escapes, so the acceptance case is **one array with two operations**:
`b := a` **copies**, `s := a[:]` **aliases**, and `gc` says `a` is **`"wSyz"`**.

| model | what it produces |
| --- | --- |
| **the truth** (value + addressability) | **`wSyz`** |
| **arrays-as-headers** | `BSyz` |
| **slices-as-copies** | `wxyz` |

> **BOTH wrong models fail the SAME ROW, in OPPOSITE directions** — strictly
> better than `Reverse8` and `out[:cap(out)]`, each of which killed one.

**Two things one row buys here that two rows do not.** It **refutes both
candidates**, and — the part worth the tier — **the DIRECTION of the failure
names WHICH wrong model you have.** A row that merely goes red says *the model
is wrong*; this one says *the model is wrong in this specific way*, which is the
difference between a refutation and a **diagnosis**.

**AND THE HIERARCHY GOVERNS HYPOTHESES FROM EVERY DIRECTION, INCLUDING
DOWNWARD** (Wasm, `6bd3ca1`). The coordinator raised *"these errors are your new
proofs"* from a log tail. The lane **refuted it by measurement** — **byte-for-byte
baseline reproduction at the same six lines**, and **`grep` for `SubtypingPort`
errors = 0** — **not by assurance**, and **the refutation quoted its
instrument.**

> **The acceptance hierarchy ranks CLAIMS, not CLAIMANTS. A coordinator's
> hypothesis enters at the same rung as a lane's self-report, and leaves by the
> same door.**

**Worth recording because the asymmetry is the natural failure**: a hypothesis
from the coordinating role arrives with standing, and the cheap response is
agreement — which would have written a false statement into the register with
**more** authority than the lane's own reports carry. **The lane answered a
plausible reading with a reproduction**, which is the only response that
settles it in either direction.

**AND IT HAS BEEN DISCHARGED TWICE IN ONE DAY, both within the hour** — the
coordinator's hypotheses on **SoftFloat's drift** (`Basic.lean` edits; actually
two `Nat.log2` rows) and on **Wasm's red** (*"these errors are your new
proofs"*) were **each corrected by lane measurement.**

> **The asymmetry this row warns about is now being exercised in the healthy
> direction, which is the only evidence that the rule is real rather than
> polite.**

**A rule that only ever runs upward is a courtesy.** Two corrections in a day,
from different lanes, against the role that dispatches their work, is what makes
*claims, not claimants* a **practice** — and it is cheap to sustain **only while
the measurement, not the disagreement, is what gets published.**

**AND THE RULE REACHED THE COORDINATOR'S OWN CITATIONS, WHICH IS THE LAST PLACE
IT HAD BEEN EXEMPT** (Go, ticket correction). The dispatch quoted identifiers
that **did not match**; the lane pushed **on ITS OWN verified green** and said
so.

> **A MISMATCHED STAMP IS EXACTLY THE THING THAT SHOULD NOT AUTHORIZE A PUSH.**

> **A coordinator's cited pids, shas and trees are CLAIMS LIKE ANY OTHER.**

**The exemption was never argued for; it came from the citation's function.** A
relayed identifier arrives *as the evidence*, so a lane checking it feels like a
lane doubting the record rather than reading it — **and the failure mode is
silent, because a wrong identifier that nobody re-derives simply becomes the
ledger's version of events.** *The lane that pushed on its own green did the
cheaper thing and the correct one: a stamp you verified beats a stamp you were
handed, at equal cost.*

**And the two top tiers rank on different axes, which is worth saying plainly
so a lane does not read the hierarchy as a single ladder.** *Cannot be stated*
is strongest on **WHEN you learn** — design time, before anything is built.
*Fails in opposite directions* is strongest on **WHAT you learn** — which
candidate survives. **A row can be both**, and a lane choosing between them
should ask which it is short of: certainty about the model, or certainty about
which model.

**AND THE THEOREM BECOMES AN ORACLE FOR ITS SIBLINGS — a THIRD adjudicator
kind.** The same landing checked `Len8` **exhaustively over all 256 inputs**
against `bitLenSpec` — **§G13's PROVED spec** — and `Reverse8` against **what
`gc` printed**.

> **The theorem proved for the crypto lane's hand-rolled loop now predicts the
> standard library's table-driven function, and they agree on every input.**

> **Once a spec is PROVED for one implementation, it serves as an INDEPENDENT
> STANDARD for sibling implementations.**

So a tier's adjudicators are now three kinds, not two: the **compiled oracle**
(what the real toolchain printed), the **hand-derivation**, and the
**spec-theorem**. The third is the cheapest to run and the most fragile to
misread, so the demotion rule applies to it **exactly as before, per relation**
(§5.4a): a spec-theorem row adjudicates *"this implementation computes the
spec"* and **not** *"the compiled artifact does"* — which is why `Reverse8`
still needed `gc`, and why `Len8`'s oracle rows are not retired by `Len8`'s
spec rows.

**Two implementations agreeing against one proved spec is genuinely new
evidence**, and it is worth naming what it is: not a second proof, and not a
differential between two models. It is **one proved relation used twice**, and
its value comes from the implementations being **structurally unrelated** — a
hand-rolled loop and a table lookup, which share no code and were written years
apart to do the same arithmetic.

**AND THE SMALL GUARD SHAPE THAT CAME WITH IT: NAMED SINGLE ROWS BESIDE AN
EXHAUSTIVE SWEEP.** Three named high-byte rows sit next to the 256-input sweep,

> **so a representation that lost the high bit fails BY NAME, not only in
> bulk.**

An exhaustive sweep is the stronger check and the **worse diagnostic**: it
reports *"some input disagrees"* and leaves the reader to bisect. **A handful of
named rows chosen at the boundary the model is most likely to get wrong costs
nothing and turns a bulk failure into a sentence.** Non-vacuity was run on both,
which is what keeps the named rows from being decoration (§5.3).

Applied: **SystemVerilog's exemplar is the floating-point divider** (§3.5.2
states its theorem, and it factors through the shared vertex rather than
comparing two models). **C's is `ctwin/sunfish.c`, which already served**
and is not re-commissioned — its job was the construct census and the
ingestion milestone, both done. A founding lane names its exemplar by
stating the theorem it intends to prove; if it cannot state one, it does
not need an exemplar yet, and its suite is enough.

---

## 6 LIMITS — the languages this model does NOT fit

Tier selection stays principled only if the model's assumptions are
written down. Five assumptions, then the misfits.

**Read this section against §0.1, because the doctrine fixes what "does
not fit" may mean.** A misfit is **never** "hard to prove" — hardness is
expected, is accepted at the definition layer, and is a signal to the
program rather than to the model (principle III). A misfit is strictly
narrower: a subject whose correctness this architecture **cannot DEFINE**
soundly and completely, because its behaviors are not generated by an
interpreter over explicit parameters. Every entry below fails at that
layer, not at the proof layer. That is why the concurrency entry shrank to
the relaxed-atomics fragment (§3.6) and why floats left the list entirely
(§3.5): in both cases the definition was available, and only the folklore
said otherwise.

**The model assumes:** (1) execution proceeds in **discrete steps**; (2)
the observable state is **finitely representable**; (3) behavior is
**GENERATED by an interpreter** that is deterministic modulo explicit
parameters; (4) per-run claims are **quantified over those parameters**;
(5) observation is **termination-indexed** — the ∃-fuel threshold form
needs a final answer to index.

**AND (5) HAS A SIBLING THAT IS EASIER TO MISS: observation is also
DETERMINISM-INDEXING.** Assumption 5 says a claim needs a final answer to
be indexed *by*; this one says a claim about *sameness* needs an observable
to be indexed *over*.

> **Determinism quantifies over the TRACE, so its meaning MOVES WITH THE
> TRACE TYPE.**

A **coarser** observation makes **more** programs deterministic; exposing
**finer** state — per-region internals, intermediate scheduler structure —
makes designs non-deterministic **by construction** at that granularity.
Neither answer is wrong; they are answers to different questions, and only
the trace type says which was asked.

**So every determinism and agreement claim in this family is
OBSERVATION-INDEXED, and a tier that changes its trace or observable type
DOES NOT INHERIT its determinism theorems.** They must be re-established
over the new observable. The measured instance: the SV tier's **five
`_det` theorems must be re-proved through `cycleOf`** — the theorems were
never false, they were about a different trace.

**This refines §3.4's and §3.6's own wording.** Those sections say the
interpreter is *"deterministic per (program, schedule)"*, which is true and
incomplete: it is deterministic per (program, schedule, **observable**). A
tier that later exposes more state in `W` has not broken that claim — it
has asked a new one, and owes new proofs.

**THE ANTI-TAUTOLOGY RULE, from the same audit.** *"RaceFree → determinism"*
is **vacuous wherever the two are one predicate**, which is easy to arrange
by accident and reads as a real theorem. The correct family phrasing:

> **Determinism is a PREMISE or a PER-DESIGN THEOREM — never a tier-wide
> conclusion.**

The audit that produced this is worth its outcome being stated, because it
went the good way: **the Lean was never wrong.** `Deterministic` was
design-indexed all along, and the racy design's **negation** was proved.
Only the surrounding prose overclaimed — and prose is the part §9's whole
strategy is about moving into things that can be run. The fix was to the
prose, and the theorems stood.

### 6.1 The misfits

1. **THE RELAXED-ATOMICS FRAGMENT ITSELF** — and note how narrow this now
   is. **Concurrency is NOT a misfit**: §3.6 gives it a four-piece pattern
   — schedule-as-parameter, executable counterexample schedules, the
   standard's own DRF-SC clause as the fence, and three proof-burden tiers
   — under which "correct for all interleavings" is an ordinary
   ∀-parameter theorem and, on a bounded fixture, a decidable one. What
   stays outside is only the fragment *beyond* DRF: programs deliberately
   using `memory_order_relaxed` or acquire-release, whose allowed
   behaviors are the execution GRAPHS satisfying a set of axioms rather
   than the traces any schedule generates. Load-buffering and
   out-of-thin-air outcomes have no generating schedule; the "parameter"
   would be the graph, and the artifact would become a **consistency
   CHECKER** — a different architecture. `docs/c-tier-charter.md` §3.3
   measured the cost of trying: R6 "is the one rung that is not a
   widening", replacing a state function with a memory-ORDER relation and
   breaking `fuelMono`, kernel-reducibility and the one-line-per-job batch
   protocol at once. That verdict survives, scoped to the fragment that
   earns it.
2. **PRODUCTIVE NON-TERMINATION** — streams, servers, reactive systems,
   lazy infinite structures. There is no final answer for ∃-fuel to index.
   The known extension is **observation-indexed** theorems: fuel indexes
   the output PREFIX and bisimulation replaces termination. Lustre-style
   per-tick systems fit today, which is why the SystemVerilog lane works
   per cycle. The verdict system's termination assumption is hereby
   written down rather than assumed.
3. **CONTINUOUS STATE** — Verilog-AMS, Modelica, hybrid systems: worlds
   evolving by ODEs over ℝ. Outside the `Run σ` model, and the tree
   already says so by building them differently: `LeanModels/Circuit/` and
   `LeanModels/Spice/` are 27 675 lines that use no `Run` at all,
   modelling by interval enclosure and contract (`Circuit/Enclosure.lean`
   quantifies over `ℝ` directly). That is not a lane to convert; it is a
   second architecture in the same repository, correctly.
4. **DISTRIBUTIONAL CLAIMS** — probabilistic and quantum programs. A
   **half-fit, stated honestly**: per-seed determinism fits perfectly via
   an entropy-stream parameter, and the verdict system would score it. But
   the interesting theorems are about the distribution OVER seeds, and
   that needs a measure layer the scoreboard does not have. Per-seed
   claims are in reach; distributional ones are not.
5. **TRANSCENDENTAL FUNCTIONS over ℝ** — and note carefully that this is
   *not* "floats". Floats are **not** a misfit and not a tax: IEEE 754's
   arithmetic core is the best-specified subject in the family, its
   correctly-rounded results are decidable integer arithmetic on finite
   encodings, and it is a shared COMPONENT (§3.5), not a limit. What
   genuinely sits outside is the part that leaves the rationals — `sin`,
   `exp`, `log` and their accuracy claims, where C says
   implementation-defined and ECMAScript says implementation-approximated.
   Those route to REFUSE(`environment`) or to a profile pin (§3.5.4); they
   are the *only* float-adjacent thing that would need ℝ, and no tier has
   demonstrated a need for them.

### 6.2 The deceptive fits, for contrast

* **Go** — looks like a concurrency misfit, is not: its memory model is
  explicitly DRF-SC, so schedules GENERATE its behavior and §3.6's four
  pieces apply unchanged. Go and a future C-threads extension are one
  pattern with two spec citations.
* **Prolog** — looks nondeterministic, is not: ISO fixes depth-first
  search with leftmost selection, so the interpreter is deterministic and
  the tier is ordinary.
* **SQL** — bag semantics, and row order is precisely the ∀-resolution
  pattern of §3.4: an explicit parameter, quantified at theorem level.
* **Interactive programs** — the input stream is a parameter, which is
  what the family already does with stdin, the clock, the environment and
  argv.
* **C++ and Rust** — the model fits them fine. Their problems are scale
  and, for Rust, the absence of a normative spec to mirror; neither is an
  architectural misfit, and neither should be founded on the strength of
  "it fits".

---

## 7 COORDINATION LAW — many lanes, one machine, one master

A family of tiers means a family of lanes, and they share two scarce
resources. The rules below are **standing law for every lane**, and this
section owns them.

### 7.1 The machine-wide BUILD LOCK (mandatory, 2026-08-22)

Concurrent Lean builds took the development machine down — load 29 across
41 processes. The protocol:

1. **ONE full build at a time, machine-wide.** Before any `lake build`, any
   triad run, or any `lake env lean` on a file that triggers more than ~100
   jobs, acquire the lock — an `mkdir` spinlock, which is portable on
   macOS where `flock` is not:

   ```
   while ! mkdir /tmp/ls-build.lock 2>/dev/null; do sleep 60; done
   trap 'rm -rf /tmp/ls-build.lock || echo "LOCK RELEASE FAILED" >&2' EXIT
   ```

   Release promptly. **Never hold it while thinking or editing.**

   **AMENDMENT 2 — the release must be `rm -rf` and its status must be
   checked. Independently reproduced by the Go lane**, which hit both this
   and the `-j4` defect below without having read them — two lanes meeting
   the same two failures is the signal that they belong in a shared
   document rather than in each lane's notes. A `rmdir` release composed with an owner-stamp file inside
   the lock directory **fails silently**: `rmdir` refuses a non-empty
   directory, the `trap` swallows the status, and the lock leaks — after
   which every other lane blocks forever on a lock nobody holds. This
   happened. `rm -rf` removes the directory whatever it contains, and the
   `|| echo` makes a failed release loud instead of invisible.
2. **Cap parallelism under the lock — but NOT with `-j4` on this lake**,
   where it is an argument error rather than a flag. Use the environment
   or the toolchain's accepted spelling, and verify the command runs
   before relying on it; a build that dies on its own flags is a build
   that did not happen.

   **Exit status 143 is a RESOURCE KILL**, not a build failure — the OS
   terminated the job. Re-read it as "the machine was oversubscribed",
   check the lock discipline, and never record it as a red build.
3. **Scratch-file loops** — `lake env lean` on small dependency-free files
   — are allowed WITHOUT the lock, but must run under `nice -n 19` and
   stay small.

   **AND ONLY IN A WARM CLONE — the exemption is a property of the CLONE,
   not of the file.** `lake env lean` on a dependency-free scratch file is
   cheap only where the dependencies are already resolved; in a **cold**
   clone the same command resolves and downloads them, which is Lean
   execution outside the lock (A11) and a GB-scale download instead of CoW
   seeding (A13). This lane made exactly that mistake, reading rule 3 as
   being about the file when it is about the clone. **Seed first (A13),
   then probe.**
4. **Batch aggressively: one triad per landing, never per edit.**
   Stage, then build. No speculative builds.
5. **A stale lock** (left by a dead lane) is cleared only after verifying
   by parentage and cwd that no build is running — then `rmdir` and note
   it.

   **THE STALENESS TEST IS TWO-PART AND MUST NEVER BE SIMPLIFIED TO
   PID-ONLY: the owner pid is alive AND a live `lake` descends from it.**
   Both parts, always. The second is not redundant, because **a lane's
   death does not imply its build's death** — detachment is deliberate, it
   is what lets a triad survive a restart.

   The rebuild lane found the violation in the wild and it is the reason
   this line exists: an owner file reading
   `go-lane lake pid 43341 (cwd /…/lean-go)` has `lean-go)` as its last
   field, so the pid parse yields a non-numeric string and `kill -0`
   **errors**. A pid-only test would not merely have failed to detect
   staleness — it would have concluded *stale* and **reclaimed an ACTIVE
   holder's lock**, stampeding the queue. It was harmless only because
   part two found a live `bin/lake build` and no reclaim fired.

   **The failure direction is what makes this worth a rule**: a broken
   liveness check does not fall back to caution, it falls forward into
   reclaiming a lock somebody is holding.
6. **Never kill another lane's processes.** Kills by parentage only. The
   owner's own tooling is not yours, and this has been got wrong twice.

The reason this belongs in the architecture document rather than in a
lane's notes: the family's whole shape — many tiers, each with its own
corpus and its own triad — is what creates the contention. A convention
that makes founding five lanes cheap has to say how five lanes share one
build.

### 7.1a THE AMENDMENT REGISTER — this section is the protocol's ONLY durable home

**The scratchpad has been purged three times.** The third purge took
`BUILD_LOCK_PROTOCOL.md`'s history with it: the file was recreated carrying
**amendment 10 alone**, under a header asserting that 1-9 live "in memory +
family doc §7" — an assertion that was **false when written**, because §7
carried only amendment 2. This register exists so the claim becomes true,
and so the next purge costs nothing.

**The lesson generalizes past the lock**: a protocol that lives only in the
scratchpad is one purge from gone, and a pointer to a durable home is not a
durable home. Anything a lane must obey belongs in a git-tracked file.

| # | rule | status |
| --- | --- | --- |
| base 1-6 | the six rules above (lock, parallelism, scratch loops, batching, stale-clearing, no cross-lane kills) | **carried, §7.1** |
| 1 | — | **LOST** — no text recovered from any durable source |
| 2 | `rm -rf` release with checked status; `-j4` is an argument error; exit 143 is a resource kill | **carried, §7.1 rule 2** |
| 3 | Go lane's empirical determination (subject line only) | **LOST** — attribution survives, text does not |
| 4 | **owner written ONCE under `set -C`** (noclobber) at acquisition, so a second writer fails loudly instead of silently taking over the identity; **owner is a hint, the process tree is the truth** | **recovered** — below |
| 5 | owner file format is exactly `<lane> <pid>`, **pid LAST**; parse the last whitespace-separated field | **carried, §7.1 rule 5** |
| 6 | never fetch-rebase while a build runs in the same clone | **carried, §7.2** |
| 7 | **the trap must be OWNERSHIP-CHECKED** — below | **recovered** |
| 8 | **a staleness verdict comes from ONE atomic re-read immediately before the removal**, never from an earlier read | **RECOVERED** — from `tools/triad.sh`'s header |
| 9 | **FIFO ticket queue** — below | **new** |
| 10 | **the owner pid must span the tenure** — below | **carried** |
| 11 | **the lock covers ALL Lean execution** — below | **new** |
| 12 | **traps kill descendants RECURSIVELY** — below | **new** |
| 13 | **mandatory CoW cache seeding** — below | **carried** |
| 14 | **full-tree builds are QUIET-MACHINE-ONLY** — below | **new** |
| 15 | `pkill -f <path>` does NOT kill a `lake build` — below | **new** (its RSS number is SUPERSEDED by 16) |
| 16 | **RSS line is PER-PROCESS 5 GB / chain 10 GB**, and **16.2 retiring a runner** — below | **carried** |
| 17 | **the single-file ITERATION loop**, ticket-free under conditions — below | **DRAFT — five tightenings flagged** |

**AMENDMENT 4 — the owner file is written ONCE, under `set -C`.** Origin: a
lane holding the lock had its `owner` file **overwritten by another lane**.
Since `owner` is the staleness signal and is writable by a lane that does
not hold the lock, a future reader could then declare a live lock stale.
Writing it once under noclobber makes a second writer **fail loudly**
instead of silently taking over the identity. And the standing corollary:
**owner is a hint; the process tree is the truth.**

**AMENDMENT 7 — the trap must be OWNERSHIP-CHECKED.** On exit, verify the
lock is still *yours* before removing anything; if it is not, print
`LOCK NOT MINE — left alone` and remove nothing. This fixes the release
that **succeeds against someone else's lock**: a surviving detached trap
pointed at a *re-created* lock would delete an active holder's lock and
stampede the queue. Observed working in the wild — a lane whose lock had
been handed on exited without removing anything.

**OBSERVED WORKING, this session** — recorded because an amendment that has
never fired is a design, not a control:

* **A7's owner-conditional trap refused to release a taken-over lock
  TWICE**, printing *"NOT RELEASING: not my lock"*. That is the exact
  scenario A7 exists for — a surviving trap pointed at a lock somebody else
  now holds — and it declined, twice. (Observed in a lane's own A7
  implementation; `tools/triad.sh` implements the same rule.)
* **The 143/137 resource-kill retry came back GREEN on attempt 2.**
  `tools/triad.sh` treats those exits as a resource kill rather than a red
  build and re-runs once, which is base rule 2 firing as designed rather
  than a lane deciding a red was spurious.

**AND A REQUIRED LOUDNESS GUARD FOR MODEL FILES: `set_option autoImplicit
false`** (SV; a 17-second red, re-ticketed, one-import fix). The error was
loud **only because that option is set in that file.** Without it, Lean would
have **silently bound the unknown identifier as an implicit universe variable**
and failed **later and stranger** — the lane's own Edge precedent.

> **`autoImplicit false` converts a strange late failure into a named
> 17-second one.**

**It is a LOUDNESS control, not a style preference**, which is why it belongs
beside the hazards below rather than in a linting note: the setting does not
prevent the mistake, it decides **where and under what name** the mistake
surfaces. Off, a typo becomes a well-formed program with an extra universe
variable, and the eventual error names something that is not the defect. On, the
identifier is simply unknown, at the site, immediately.

**The general shape, since every tier will meet a version of it**: a language
feature that **silently supplies a plausible meaning for something the author
did not write** is a loudness hazard, and the fix is always the same — **turn it
off in files that are the model**, where a wrong meaning is a wrong semantics
rather than a convenience.

**AND THE LAW GAINS A DEPLOYMENT CLAUSE, because the honest ladder position is
part of the law** (measured 2026-08-24, re-verified here): **1 of 163
`LeanModels` files carries it. 0 of 188 under `Examples`.**

> **A LOUDNESS GUARD ADOPTED AS LAW BUT PRESENT IN 1 OF 163 FILES IS A DECLARED
> GATE THAT IS NOT YET POINTED** (§5.4b's ladder), **and the register records
> the ladder position ALONGSIDE the law — never the law alone.**

**A law without its deployment number reads as a property of the tree**, and
that is exactly the misreading §5.4b exists to prevent: *the rule is adopted*
and *the tree obeys the rule* are different claims, and only the second is
coverage. **So the adoption is stated in three parts:**

* **REQUIRED for NEW files, immediately** — no cost, no migration, and the
  files most likely to carry a fresh typo;
* **RETROFIT per tier, riding natural touches** (§9.2's by-touch discipline) —
  a 162-file sweep is a big-bang change to files nobody is otherwise editing;
* **EXPLICIT BINDERS FIRST wherever elaboration depends on auto-bound
  implicits.**

**The third clause is the one with teeth, and `Surface.lean` is its exhibit**:
it **hard-codes arity 10 and position 4**, so flipping the option there is **a
SEMANTIC change, not a hygiene change.** Wherever a metaprogram hard-codes a
shape, the auto-bound implicits are **part of that shape** — and the retrofit
that looks like a one-line setting is a rewrite of what the metaprogram
matches.

> **A setting that changes how many binders a declaration has is not a style
> setting in any file that COUNTS binders.**



**THREE LEAN TOOLING HAZARDS, recorded because each cost a red and none
announces itself.**

* **Through a `def`-ALIAS, DOT NOTATION PICKS THE TARGET'S LEMMA.**
  `VEnv.HasType.instN` and `VEnv.IsDefEq.instN` **take their arguments in
  different orders**, and `HasType` is a `def` unfolding to `IsDefEq` — so
  dot notation resolves to the **`IsDefEq`** lemma and **mis-slots
  silently**. It worked for `instL` only because those two orders
  *coincide*, which is the worst kind of luck: it taught the wrong lesson
  before it produced a red. **Name the lemma you mean.**
* **Nested inductives refuse `induction`.** Use the equation compiler's
  **`<f>.induct`** — and note the calling convention differs: the arms
  arrive **unfolded**, so **`apply` it**; `induction … using` fails.
* **A plain `def` delta-unfolds past the motive.** Prove the `_iff` form
  first, then `attribute [irreducible]` — otherwise the definition
  disappears underneath the induction that was supposed to be about it.

**A TRUNK PROOF'S `clear` LINE IS INTERFACE, NOT HYGIENE** (Wasm; fix clean,
ticketed). `clear h` was **LOAD-BEARING and was dropped as boilerplate** — the
leading hypothesis **sweeps into the induction motive.**

> **`clear` before an induction is part of the PROOF'S CONTRACT: it says which
> hypotheses the motive must not generalize over.**

**The ported-lemma law's sibling.** That one says *the proof architecture ports,
the proofs do not*; this says **a line that LOOKS like tidying is architecture** —
and it is the line a porter is most likely to drop, because **hygiene is exactly
what a reader trims when adapting someone else's proof.** *A tactic whose only
visible effect is a smaller context is doing its work in the motive, where the
context is not visible at all.*

**AND THE INSTRUMENT-PAYOFF LAW HAS ITS SECOND MEASUREMENT**: *the scratch loop
did in **four 20-second probes** what **four tenures** could not.* **Same lane,
same defect class, two orders of magnitude** — arriving the day after crunga's
5 934-seconds-for-43 figure, from a different tier. *Two independent
measurements is this document's convergence standard, applied to the claim that
instruments set cost rather than defects.*

**AND THAT STANDARD HAS NOW BEEN MET BY A SPINE CLAIM, WHICH IS A DIFFERENT KIND
OF THING TO MEASURE** (Lean tier, same fork). **Four monad rules were reused
VERBATIM across four new pairs** — *the first evidence they are the corner's
SPINE rather than a two-pair accident.*

> **A SPINE CLAIM GRADUATES FROM DESIGN TO MEASUREMENT WHEN THE SAME RULES
> DISCHARGE PAIRS THEY WERE NOT WRITTEN FOR.**

**The design version of the claim is unfalsifiable and every lane makes it**: a
set of lemmas *looks* like a spine at n=2, because two uses is what an author
needs to notice a pattern. **At n=6, with four of the six not in view when the
rules were written, the claim has a denominator.** *Reuse across cases chosen by
the author is a description of the author; reuse across cases chosen by the
corpus is a property of the rules.*

**AND A ROUTE-SELECTION LAW FOR THE MATCHER FAMILY, which sharpens the
third-state finding above** (same tier).

> **WHERE A DEF'S MATCHER HAS NO EQUATIONS, SPECIALISE IT AT THE ARGUMENT YOU
> CARE ABOUT — and reach for surgery on the subject only if the payload contains
> something that does not reduce.**

**The two routes need different things, and the taxonomy predicts which one
exists.** The **stranded** route needs **equations** (`simp`/`rw`); the **open**
route needs only **reduction** (`rfl` at a concrete argument) — **so the open
route is available exactly when the discriminant is string-free**, which is what
walls 1-2 already classify. *A lane holding that taxonomy does not have to
discover the route; it can look it up.*

**And the ordering is the part that matters, because it is the previous law's
operational form**: **specialise first, and treat editing the subject as the
LAST resort it is.** *A matcher with no equations is not a wall — it is a
general statement asking to be asked a specific question.*

**TWO MORE FROM THE C LANE'S SEAM LIFT, AND THE FIRST IS ABOUT WHAT A TERM
*IS*.**

**A MATCH OVER AN INSTANTIATION IS A DIFFERENT TERM FROM A MATCH OVER THE
GENERAL TYPE.** The cross-spelling example **did not typecheck**: the two sides
are **two distinct matcher constants.**

> **State cross-spelling claims on MATCH-FREE lemmas, or you are testing MATCHER
> ELABORATION rather than the fact.**

**A `match` compiles to a generated constant that carries its motive**, so
instantiating the type produces a **different** matcher — and a claim written
with matches on both sides is a claim **about those two constants**, which is
almost never the fact the author meant. *The lemma that survives instantiation
is the one with no match in it.*

**AND A DIAGNOSIS ROW FOR TACTIC-SCRIPT REDS: A TACTIC THAT FAILS BECAUSE THE
GOAL IS GONE READS EXACTLY LIKE ONE THAT FAILS BECAUSE THE GOAL IS HARD.**
`rw`'s **trailing `rfl` discharged the goal**, and the following cases **errored
`no-goals`.**

> **The error names the tactic that had nothing to do, not the tactic that did
> too much.**

**Same family as *count defects after unification***: the visible failure is
**downstream of the cause**, and a lane triaging the reported line **works on
the wrong tactic.** The tell is specific and cheap — **`no-goals` is never about
the tactic it names** — and a script whose cases begin failing in sequence is far
likelier to have lost its goal than to have met several hard ones at once
(§5.4b's uniformity rule again).

**TWO MORE, BOTH FROM ONE-CAUSE REDS, AND BOTH ABOUT WHAT A TACTIC DISPATCHES
ON** (C lane; verify at landing).

**A TACTIC THAT DISPATCHES ON A GOAL'S HEAD NEEDS A STABLE HEAD — AND A `def`
THAT UNFOLDS TO A BINDER HAS NONE.** `MemInvariant` as a `def` produced
**thirteen identical failures from a single `intro`**; as a `structure` it has a
head the dispatcher can see.

> **Thirteen failures, one cause — and the count is the tell.** A dispatcher
> failing on a head it cannot form fails **identically everywhere**, so a
> uniform failure set is evidence about the DISPATCH, not about the goals.

That is the *uniformity* rule (§5.4b) arriving in a proof: **a check that
convicts most of a corpus is likelier reading the wrong column** — here, a
tactic that fails at every site is likelier missing a head than meeting thirteen
hard goals.

**AND `apply` AT DEFAULT TRANSPARENCY DELTA-UNFOLDED A 19-WAY `String` MATCH
INTO A whnf TIMEOUT.** Fixed with **`with_reducible` per `apply`**:

> **Each failure is one HEAD COMPARISON, not one UNFOLDING.**

**This is the same hazard §8 already records** (`apply` at default transparency
whnf-unfolding tier constants) **arriving at a different scale**, and it is
worth the second entry because the fix is now stated as a **cost model** rather
than as a caution: the tactic's price is *attempts × cost-per-attempt*, and
**transparency is what sets the second factor.** A19-way match is nineteen cheap
comparisons or nineteen expensive unfoldings, and **nothing in the source says
which.**

**And the landing carried a DOCUMENTED heartbeats budget on the one large
declaration** — not a raised limit but **a stated one**, which is the honest
form: *raising heartbeats trades a wrong answer for a slow one*, and **a budget
written down with its subject is a measurement of what that declaration costs.**

**AND THE DECLARATION-SLOT FAMILY HAS ITS GRAMMAR STATED ONCE — SEVENTH
INSTANCE** (SV). Every member of this family has been a token in a position the
grammar does not admit; the rule that generates all of them:

> **`/--` BINDS TO THE NEXT DECLARATION. `/-!` STANDS ALONE. And `#guard` /
> `#eval` / `#print` are COMMANDS, NOT DECLARATIONS.**

**Seven incidents, one sentence** — and the reason it took seven is that **each
instance looked like a fact about the token that bit that day** (a doc comment, a
`set_option`, a `#guard_msgs`), when all of them were **facts about which slot
the token was in.** *The family's cost was paid one member at a time because
nobody had written the generator.*

**And the comment-forms gate should gain the `#guard` case**, which is the
concrete residue: the gate encodes the incidents it was built from, and **this
sentence names one it has not met yet.** *A rule stated once is worth a gate row
per clause — the clause the gate lacks is exactly the incident it will not
catch.*

**A FIFTH HAZARD, AND IT BITES THE DOCUMENTATION RATHER THAN THE CODE: A
COMMENT THAT DESCRIBES COMMENT SYNTAX CANNOT QUOTE IT** (analog; verify at
landing). **Lean comments NEST**, so a comment containing a worked example of a
comment delimiter **would have swallowed the file.**

> **NAME THE DELIMITERS, NEVER SPELL THEM.**

**The hazard is specific to explaining a language IN that language**, which is
exactly what a spec-mirrored tier's own documentation does constantly — and it
is invisible to a reader proofreading the prose, because **the sentence is
correct; it is the file that stops being what it was.** Nesting makes it worse
than the non-nesting case: a non-nesting comment syntax ends at the first
terminator and the damage is local and loud, while **nesting quietly extends the
comment to the next unbalanced close, which may be pages away or absent.**

**And it generalizes past comments to every delimiter a tier documents** —
string quotes, raw-string fences, attribute brackets: *wherever documentation
explains a delimiter, the explanation is written in the language the delimiter
belongs to.*

**A FOURTH HAZARD, AND IT IS A DIAGNOSIS LAW: DOT-NOTATION THEFT RE-TYPES THE
OTHER SIDE OF THE EQUATION** (Lean tier; fix built, intervention issued before
its ticket ran). A **named abbrev monad** makes `.run` bind to the **wrong
function**, and the resulting mismatch **re-types the other side** — `Except.ok`
elaborated as `EST.Out.ok`.

> **ONE MISMATCH CAN PRINT AS THREE UNRELATED ERRORS.**

> **Count defects AFTER UNIFICATION, never by error lines.**

**This is the third dot-notation entry in this register** (the `def`-alias
mis-slot above, the arity/position exhibit at §7.1a's loudness clause), and the
family has a single shape: **dot notation resolves against a type the reader is
not looking at.** What is new here is the **blast radius in the error output** —
a lane triaging by line count sees **three problems and prices three fixes**,
where the tree has one.

**AND A PROOF-STYLE CONSTRAINT IMPOSED BY THE GUARD INSTRUMENT** (Ada inch 2).
`partial` **blocks `#guard`** — it cannot reduce — so the tier is **structurally
recursive on fuel with `termination_by` DELIBERATELY ABSENT**: adding it forces
**well-founded recursion** and **takes kernel reduction back.**

> **The instrument that attests a definition can constrain how the definition
> must be WRITTEN.** `#guard` is unavailable to `partial`, and well-founded
> recursion is unavailable to the kernel — so the recursion style is chosen by
> what must remain checkable, not by what reads best.

**WALL 2 — A PROOF-STYLE RULING FROM CORE'S OWN CONSTRUCTION: STRINGS ARE
DECIDABLE BUT NOT *ORDERED BY COMPUTATION*** (Lean tier). `compare` runs through
a well-founded `utf8Decode?`, and **core ships `String.reduce*` simprocs
precisely because of it.** Consequence: **a JSON object lookup can never be
COMPUTED, only REWRITTEN** — and **~20 of the export corner's 27 obligations are
ruled rewrite-style** on that basis.

> **A LIBRARY'S OWN WORKAROUNDS ARE EVIDENCE ABOUT WHAT IT CANNOT DO. The
> simprocs are the confession.**

**That evidence form is the transferable part**, and it is stronger than reading
the definition: a definition tells you what something *is*, while **a workaround
shipped alongside it tells you what its authors found they could not get** —
measured by people who had every incentive to find a way. **Before pricing a
computation, look for the library's own escape hatch; if one exists, the
computation is the road not taken.**

**AND WALL 1 — THE MODULE SYSTEM IS OPT-IN PER *ROOT* FILE**, found before it
bit. A **non-module root sees every imported body**, so **proofs that unfold core
definitions are portable only to legacy roots.**

> **A portability constraint that depends on the CONSUMER's root, not on the
> proof.** The same proof is portable or not according to a property of the file
> that will import it — which is invisible from where it is written.

**Recorded as a wall rather than as a bug** because nothing is broken: it is a
**boundary on where a proof style may travel**, and a tier that writes
unfolding proofs has silently chosen its consumers.

**AND THE ONE-SECOND-BUILD RULE — a positive artifact, not just a positive
assertion.** `exit 0` with **no `Build completed` line is not evidence**: a
build that did nothing and a build that did everything exit the same way.
The evidence is **the olean mtime landing in the build's second**. That is
the same discipline as the positive assertion below, carried one step
further — from *"do not infer success from the absence of errors"* to
*"name the artifact whose existence success would have produced."*

**And the wrapper asserts success POSITIVELY**, which is §5.4a implemented
rather than described: it greps for `Build completed successfully` instead
of grepping for errors, because — in its own words — *an argument error and
a resource kill both emit no line the failure greps look for, and "no error
found" must never read as "the build happened".*

**AMENDMENT 9 — a FIFO TICKET QUEUE, because the spinlock starves.**
Measured cause: the lock changed hands between four lanes while one
watched, and **a lane that releases and immediately re-acquires beats a
poller every time** — so waiting politely is a losing strategy and the wait
is *unbounded*, not merely long. The C lane lost **five consecutive
handoffs while queued first**. A `mkdir` spinlock has no queue discipline;
the fix is a ticket.

* the queue is a directory, `/tmp/ls-build-queue/`;
* each lane creates a ticket named `"$(date +%s%N)-$$-<lane>"`;
* **only the OLDEST ticket attempts the `mkdir`** — everyone else waits;
* stale tickets are reaped by **pid liveness**, under amendment 8's
  discipline;
* observed working: **FIFO order held, tenures ~2 minutes.**

**AMENDMENT 10 — THE OWNER PID MUST SPAN THE TENURE.** A multi-stage tenure
— two builds under one lock — that writes a **per-stage** `lake` pid invites
a **CORRECT** staleness reclaim the moment stage 1 exits: the reaper does
exactly the right thing with a pid that stopped describing the tenure.
Write the pid of the **lock-holding script**, whose lifetime *is* the
tenure, never a child stage's. **The two-part staleness test is unchanged —
it was right; the owner file was lying.** Measured today, by the lane whose
own owner file lied to it.

**AMENDMENT 11 — THE LOCK COVERS ALL LEAN EXECUTION, not just `lake build`.**
Any Lean process is Lean execution: `lake env lean` on a real module, a
`--self-test` that elaborates, an instrument that shells out. Under a
tenure: **`LEAN_NUM_THREADS=2`**, **`nice -n 19`**, and a **3 GB RSS kill
line** measured over *this script's own descendants* — never over the box,
which would let one lane kill another's chain. **Thomas's own processes
have absolute priority**; a training run outranks every tenure, and a lane
that would hold the machine's whole Lean allowance waits for a quiet
machine and a ticket.

**A11's FIRST NEAR-MISS CAME FROM AN INSTRUMENT, NOT A LANE (2026-08-23,
`a9f7867`) — recorded here rather than minted as a new amendment, because the
amendment that governs it already exists.** A new `tools/ci.sh` step selected
tools by content and **selected `ci.sh` itself**, so CI re-entered CI and
started an **unticketed `lake` build**. Every clause of A11 and A9 was in force
and none was violated *by a lane* — the build was started by a **tool**, and
tools do not take tickets.

> **A9's queue disciplines LANES. A11 says the lock covers all Lean execution
> — so a tool that can start Lean is a lane that never queued.**

The root cause is §5.4's self-selection law (an instrument that selects by
content matches its own source); the reason it belongs in this register is the
**failure channel**: it produced no error, only a **hang**, which is precisely
the state the queue's staleness machinery is worst at reading — an unticketed
build looks to every reaper like a lane whose owner file is simply missing.
**Any gate step that can invoke Lean is inside the tenure discipline**, and the
cheap form of that is what the lane did: a per-tool timeout, so a hang cannot
become a tenure.

**ESCALATED THE SAME DAY — THE NEAR-MISS BECAME THE INCIDENT (`qol-36`).**
The paragraph above was written while this was still a hang somebody noticed.
Hours later the same re-entrancy ran **26 deep** on an unseeded clone: 26
`lake build`s, no ticket, no `nice`, load ~30 for twenty minutes, 3.2 GB of
Mathlib built from nothing. **The law was right and its severity was
understated**, which is recorded rather than edited away — a charter sentence
is present-tense prose and gets fixed, but a *wrong estimate of how bad
something is* is worth leaving visible next to what it turned into.

**THE FIX IS THREE LAYERS, and the shape generalizes past `ci.sh`:** (1) the
entry point **refuses arguments** (§5.4); (2) an **environment sentinel**
(`LS_CI_SELF_TEST`) rather than an argv check, because it is inherited by
**every descendant at any depth and through any argv**, which is exactly what
an argv or filename guard cannot do; (3) under the sentinel, **`lake` itself is
stubbed** with a no-op that exits loudly, so a self-test **cannot reach a real
build** even if a future edit re-introduces the call. Layer 3 is A11 as a
mechanism instead of a rule: *any `lake` invocation needs a ticket or a stub,
and a self-test has no ticket.*

> **A guard against RE-ENTRY must live in something INHERITED, not in
> something PASSED.** Depth and argv are exactly what the recursion controls;
> the environment is what it cannot rewrite.

**AND THE COORDINATOR'S RULING ON THE PART THE LANE FLAGGED AS NOT ITS OWN:
`ci.sh`'s `lake-build` step is HOST-GATED** — ruled, and **implemented in
`a1bb01e`** (`docs/backlog/qol.md` `2026-08-23-qol-37`; `--verify-guards` 14
ok). It builds under `GITHUB_ACTIONS`;
locally it **skips loudly and points at `tools/triad.sh`**, and **no local
override reaches a bare `lake`.** The lane was right to flag rather than fix
it: shared infrastructure whose default is *build the world* is a machine-wide
setting, not a lane-local one. The rule it lands, stated so the next such tool
inherits it —

> **A step that can start Lean names the HOST it is allowed to start it on.
> Off that host it does not degrade quietly to a smaller build; it REFUSES and
> names the ticketed path.**

**AND A COROLLARY THAT GUARDS THE REBASE EXCEPTION FROM BEING READ AS AN A11
EXEMPTION** (QoL, `95849db`). `--classify` used to list three hard-coded
prefixes, so a `.lean` under `probes/` or at the repo root got **no note**; the
question is now **asked of the lakefile**, and the note names the consequence:
**outside all `lean_lib` roots, never compiled by `lake build`, so a rebase
touching only it owes no re-gate.**

> **NOT COMPILED IS NOT NOT RUN.** A file `lake build` ignores is still Lean,
> and `lake env lean` on it is Lean execution — **A11 covers it regardless of
> whether any target does.**

**The two facts sit one line apart and pull opposite ways**, which is why the
note carries both: *"nothing rebuilds it"* is a true statement about the
**build graph** and says nothing about the **lock**. And the classifier's
restraint is the pattern: **the note EXPLAINS, it never DOWNGRADES** —
classification is unchanged, so a tool that has learned something new tells the
lane about it **without quietly buying it a cheaper tenure.**

**AMENDMENT 12 — TRAPS KILL DESCENDANTS RECURSIVELY, and never bare-kill a
wrapper.** `pkill -P` reaches children and **misses grandchildren**, which
is how orphaned `lake` processes survive a lane's exit and go on eating the
box outside anyone's tenure. The kill walks `ps -eo pid,ppid` as a BFS over
the *own* chain. Killing a wrapper without its descendants is the specific
mistake: the wrapper dies, its build does not, and the survivor is now
parentless and invisible to every staleness test that works by parentage.

**AMENDMENT 13 — CACHE SEEDING IS MANDATORY, and it is copy-on-write.** A
new clone is seeded `cp -Rpc` from a **warm, idle** peer — measured at
**27 s and 29 MB of real disk**, against GB-scale downloads for the same
result. The `-c` is the whole point (APFS clones the blocks); `-p`
preserves the timestamps Lake's staleness checks read. Seed only from a
peer with **no build running** (verify by parentage) and an untorn tree.

**THE A13 CAVEAT, and it has already caught three lanes: `cp -Rpc` SEEDS THE
PEER'S BRANCH TOO.** A seeded clone inherits whatever branch the peer had
checked out. Two lanes were silently sitting on `pyrebuild-monadic` and
pushing a **stale local `master` ref**, and the obvious check does not
catch it: `git rev-list HEAD..github/master` reads **0** because it
compares **HEAD**, not the ref you are about to push. So:

* **check `git branch --show-current` immediately after seeding**, and
* **push `HEAD:master`**, never bare `master`, which pushes the local ref
  rather than the work in hand.

**AND SEEDING INHERITS THE REMOTES TOO — the rule's complete form.** A
fourth lane paid a full tenure for the other half: in the seeded clones
**`origin` points at a stale local BUNDLE** (2026-08-14), so

* `git reset --hard origin/master` **silently lands a tree eight days
  back**, and
* `git rev-list HEAD..origin/master` reports **0** — nothing to pull,
  because it is comparing against the bundle, and
* a feature branch reads **"238 commits ahead"**, which looks like a
  branch-hygiene problem and is not.

**That last line explains the audit's branch-hygiene observation: same root
cause.** What looked like several lanes drifting onto feature branches was
one seeding defect wearing three different faces.

> **A seeded or borrowed clone's identity — BRANCH AND REMOTES BOTH — is
> INHERITED, not chosen.**

After seeding: run **`git remote -v`** *and* **`git branch --show-current`**,
and **compare or reset only against `github/master`** — never against
`origin`, which in a seeded clone is not what the name implies. This lane
hit the same trap from the third direction (§7.2's clone incident), and the
count is now **four lanes, one root cause.**

**THE A13 COROLLARY, MEASURED THE HARD WAY (2026-08-23, `qol-36`).** The clone
that ran the 26-deep recursion was a **plain `git clone`, never seeded**. So the
accidental build had nothing to build *from*: it fetched and built Mathlib from
zero and left **3.2 GB** of `.lake` behind — **not an invalidated cache, a cache
that never existed.**

> **An unseeded clone is permanently ONE ACCIDENT away from a full Mathlib
> build.** A13's *27 s and 29 MB* is the price of not being in that state.

**AND THE SHARP HALF: `check.sh --iterate` HAD BEEN REFUSING THAT CLONE AS COLD
ALL ALONG, CORRECTLY** (`~/repos/lean-qol`, **seeded since `a1bb01e`** — the
state below is the one that produced the incident, not today's)**.** The refusal was right, it fired every time, and the
hazard sat **behind** it untouched — because a guard that declines to *use* a
bad state does nothing to *remove* it.

> **A correct refusal is not a mitigation. Refusing to operate on a hazardous
> state leaves the hazard for whoever does not check.**

That is a distinct failure shape from the ones this document has been minting,
and worth naming as such: the usual defect is a guard that **fails to fire**;
this is a guard that **fired perfectly, every time, and bought nothing**,
because it protected the caller rather than the machine. The practical form is
A13 as written — **seed the clone**, do not merely refuse to build in it — and
the general form is that a refusal is a control on **one path**, while the state
it refuses is reachable from every other.

**AND A TENURE NOW NAMES BOTH HALVES AT OPEN — what will be gated, and what the
lane ASKED for** (QoL, `95849db`). *"gates: `<list>`"* and *"gates asked by the
lane: `<list>`"*, composed by `gates_planned`, which calls **the same
`gates_compose` the gate phase calls**, against a `DEFAULT_FLOOR` constant that
used to be **a literal inside the phase**.

> **AN ANNOUNCEMENT THAT CAN DRIFT FROM THE PHASE LIES IN THE REASSURING
> DIRECTION.**

**Two properties, and only the second is unusual.** Printing the plan is
ordinary; **printing the two halves separately** is what makes a dropped
argument visible — *asked* and *will run* differ exactly when something ate the
request, which is the failure `argv.sh` guards from the other end (§5.4b). And
**composing the announcement with the phase's own function** is the structural
half: a re-implementation of the plan for display purposes is **a second
decision site** (§5.4a), and when the two disagree it is the *announcement* the
reader believes, because it arrives first and looks like a summary.

> **An announcement is GENERATED BY the code it announces, or it is prose about
> a plan.**

The `DEFAULT_FLOOR` extraction is the whole of the fix: **a literal inside a
phase cannot be announced without being copied**, and every copy of a value is a
place for it to drift.

**AND THE NEXT INCH PROVED THAT SENTENCE BY TRIPPING OVER IT** (QoL, `ccdc839`).
Putting `refusal_census` in the floor surfaced that **`gate_floor` carried its
OWN SECOND COPY of the list** — so **the classified and unclassified paths could
have run different gates, silently.** Both now read `DEFAULT_FLOOR`.

> **DUPLICATION IS DISCOVERED BY CHANGING, NOT BY READING.** A second copy is
> invisible while the value is stable; it announces itself the first time the
> value moves, and only to whoever moves it.

**Which is a working procedure, not just an observation**: when you change a
constant that more than one path consumes, **grep for the OLD value before you
grep for the name** — the stale copy still carries it, and the name may differ.
It is also why MEAS-28's instrument reports **contracts** as well as names
(§2.4): a second copy of a *list* rarely shares a spelling with the first.

**AND A SECOND DEFECT FROM THE SAME WIRING, which is the more instructive one
because it would have WORKED.** `gate_runner_targets` did not know the census
invokes `leanmodels-run` through its own `--runner` default: **inside the floor
it would have worked BY ACCIDENT** (the floor also names `diff_test`, which
supplies the runner) and **failed under `--gates-only`**, where a lane reaches
`--no-build` with nothing built and reads a missing runner as a **census
failure**.

> **A dependency satisfied by a NEIGHBOUR is not a dependency met — it is a
> dependency HIDDEN, and it surfaces as someone else's red.**

**AND THE FLOOR CHANGE REACHED THIS DOCUMENT, correctly and in the same
commit.** §7.1a **enumerated the floor's members**, so that sentence was **wrong
the moment the floor changed** — the QoL lane landed the doc edit with the code,
which is the doc-first norm working from the other side.

> **A DOCUMENT THAT ENUMERATES A SET OWNS THAT SET'S MAINTENANCE. Enumerate only
> what you will maintain, or point at the source of truth and let the reader
> follow it.**

This document does both in different places, deliberately — an enumeration is
**readable** where a pointer is **durable** — so the rule is not *never
enumerate*, it is: **an enumeration is a copy (see the law above), and a copy in
a charter is a copy the code cannot see.** Enumerate when the set is small and
the sentence is the point; point when the set is a moving part.

**AND THE `--classify-default` REJECTION, landed as a ruling because the
argument generalizes** (`ccdc839`). `--classify` stays **opt-in**, so a plain
`--lane X` on a docs-only diff queues a **full** tenure.

> **CLASSIFICATION NARROWS, so default-on makes NARROWING the default — every
> lane's coverage would depend on the classifier being right WITHOUT ANYONE
> ASKING.**

That is the same reading the `--gates` ruling rejected, arriving through a
convenience instead of through a flag: **a default that makes a run cheaper is a
default that makes a claim smaller**, and the lane never sees the trade because
nothing in the log records a narrowing that was never requested. (It also turns
working runs into refusals — no merge target, unstaged Lean, and `--foreign`
contradicting `--classify` by design.)

**The advisory is the resolution, and its implementation carries the second
half of the ruling**: the tenure prints one line at enqueue saying what the diff
**would** classify as and that a full tenure was queued anyway — **behaviour
unchanged** — and it runs **in a subshell**, because `classify_list` sets
`BUILD_TARGETS`.

> **An advisory that LEAKED would narrow the build it only describes.**

**A description that can change its subject is not a description.** The subshell
is what makes *"advisory"* true rather than intended, and it belongs in the same
family as the announcement rule above: **the safe way to talk about a phase is
to call its function; the safe way to talk about a phase WITHOUT running it is
to make leakage impossible.**


**AND A BUILD LOG MUST SAY WHOSE IT IS** (QoL, `b2150ae`). `triad-build.*` held
**only lake output** — no ticket, no lane, no branch, no tree — so a lane
grepped **68 of them** for its own tag and **matched NOTHING**. **Every log was
still on disk; not one could be attributed.**

> **An artifact with no identity is not evidence — it is storage.**

Each attempt now stamps **one identifying line first**, per attempt because the
redirect truncates (`header >`, `lake >>`), keeping one-attempt-per-log exactly
as before.

**AND ITS INERTNESS IS ASSERTED, NOT REASONED ABOUT — which is the part worth
copying.** A header riding **inside the file whose failures are COUNTED** is a
change to the input of every downstream reader, so the claim *"it changes
nothing"* is checked: **the same red log with and without it yields
byte-identical error-line, failed-module and axiom-ledger verdicts**, and it
**carries no hostname**.

> **A stamp added to a measured artifact owes a DIFFERENTIAL: the same input,
> with and without it, must produce the same verdicts.**

**The temptation is that inertness is obvious** — a comment line, a header, a
banner — and it is obvious right up until a counter matches on a substring or a
reader keys on the first line. *"Obviously inert"* is exactly the reasoning
§5.4a keeps convicting; **one differential run retires it.**

**AND THE SCRIPT PRINTS ITS PROTOCOL LEVEL.** Audit #2 found **two drifted
copies of `tools/triad.sh` in `/tmp`**. Copying before editing is legitimate —
bash reads a script **incrementally**, so editing one that is running corrupts
it — but a copy whose diffs never land is a private script again, at the 38%
violation density this section already prices. `tools/triad.sh --version`, and
one line at tenure open, name the protocol level implemented
(`base 1-6 + A4-A13 + A16`) and the sha. Drift becomes visible in the log
instead of invisible in a temp directory.

**One operational note on the wrapper**: `--lane` rejects hyphens
(`[A-Za-z0-9_.]+`), and the reason is Amendment 9's ticket format — a
ticket is `<epoch>-<pid>-<lane>`, so a hyphen in the lane tag breaks the
field parse the FIFO queue depends on. Lane tags are bare words.

**`tools/triad.sh` is the canonical wrapper**, and adoption is the point of
having it: private per-lane scripts were measured at a **38% violation
density** across the applicable protocol cells, and a prose register can
sit one amendment behind its own birth — as §7.1a's did, by two minutes —
while **a missing amendment in a script is a diff.**

**AMENDMENT 14 — A FULL-TREE BUILD IS QUIET-MACHINE-ONLY.** Lake has **no
process-count cap**, so a full build fans out as wide as it likes — and on
a box already in swap it is **the first thing jetsam takes**. The rules:

* **exit 137 is never red** (base rule 2, and now with a named cause);
* **ONE retry**, then stop retrying and switch strategy;
* fall back to **SCOPED builds** (`--build-target`), and when you do, the
  landing carries a **§5.4a coverage statement** — *what was built, what
  was not, and therefore what the green covers*;
* **CORRECTION to that guidance: a scoped coverage statement needs a GREEN
  to scope a DELTA against.** A coverage statement says what this green
  covers *relative to a known-good baseline*; **a red full build leaves
  nothing to scope**, because the untouched part's status is unknown
  rather than good. So after a red, **the next build is FULL again** — a
  scoped build is how you extend a green, never how you recover from a
  red;
* **CANCEL A QUEUED TICKET RATHER THAN VALIDATE A KNOWN-WRONG TREE.**
  Recorded as the right move: ES cancelled its own queued ticket on
  discovering two wrong answers, instead of spending a tenure on a verdict
  it already knew was about the wrong state. **A tenure is the scarce
  resource** (A9's queue exists because it is), and a green over a tree
  with a known wrong answer is **a number about the wrong state** — §5.4a
  applied to *scheduling* rather than to reporting. Re-ticket after the
  fix; the queue position is cheaper than the tenure;
* the **full triad stays OWED**, discharged when the box is quiet:
  **load < 5 and swap < 1 GB**.

**AND THE TRIAD SUMMARY IS NOT A COUNT — measured on the wrapper itself.**
`tools/triad.sh`'s "first failures" block is
`grep -E '^error|✖' | sort -u | head -8`: **deduplicated and truncated at
eight.** Worse, **`lake` stops at the first failing module**, so the log
it summarises is already partial. A "one error in 839 targets" line
reported from a red triad came from exactly this block — and a failure
count taken from it is a **LOWER BOUND on sites, never a count.**

> **The triad summary LOCATES; the full log COUNTS.**

**IMPLEMENTED, 2026-08-23** — the block quoted above is the defect *as found*.
`tools/triad.sh` now prints, on any red build, counts taken from the **whole**
log: failed modules (`✖` lines), error lines **total and distinct** with the
**amplification ratio named** when they differ, and how far `lake` got before
it stopped. The preview is labelled **`first N of M`** and still only locates.
The dead `monadic_gate` patterns went with it — that harness was deleted in
`eeeb1fd`.

**AND THE GATE LINE HAS THREE STATES, not two — a distinction two lanes
drew independently the same morning, which is the family's convergence
standard.** Reading a missing gate line requires knowing *why* it is
missing, and only one of the two absences is a verdict:

| gate line | lock | what it means |
| --- | --- | --- |
| **PRESENT** | acquired | **the gates RAN** — this is a verdict |
| **ABSENT** | **ACQUIRED** | **RED — an aborted triad.** The build failed, so the gates never ran |
| **ABSENT** | **not acquired** | **NEVER STARTED — not a verdict at all.** No tenure ever opened |

**The third row is the one that was missing**, and it is what **SV's killed
ticket** and **the Lean tier's pending one** both were. Collapsing it into
the second reports a red for work that was never attempted; collapsing it
into the first is worse. **The discriminator is whether the LOCK was
acquired** — which is why the lock line, not the gate line, is what a
reader checks first.

**And a red build means THE GATES NEVER RAN.** Build exit 1 short-circuits
the tenure, so a red triad yields **a build-error list and nothing else** —
no `docs_check`, no `diff_test`, no census. A red triad is therefore not a
triad *result* with one part failing; it is **an aborted triad**, and
reporting it as "triad: 1 failure" claims two gates that never executed.
This is §5.4a again, on the instrument that reports the other instruments:
**the number carries the state it was taken in, and "red" is a state in
which most of the numbers do not exist.**

A scoped green is a real green about a smaller claim. Reporting it as a
full triad is the flattering direction §5.4a exists to catch.

**AMENDMENT 15 — `pkill -f <path>` DOES NOT KILL A `lake build`.** Its RSS
number is superseded by A16; **this rule survives and is the important
half.** `lake`'s command line **contains no path**, so a `-f <path>` match
finds only the *workers*. Kill them and the **parent respawns them** — and
if the parent has by then lost its lock, the result is an **unlocked
orphan** eating the box with nobody's name on it. **Kill by CWD, then by
tree** (A12's recursive descent). This is the same lesson as A12 from the
matching side: identify the chain correctly *before* killing anything.

**AMENDMENT 16 — THE RSS LINE IS PER-PROCESS 5 GB / CHAIN 10 GB**, raising
A11's single 3 GB chain line. The number comes from a measurement, not a
concession: **one honest worker measured 3 251 MB** — a single legitimate
process above the old *chain* limit. **Neither lane raised its own limit**,
which is why the number is trustworthy: it was set by a third party after
the fact, not by the lanes that kept hitting it.

Two implementation defects the amendment fixes, both single-shot bugs:

* **the guard EXCLUDES ITSELF** — a watchdog that counts its own RSS
  eventually kills the thing doing the watching;
* **it RESTARTS PER ATTEMPT** — the original fired once and then stopped
  watching, so a retry ran unguarded.

**16.2 — RETIRING A RUNNER: `SIGKILL` superseded scripts, and delete the
file in the same breath.** `SIGTERM` runs **EXIT traps**, and a
**pre-A7 trap deleted a third lane's lock** on its way out — the retiring
script's last act was to break the amendment that replaced it. So a
superseded runner is **SIGKILL**ed and its file removed immediately, or the
next person to find it will run it.

**AND SIGKILL BYPASSES THE EXIT TRAP — WHICH IS ALSO WHAT REMOVES THE
TICKET.** Measured by the Lean tier on its own migration. The trap that
`SIGKILL` skips is the trap that does `rm -f "$QUEUE/$TICKET"`, so a
retired **ticket-holding** script leaves its ticket behind: a **phantom at
the queue head**, blocking every lane behind it (A9 gives the lock to the
oldest ticket) until a human reaps it.

**So retiring a runner is a THREE-step act, in one breath:**

1. **`SIGKILL`** the process — never `SIGTERM`, per the trap hazard above;
2. **delete the file**, or the next person to find it runs it;
3. **remove its ticket by hand** — `/tmp/ls-build-queue/<ts>-<pid>-<lane>`.

**The third step exists BECAUSE of the first**, and that is the shape worth
noticing: the fix for one hazard *creates* another. `SIGTERM` would have
cleaned the ticket up and might have deleted a third lane's lock;
`SIGKILL` protects the lock and orphans the ticket. There is no signal that
does both, so the manual step is not an oversight in the amendment — it is
the amendment's price, and leaving it implicit is how the two-step version
of this rule shipped incomplete.

> **Adoption is the most dangerous moment**, and **an amendment takes
> effect when the last script predating it is dead** — not when it is
> written, not when it is landed, and not when the first lane adopts it.

That is the protocol's own version of §9.2's by-touch discipline, and it is
sharper: by-touch tolerates a slow migration because the old artifact is
*inert*. A superseded **runner is not inert** — it holds locks, kills
processes and runs traps — so its migration window is a hazard rather than
merely a delay.

**16.2's SECOND INSTANCE, AND IT CONVICTED ITS OWN AUTHOR (2026-08-23, QoL,
`docs/backlog/qol.md` `2026-08-23-qol-36`).** The lane that carries 16.2 in its
own ledger diagnosed a CI re-entrancy near-miss, added a belt, verified it
green — **and left its own hung pre-belt process running.** That process had the
old `selftests` in memory and went on spawning: **26 instances of `ci.sh`**,
each starting `lake build` with default parallelism, no `nice` and **no
ticket**. Load ~30 for twenty minutes.

> **The guard never failed, because the guard was never in those processes.**
> A fix in the source does not stop what is already running.

Which is 16.2 restated from the far side, and it earns a rider the amendment
did not have:

> **The rule applies to YOUR OWN runners FIRST. The author's surviving process
> is the likeliest in the tree to predate the amendment** — it was started
> before the fix existed, by the person who then stopped thinking about it.

**And the incremental-read hazard fired in the same window**, which this
section already names: the lane **edited `ci.sh` while 26 instances were
executing it**, and reports honestly that it *"cannot cleanly separate 'ran the
old code' from 'read a shifted file'."* Record that admission rather than
resolving it — **an incident with two indistinguishable causes has two causes**,
and a post-hoc pick between them would be a reconstruction (§5.4a).

**A PRICING CLIFF IN `--classify`, measured — budget it deliberately.**
Adding **one new `Examples/` subdirectory** made classification widen from
**four Go modules to the WHOLE `Examples` library**: **91 s → 37 minutes,
a 25× step.** It is a cliff rather than a slope, so a lane that has been
paying 91 s has no warning before it pays 37 minutes. Two consequences
worth planning around: **a new `Examples/` subdirectory is a scoping
event**, not just a file addition; and **the cheap classify a lane budgets
from yesterday's tenure is not the one it will get today** once the
directory lands. Check the scope before the tenure, not after.

**`tools/triad.sh --classify` IS OUR-REPO-ONLY BY CONSTRUCTION**, and a
lane pointing it at a foreign checkout will get a confident wrong answer
rather than an error. Two reasons, both structural:

* **the class floor hard-wires our gates** — `docs_check` / `diff_test` /
  `refusal_census` are named in the classifier's floor and in the default
  gate set, and a foreign project has none of them;
* **classification diffs against `github/master`** (the flag's default
  `--against` ref), which names **our** master. A foreign checkout either
  has no such ref or has one that means something entirely different — and
  §7.1a's seeding caveat is the reminder that a remote's *name* is not its
  identity.

**Until a `--foreign` flag lands** (the QoL lane holds the request), a
foreign checkout — `lean4lean`, `spectec` — is built with **plain
`--gates` under the full tenure discipline**: the lock, the queue, the RSS
line and A14's quiet-machine rule all still apply. What does not apply is
the *scoping*, so those tenures run the full gate set the lane names
explicitly, and their landings carry a §5.4a coverage statement saying so.

**AMENDMENT 17 (DRAFT) — PROOF ITERATION IS A DIFFERENT SHAPE FROM BUILD
VERIFICATION.** The measured problem: **a 300-line proof at one compile per
tenure is not a session's work** — roughly **80–88 minutes per compile**
under the queue. A11 made the lock cover all Lean execution and subsumed
old rule 3's exemption; that **fixed the starvation of BUILDS and, in the
same move, priced ITERATION out.** A17 re-licenses a narrow slice, with the
conditions rule 3 was missing when it was abused.

**A single-file iteration loop** — `lake env lean <file>`, which **writes no
oleans** — is permitted **without a ticket** under **all** of:

* **(a)** machine **load < 10 AND swap < 50%**, checked **immediately
  before each run** (A8's atomic-re-read discipline, applied per
  iteration) — **BUT SEE THE INSTRUMENT DEFECT BELOW: the swap half of this
  line has been measuring a HIGH-WATER MARK, not pressure**;
* **(b)** at most **ONE such process per lane**, `nice -n 19`,
  `LEAN_NUM_THREADS=2`;
* **(c)** the file's imports' **oleans are WARM** — otherwise it silently
  becomes a dependency build, which is §7.1's cold-clone trap;
* **(d)** it **YIELDS**: the loop pauses while any build tenure is in its
  build phase on a memory-tight box, and **swap > 50% = stop**.

**Tools side:** `check.sh` gains an **`--iterate`** case implementing
(a)–(c), so the conditions are **checked, not guessed** — which is the
whole difference between this and the rule-3 exemption it replaces.

**FIVE TIGHTENINGS FLAGGED FOR RULING**, in the order I would apply them:

1. **THE PER-LANE CAP DOES NOT COMPOSE — this is the load-bearing one.**
   (b) caps one process *per lane*; N lanes each obeying it is N
   unticketed Lean processes, which is the hazard the lock exists for.
   **The check should count ALL iteration processes machine-wide, not the
   lane's own** — the same class of error as measuring RSS over the box
   instead of over your own chain, with the scope inverted.
2. **NO RSS CEILING.** (b) bounds count and niceness but not memory, and
   A16 exists because **one honest worker measured 3 251 MB**. An
   unticketed, unsupervised process needs an explicit line — I would set
   it **below** A16's 5 GB precisely because nothing is watching it, and
   make exceeding it a kill rather than a pause.
3. **(d) SHOULD MIRROR (a) ON BOTH CONDITIONS.** (a) starts on *load < 10
   AND swap < 50%*; (d) stops only on swap. A loop that starts at load 9
   keeps running as load climbs, since swap alone gates it. **Pause on
   `load ≥ 10` OR `swap ≥ 50%`.**
4. **A11's THOMAS-PRIORITY CLAUSE IS UNTOUCHED, and should be said.** A
   training run outranks every tenure — and therefore outranks an
   iteration loop, which stops for it and not merely for swap.
5. **THE CHECK IS PER-ITERATION AND THE YIELD IS BEST-EFFORT.** There is a
   window between passing (a) and a tenure starting, so A17 is a
   *courtesy* protocol, not a guarantee — which is the strongest argument
   for tightening 2: the RSS ceiling is the backstop that does not depend
   on anyone observing anything in time.

**AND A SECOND DATA POINT ON THE A15 → A16 CHAIN FIGURE.** The C lane's
**stale watchdog killed a HEALTHY build at 6 171 MB against the superseded
6 144 MB line.** That is A15's number doing active harm after it was
superseded — a retired limit still enforcing — and it confirms both halves
of A16: the raise was right, and **canon's 10 GB chain line is the correct
one.** It is also A16.2 in miniature: **an amendment takes effect when the
last script predating it is dead**, and this watchdog was not.

**AND A SIXTH TIGHTENING, ARRIVING AS A MEASURED INSTRUMENT DEFECT RATHER THAN A
DESIGN NOTE — AND IT REPRICED A WHOLE DAY** (tools lane, dispatched priority).
**A17's swap line reads `vm.swapusage`, which on macOS is a HIGH-WATER MARK, not
a pressure reading.** Measured: **88.5% against the line while
`memory_pressure` reported 59% free.**

> **A BOX THAT SWAPPED ONCE HAS A17 CLOSED FOR THE REST OF ITS UPTIME.**

**So the entire one-shot-compile regime of 2026-08-24 was an INSTRUMENT
ARTIFACT.** It shaped **Ada's one-shot discipline**, **three syntax-position
reds**, and **every lane's make-each-tenure-count behaviour** — a day of
economics set by a proxy that could only ever ratchet.

> **A REFUSAL GATE WHOSE INSTRUMENT MEASURES A MONOTONE PROXY CONVERTS A
> TRANSIENT CONDITION INTO A PERMANENT ONE.**

**AND THE FIX'S OWN FAILURE MODE ARRIVED WITHIN A DAY, ON THE RELAY RATHER THAN
THE INSTRUMENT** (Ada's inch-3 census, merged `1260af7`; **fourth coordinator
hypothesis killed today**). A relayed *"pressure ~31%"* was **`memory_pressure`'s
FREE percentage — and stale** — while the live reading was **65–70% in use,
`kern_level 2`.** **Ada measured with the landed instrument before acting** and
**declined the spine build.**

> **The amendment's own failure mode: a FREE percentage read as a PRESSURE
> percentage — same class, OPPOSITE POLARITY.**

**The instrument was right; the prose dropped the label.** Which is the
consumer-side corollary the every-line-names-its-instrument rule was missing:

> **A RELAYED NUMBER WITHOUT ITS INSTRUMENT NAME RE-CREATES THE DEFECT THE
> INSTRUMENT FIXED.**

**AND THE POLARITY FIX CARRIED THE SAME DEFECT ONE TURN DOWN** (QoL, merged
`40c093c`). The label said **`memory_pressure:free%`** while **printing the
complement.**

> **Naming the instrument was NECESSARY AND NOT SUFFICIENT: an unlabelled
> POLARITY is the same defect one turn of the screw down.**

**Labels now name the TRANSFORM — `100-free%` — not merely the source.** Which
fixes a rule this register had been stating at the wrong granularity: *name the
instrument* answers **where the number came from** and says nothing about **what
was done to it on the way.** A derived number carries **two** provenance facts,
and **the derivation is the one that flips signs.**

> **A NUMBER'S LABEL NAMES ITS SOURCE AND ITS TRANSFORM. Either alone is a
> shadow.**

*The fix for a polarity defect is not a more careful reader — it is a label the
polarity cannot be read wrongly through.*

**A bare percentage is not a measurement, it is a measurement's shadow** — and
the shadow of *free* and the shadow of *in-use* are **the same shape**. The
original A17 defect was a **proxy that could not come down**; this is **a correct
reading transported without the sentence that says which direction it points.**
*Fixing an instrument does not fix the channel that quotes it.*

**AND THE CHANNEL FAMILY HAS A CONSUMER-SIDE MEMBER: THE STALE TOOLKIT** (Ada,
building inch 3). The lane filed a residual against master and then found its
own `tools/` was **372 lines behind** —

> **"I was reporting a defect I was carrying, not one master had."**

**This is the wrong-tree family met from the reporting end rather than the
certifying end.** The usual member is *a green that certifies the wrong tree*;
this is **a RED that reports a defect that exists only in the reporter's copy** —
and it is worse for the fleet than a stale green, because **it spends another
lane's attention on a fix that is already landed.** *A defect report is a claim
about a tree, so it carries a sha for the same reason a measurement does.*

**And the structural fix is not a habit** — QoL's item-15 guard (fetch-and-warn
against the shared tools) is where this belongs, for the reason this register
keeps arriving at: **a discipline that must be remembered before every report is
a discipline that will be skipped on the report that matters.**

**AND A DEFERRAL RE-MEASURED CAN FIND THE BINDING CONSTRAINT HAS MOVED** (Ada,
same tenure: **pressure 51.0, load 6.86**).

> **A deferral names WHICH LINE BINDS. Re-measured later, the answer can be a
> DIFFERENT LINE — "blocked on load rather than memory."**

**Which is the two-instrument requirement earning its keep in the one way a
single instrument never could.** A lane carrying one gauge re-reads it, sees
room, and proceeds — **into the constraint it was not measuring.** *The pair does
not merely make the reading safer; it makes the DIAGNOSIS survive its own
success*, because relieving the first limit is exactly the event that promotes
the second.

**So a deferral is not "wait until X is under the line" but "wait until the
LADDER is under its lines"** — and a re-measurement that changes which line binds
is **a result to record, not a retry to repeat.** *A deferral whose reason
silently changes has become a habit.*

**AND THE STALE-RELAY PATTERN IS NOW COMPLETE, WITH THE COORDINATING ROLE AS ITS
REPEAT SOURCE.** *"Pressure ~31%"* was the first; *"the queue is empty, the
window is good"* is the second. **Both were TRUE WHEN SENT and both aged into
falsehood while in flight.**

> **A COORDINATOR'S SITUATIONAL STATEMENTS NEED TIMESTAMPS OR INSTRUMENTS
> ATTACHED, EXACTLY AS ANY NUMBER DOES.**

**What makes them worse than a stale measurement is that they read as
PERMISSION.** A number invites a lane to re-measure; *"the window is good"*
invites it to proceed — **so the one class of relay most likely to be acted on
without checking is the class this register had exempted**, on the unexamined
ground that it is context rather than data.

**The remedy is the one already ruled for numbers, applied to advice**: name the
instrument (`the queue at 14:02`), or say what to re-read (`check the queue
before you start`). *A relayed condition without a timestamp is a measurement
whose stamp discipline was waived because it was phrased as a sentence.*

**And the compliant behaviour is the row worth copying**: the lane **did not act
on the relay.** It **re-measured with the landed instrument**, and the decision
it then made was the opposite of the one the relay implied. *A number arriving
without its instrument is a prompt to measure, never a measurement.*

**That is a distinct failure from every other gate defect in this register**,
and worth separating: the stuck-channel family covers gates that **cannot
decide**; this one **decides correctly, on a number that never comes back
down.** A high-water mark is a perfectly good measurement of *what happened*;
it is **not a measurement of what is true now**, and a gate is a question about
now.

**THE FIX IS A BETTER INSTRUMENT, NEVER A LOOSER LINE — the third appearance of
that shape**, after the cross-lane scope narrowing and the conservative
heuristic. **All three offer the same bargain**: the gate is inconvenient, and
the cheap repair is to weaken what it demands. **All three are refused for the
same reason** — *the line was not wrong; the reading was* — and weakening a line
to accommodate a bad instrument **destroys the evidence that the instrument was
bad.**

**AND THE COST STRUCTURE IS THE PART THAT OUTLIVES THE BUG.** The syntax-position
red **class** — a doc comment, then a `set_option`, both *"a token in a
declaration slot"* — **repeated across two lanes precisely because the artifact
regime had removed the 15-second check.**

> **A defect class whose prevention cost collapsed from TRIVIAL to a
> 2000-SECOND QUEUE CYCLE.**

> **COST STRUCTURE IS SET BY INSTRUMENTS, NOT BY DEFECTS.**

**AND THE EVIDENCE IS NOW n=12, ACROSS THREE INCHES** (C inch 6): after the A17
fix, **the last nine defects cost under two minutes of machine time TOTAL**,
against **5 934 seconds for three** before it. *The law arrived with one
measurement, was corroborated by a second from another tier, and now has a
population.*

**AND IT NOW HAS ITS BEFORE/AFTER NUMBERS — the day's closing exhibit** (crunga
Rung A, merged). **Three defects cost 5 934 seconds of QUEUEING for 43 seconds
of BUILDING.** After the pressure fix, **the next two cost 20 seconds TOTAL** —
including a **`have`-vs-`let`/`letFun` defect that no amount of reading would
have produced.**

> **The instrument was the whole difference.**

**AND A LANE RE-PRICED ITS OWN PROCESS DECISION IN THE SAME REPORT THAT
BENEFITED FROM IT** (pyc inch 4). A **70-minute queue for a 67-second compile
probe**, judged *"the right trade"* in the moment and re-judged **"the wrong
trade on a busy machine — and I took only one."**

> **A cost judgement made under pressure is a hypothesis about the machine, and
> it is re-priceable after the fact with information the decision did not
> have.**

**Worth a row because the incentive runs the other way.** The probe **worked** —
the report exists because of it — and *a decision that paid is the one nobody
re-examines.* **The lane separated "it produced the result" from "it was the
right allocation"**, which are different claims about the same 70 minutes, and
only the second is about the fleet. *And "I took only one" is the clause that
makes the reversal actionable rather than remorseful: it bounds the damage and
names the behaviour that would have compounded it.*

**A 300:1 ratio between waiting and working, then a 300× collapse in the price
of a defect** — same lane, same class of mistake, **no change in anyone's
care.** That is the law stated in numbers rather than argued: *the defect rate
did not move; the price of finding one did.*

**And the `have`-vs-`let` case is the half that matters most**, because a
cheaper instrument does not merely find it faster — **it finds it at all.**
*Some defects are reachable only by running; an instrument that makes running
expensive does not slow those down, it converts them into defects nobody
finds.*

**Neither lane made a new mistake**; the same mistake simply stopped being
catchable in fifteen seconds. **A defect's rate is a property of how cheaply it
can be checked**, so an instrument that closes a cheap check does not merely slow
a lane down — **it changes which defects reach the queue at all**, and it does so
invisibly, because nothing records the checks that were not run.

### 7.2 The master branch

Many lanes push the same master. Fetch-rebase before every push; read your
own backlog section at push time rather than at draft time, because the
section number you reserved may have been taken while you worked. After
any rebase that touches `.lean`, re-run the build and the differential
before pushing — a rebase is a merge, and a merge is not a measurement.

**NEVER FETCH-REBASE WHILE A BUILD RUNS IN THE SAME CLONE** (protocol
amendment 6, from the Go lane's torn-tree incident). The build reads
**rebased files against a pre-rebase build graph** and dies with spurious
`Unknown constant` errors that look **exactly** like a broken master. The
cheap part is the failure; the expensive part is the investigation cycle
that ends by proving master was fine all along — theirs did, with all four
"missing" constants present and the diff empty.

**AMENDED — A6 COVERED ONLY HALF THE HAZARD, and the missing half is the
ordinary one.** A6 forbade *rebasing* under a running build; a corollary
extended it to a queued ticket, on the grounds that a ticket reaching the
head mid-`git` opens a tenure on a torn tree. Both are true and both are
too narrow, because of a fact about *when the tree is read*:

> **A queued tenure reads the source at BUILD time, not at ENQUEUE time.**

So **an ordinary EDIT** to a file while its ticket sits in the queue
**silently changes what the verdict is about.** Nothing is torn, nothing
fails, and the tenure is not interrupted — it simply builds a different
tree than the one enqueued. The measured near-miss: a lane would have
reported **"`instN` green"** for a run that actually built **`instN` +
`weak'`**. A true statement about a tree nobody asked about.

> **Never CHANGE THE TREE a ticket will build — no rebase, no edit, no
> stage — between ENQUEUE and RELEASE. Batch BEFORE enqueue, or after the
> verdict.**

**AND THE STAMP THAT ENFORCES THAT RULE HAD A BLIND SPOT, FOUND BY A LANE
CHECKING WHETHER IT COULD SAFELY EDIT** (Wasm; **fixed in `22ed755`**).
**`tree_stamp` WAS `git write-tree`, which hashes the INDEX. `lake` builds the
WORKING TREE.** Verified against the tool at the time: `tools/triad.sh:1181-1183`.

> **An UNCOMMITTED, UNSTAGED edit between enqueue and acquire is INVISIBLE to
> A6's enforcement — and the green would certify a tree the gate never saw.**

**THIS IS THE WRONG-TREE FAMILY ARRIVING INSIDE THE GUARD BUILT TO PREVENT IT.**
The enqueue stamp exists **precisely** to pin the certified tree, and it points
at **the one object `lean` does not read.** It is §5.4b's pointer question —
*what is this pointed AT?* — aimed at a **guard** rather than at a gate, with
the sharpening the analog apex supplied (§5.3): **correctly motivated,
correctly implemented, against the wrong object.** Nothing here is a slip; the
`write-tree` call does exactly what it says, and what it says is not what the
build reads.

**AND A COMPLIANCE INSTANCE WORTH THE RIDER, because it shows the rule being
OBEYED rather than enforced** (pyc lane, inch-3 design). The lane needed to read
master while holding a ticket on a **frozen worktree**, and **read through an
isolated BARE MIRROR** rather than fetching into the worktree — so **the enqueue
stamp never came near the ticketed tree.**

> **READING master and BEING ON master are different needs. A bare mirror
> satisfies the first without touching the second.**

**The rule §7.2 states is *do not change the tree a ticket will build*, and the
naive reading is that a lane holding a ticket is simply blind until it
releases.** It is not: **the constraint is on the WORKING TREE, not on the
lane's knowledge**, and a separate read-only clone is outside the constraint
entirely. **A lane that believes a protocol forbids more than it does will
either stall or break it** — which is `-58`'s reputation-versus-mechanism law
arriving as a success rather than as a defect: *the lane that reads the
mechanism finds the room the reputation denied.*

**RESOLVED (`22ed755`, merged `b98b4d0`; verified here — `STAMP_VERSION="v2"`
at `tools/triad.sh:1192-1208`).** The stamp now hashes the working tree through
a **temporary** `GIT_INDEX_FILE`, so the lane's own staging area is untouched;
`add -A` catches untracked files (a new `.lean` is exactly what must not slip
in) and honours `.gitignore` (so `.lake` churn cannot defeat it), **at both
ends**, for **0.31 s cold against 0.015 s**, twice per tenure. Two
consequences worth keeping. **An index-only edit is now ACCEPTED** — content
staged but absent from the working tree will never be elaborated, so it is not
part of what the tenure certifies, and the old stamp's refusal of it was a
false alarm in the opposite direction. And **stamps carry a version**: a `v1`
stamp compared against a `v2` one reads `unversioned`, which **accepts and
logs** rather than refusing, because the two hash different objects and an
answer to one is not evidence about the other — eight tenures were queued when
the fix landed. **OPS-79's interim rule therefore SUNSETS: it applies only to
tenures whose tickets carry v1 stamps.**

**AND THE GRACE WINDOW NEEDS A DIRECTION, ruled on an intervention** (Lean tier;
caught **before** the ticket ran, from the lane's own honest report line). The
lane created a **NEW ticket under its worktree's pre-rebase `v1` stamp with a
196-line rewrite UNSTAGED** — so **the pending green would have certified the
old red tree while building the new file.** Ordered: **dequeue, commit, rebase,
re-enqueue.**

**The law already existed** (MEAS-202 plus the working-tree fix). What the
incident adds is the boundary on the tolerance itself:

> **ACCEPT-AND-LOG TOLERANCE IS FOR TICKETS IN FLIGHT, NOT A LICENSE FOR NEW
> ONES. A migration's grace window needs a DIRECTION.**

**A grace window without a direction is not a migration, it is a second
protocol** — and it is self-perpetuating, because the cheapest way to stay
inside it is to keep minting tickets in the old form. **The tolerance exists to
avoid killing work that was already queued when the rule changed**, which is a
statement about *when the ticket was created*, not about *which stamp it
carries*.

**And the detection channel is worth its own line: this was caught from the
lane's own report**, not from a gate. **A lane that reports its actual state —
including the unstaged rewrite — is doing the one thing no instrument in this
tree can do for it**, and the intervention was possible only because the report
was honest before it was flattering.



**AND HOW IT WAS FOUND IS ITS OWN LAW.** The lane **almost deferred a safe
edit** for fear of the stamp, then **read the stamp's implementation instead of
obeying its reputation** — and found **the fear unfounded and the guard hollow
in the same read.**

> **A GUARD'S REPUTATION AND ITS MECHANISM DRIFT APART SILENTLY. The lane that
> reads the mechanism inherits BOTH facts.**

**AND AT THE BUILD-SYSTEM LAYER, THE MECHANISM CANNOT BE READ AT ALL — IT MUST
BE RUN** (SV's red, diagnosed and re-ticketed). **The glob is by PATH, not by
import graph**: the hold-out **never existed**, and the earlier escape **worked
by accident of location.**

> **The way to know which you have is to BUILD, not to reason about the
> lakefile.**

**Reputation-versus-mechanism with the mechanism out of reach.** The earlier
rows in this family say *read the implementation rather than obeying the
reputation*; here **reading is what produced the wrong answer** — a lakefile
describes a selection rule, and **which files that rule selects is a fact about
the tree, not about the rule.** *An escape that worked by accident of location
is indistinguishable, on the page, from one that worked by design.*

**AND THE MECHANISM YOU READ MUST BE THE CURRENT ONE** (Lean tier, same
closure). The lane's worktree was **pre-fix only because it had not rebased** —
**the fix had been on master for hours.**

> **The correct reflex on discovering a tool defect is to check whether it is
> ALREADY FIXED UPSTREAM OF ME before reporting it as residual.**

**This is the reputation-versus-mechanism law with a third failure mode.** That
row warned about a guard's *reputation* drifting from its *mechanism*; here the
mechanism was **read accurately and was simply old** — the lane's copy of the
tool, not the tool. **A defect measured in a stale worktree is a fact about the
worktree**, and it is the one kind of tool finding that **costs the register
nothing to check and everything to publish**: a residual-defect report against a
fixed tool sends the next lane to re-derive a repair that already exists.

**Two reads, not one**: what does the mechanism do, **and is this the mechanism
master has?** The second is a `git log` on one file.



**Both directions of that drift cost something, and they are usually paid by
different people.** An over-estimated guard **taxes every lane that obeys it**
— here, a deferred edit and a lost hour, for a rule that did not apply. An
under-estimated one **taxes whoever eventually trusts a green it did not
earn.** *The same read settles both*, which is the practical argument for
reading a guard before working around it: **the cost of the read is bounded and
it is the only move that can return either answer.**

**AND THE DISCLOSURE IS WHAT MADE IT A FINDING RATHER THAN AN EXPLOIT.** The
lane's own words: *"mine is comments-only and I'm declaring it rather than
relying on the hole."*

> **THE SAME HOLE, USED SILENTLY, IS INDISTINGUISHABLE FROM THE ADA INCIDENT.
> DECLARED, IT IS A TOOL DEFECT WITH A NAMED FIX.**

**This is the drift family's declaration rule (§5.4b) one level up — at protocol
compliance rather than at an artifact.** There, prior declaration is what
separates a legitimate baseline change from a silent regression; here it
separates **a lane working within a known-imperfect protocol** from **a lane
quietly relying on the imperfection**, and *after the fact the two produce the
same tenure.* **Declaration is cheap only before**, and it is the entire
difference between a hole that gets fixed and a hole that gets used.

**AND THE RE-POINTING FLIPPED ONE OF THE GUARD'S OLD VERDICTS, DELIBERATELY.**
The old stamp **REFUSED an index-only edit**; the new one **accepts** it —
*content staged but absent from the working tree will never be elaborated, so it
is not part of what the tenure certifies.* **The old refusal was a false alarm
in the other direction.**

> **RE-POINTING A GUARD IS NOT MONOTONE TIGHTENING. A guard aimed at the right
> object flips some of its old verdicts, and each flip owes its reasoning WHERE
> THE CHECK LIVES.**

**This is the necessary companion to MEAS-202**, and the reason it needs saying:
*"we fixed the guard"* invites the reading that everything it used to reject it
still rejects, plus more. **A re-aimed guard is a different guard** — some old
reds were about the old object and do not survive the move — and a lane meeting
the newly-accepted case a year from now will ask whether it was considered. The
answer belongs **in the test comment**, not in a landing message that no one
greps.

**AND THE SAME BLINDNESS WAS ONE LEVEL DOWN, FOUND BY THE FIX RATHER THAN BY A
SECOND INCIDENT.** `record_green` also called `write-tree`, so a green taken
with an unstaged edit **recorded the index's hash and could be judged CITABLE
while the elaborated content was something else.** One source, two consumers,
one fix.

> **WHEN A DEFECT IS FOUND IN A PRIMITIVE, CENSUS ITS OTHER CALLERS BEFORE
> CLOSING. The second consumer is found by the FIX, not by the second
> incident.**

**The exposure audit came back clean** — all merged greens were porcelain-clean,
and **clean ⇒ index == working tree**, which is the sort of argument worth
keeping: *the defect was live, and the population that could have been affected
was measured rather than assumed.* This is MEAS-28's one-source rule read
backwards: sharing a primitive is what made **one** fix sufficient, and it is
also what made **one** defect reach two guards.

**AND THE DELTA-VS-MASTER LINE LANDED WITH ONE DEVIATION FROM THE BRIEF, WHICH
IS THE INCIDENT ONE LEVEL DOWN.** *"0 `.lean` files"* is **not** docs-only:
`lakefile.toml`, `lean-toolchain` and `lake-manifest.json` carry no `.lean` and
**invalidate the entire graph.** Printing `DOCS-ONLY` for them would **reproduce
the tree/label mismatch the line exists to expose.**

> **ASK THE ORACLE THAT ALREADY ANSWERS THE QUESTION. A label re-derived inline
> is a SECOND classifier, and it will be weaker than the first.**

So the label is asked of `classify_path` and prints
`NOT docs-only (lakefile.toml)`. **A line added to catch a mismatch that
introduces a mismatch of its own is the failure this whole section keeps
finding**, and the fix is the one §5.4a already gives for two tools disagreeing:
**one reader, and it is the one that already exists.**

**AND THE ABSENCE FAMILY HAS THREE MEMBERS AT THIS PRINT STATEMENT, NONE OF
WHICH MAY LOOK LIKE A MEASUREMENT**: `n/a-foreign-tree` (refused before
trying), `n/a-no-merge-target`, `n/a-unrelated-histories` — against **`0
files`**, which **is** a measurement.

> **A TAXONOMY OF ABSENCE BELONGS AT THE PRINT STATEMENT, because that is where
> a zero and a non-answer become indistinguishable.**

Every earlier member of this family was an absence **inside** an instrument (a
`null` on an absent repo, a zero-row census, a `sed` with no input). **This one
is at the boundary where the instrument speaks**, and it is the last place the
distinction is still available: **once `0` is printed, no reader can recover
whether the question was answered or declined.**



**AND A HOLE THE STAMP DOES NOT COVER: A LANE INHERITS ITS BASE'S RED, AND THE
QUEUE IS LONG ENOUGH FOR THE FIX TO LAND INSIDE ITS OWN TENURE** (pyc2, aborted
attempt 1 — **not its red**). Measured timeline:

| moment | fact |
| --- | --- |
| **00:32** | base committed, **already red** for a full build |
| **02:27** | tenure opens |
| **02:30:54** | **the fix lands on master — 3 m 22 s into the build** |
| **03:02** | death, on **the one already-fixed module**, at **3 771/3 772 targets built** |

**Cost: 116 minutes of the machine-wide tenure to rediscover a defect that was
fixed while the build ran.**

> **NOTHING CHECKS THAT A TICKET'S BASE WAS EVER GREEN.** The enqueue stamp pins
> *what will be built*; it says nothing about whether that tree ever passed.

**AND THE MITIGATION MET ITS INTENDED CASE ON DAY ONE** (QoL's base-staleness
warning; pyc3 acquired with **`BASE STALE: 4 commits behind`**). It was **read,
reasoned about, and CORRECTLY NOT ACTED ON mid-tenure** per A6 — the four
commits touch **disjoint files.**

> **The warn-never-refuse design was validated by a lane DECLINING to act on
> it.**

**That is the outcome a warning is FOR, and it looks like nothing happened.** A
refusing gate here would have killed a tenure over a staleness that could not
affect it; **a warning that is read and reasoned about produces exactly this: a
lane that knows something it did not know, and changes nothing.** *The evidence
that a warning is correctly calibrated is a documented decision NOT to act, not
a saved incident.*

**This is the wrong-tree family's remaining corner**, and it points the opposite
way from all the others: those catch a green certifying **the wrong tree**; this
is a **red certifying nothing at all**, paid for at full price. **And the
duration makes it worse rather than better** — the longer the queue, the more
likely the fix lands *inside* the tenure, so **the tenure is refuting a claim
that is no longer being made.** Mitigation (fetch-and-warn at enqueue **and** at
acquire) is dispatched to the tools lane.

**COMPANION — THE ABORT REPORT'S OWN QUALITY, which is why this is legible at
all.** The lane reported **"aborted, not red-on-my-work"**, with the conviction
drawn from **the other lane's commit message.**

> **THREE STATES, NOT TWO: green, red-on-my-work, and ABORTED. A report that
> collapses the third into the second concedes a defect the lane does not have.**

**And the third state is the one a lane is least motivated to claim**, because
it reads as an excuse — which is exactly why it needs a name and a standard of
evidence. **The standard here was met**: the conviction came from **another
lane's own words**, not from the reporting lane's reconstruction.

**AND THE STALENESS HAS NOW BEEN SPLIT, MEASURED — most of it is the QUEUE, not
the BUILD** (Ada). A tenure came back **53 commits behind**, and the obvious
reading is that a long build fell behind a fast tree. The split says otherwise:
**104 minutes of QUEUE** accounted for the bulk, and **4 commits** arrived
during the **78-minute build**.

> **The staleness came from the QUEUE, not the BUILD.**

**Which relocates the fix.** *"Builds are too slow"* prescribes shrinking the
build — the expensive, technical answer — while the measurement prescribes
**shortening the wait or re-reading at the head**, a scheduling change. **A wait
is invisible in the artifact**: the build's log shows 78 minutes and says
nothing about the 104 that preceded it, so the only number a lane has to hand
attributes the whole gap to the one phase it can see.

> **Attribute staleness to a PHASE before prescribing a fix. Enqueue-to-start
> and start-to-finish are different costs with different owners, and only one of
> them appears in the build log.**

**AND THE TOOL-SKEW GUARD THAT CLOSES THE CONSUMER SIDE IS BUILT ON IDENTITY,
NOT ANCESTRY, AND IT NEEDED THREE STATES TO BE USABLE** (QoL item 15).

> **MATCHES NOTHING = LOCAL WORK, NEVER BEHIND.**

**A bare *differs-from-master* would refuse every lane editing the tool, starting
with the lane that maintains the guard** — the self-refuting shape this register
has now met at three gates. *Two states force a guard to call every edit a
defect; the third state is what lets a control coexist with the work that
improves it.* **`matches master` / `matches an older master` / `matches nothing`
are three different facts, and only the middle one is skew.**

**AND THE GUARD STATES ITS OWN LIMIT IN THE CODE, WHICH IS THE PART TO COPY:**

> **A superseded copy PREDATES the thing that would refuse it. This closes every
> skew that begins AFTER it lands.**

**Every guard has that boundary and almost none say so.** A control installed
today cannot reach copies made yesterday — *the population it governs is defined
by its own landing date* — and a reader who does not know that will read a green
as *no skew* when it means **no skew among copies this guard has ever seen.**
**Writing the limit where the guard lives, rather than in a landing note, is what
keeps it attached to the artifact it qualifies**; a limit stated only in prose
gets separated from its guard by the first person who quotes the green.

**AND A GIT MECHANIC THAT DEFEATS THE OBVIOUS WAY OF STAMPING A LANDING** (Go
E1, `4a9f9ec`).

> **A COMMIT CANNOT CONTAIN ITS OWN HASH.** An `--amend` to insert it
> **invalidates it**, leaving a citation to a **destroyed** commit.

The stamp discipline (§9.0, MEAS-10) asks each landing to carry its sha, and the
natural move — commit, read the sha, amend it into the message — produces a
message naming a commit that **no longer exists**. **The amend rewrites the
object the sha was computed over**, so the citation is not merely stale, it
points at nothing.

> **Each rung's sha lands in the FOLLOWING commit.**

**Which is a property of the artifact, not a preference about workflow**: a
self-referential identifier is impossible for the same reason a checksum cannot
cover itself, and every scheme that tries produces a citation with **no
referent** rather than a wrong one. The practical form for this repository:
**a landing cites its predecessors; the ledger entry that follows cites the
landing.** Same discipline, one commit of latency, and every sha in the tree
resolves.



The window is **enqueue → release**, not build-start → build-end, and the
forbidden act is **any** change, not just a history rewrite. This is
§5.4a's shape once more and in its most ordinary clothing: **the number
reads clean and is about the wrong state**, and here the wrong state was
produced by the most routine thing a lane does between tickets.

**AND NEVER `git stash` MID-MERGE — it silently destroys `MERGE_HEAD`.**
Measured on the Core-payload merge itself. A `stash` / `stash pop` inside
an active merge leaves the **content correct and the SECOND PARENT gone**:
the resulting commit is an ordinary one wearing a merge's tree. The lane
caught it only because its commit **fell through as a no-op**; had it
landed, **master would not have been an ancestor**, the push would have
been rejected, and **nothing in the tree would explain why** — the files
would all be right.

> **Never stash mid-merge. Take comparisons from
> `git show <ref>:<path>`, which touches no state.**

**AND THE COORDINATING ROLE'S OWN MERGE MACHINERY IS IN THE GATE-AUDIT SCOPE —
RULED HERE, after two leaks that reached master** (`docs/backlog/sv.md`, then
`docs/backlog/qol.md`, the second sitting on master for hours). The merge
fallback's **`git add -A` staged CONFLICTED files as resolved**, committing
`<<<<<<<` markers into the tree.

> **A COORDINATOR'S MERGE RECIPE IS A TOOL. It gets the same gate audit as a
> lane's instrument, and its output reaches master with fewer readers in the
> way.**

**The second leak is the finding, not the first.** It was caught **only because a
marker scan had been added after the first** — *the recipe's own instance of the
rule this register already carries*: **the clause the gate lacks is exactly the
incident it will not catch.** *A fix that closes the case it was written for and
adds no detector has bought one incident, not a class.*

**Standing, and it applies to every merge this role performs:** run the
**all-docs marker scan after each merge**, not only after a merge that reported a
conflict. **The whole defect is that the resolution SUCCEEDED loudly** — `git
add -A` returns zero, the commit lands, and the only witness is text in a file
nobody re-opens.

*And the scope ruling matters beyond this recipe.* **The coordinating role's
tooling had been implicitly exempt from the audits it dispatches**, on the
unstated ground that it is not a tier's instrument. It writes to master; that is
the only property the audit scope should have ever turned on.

**AND THE SCAN CAUGHT A THIRD LEAK ON THE RULING'S OWN LANDING** — `qol.md`
again, **live on master**, from `17d1f7b`. *Two entries' worth of content sat
inside `<<<<<<<` / `=======` / `>>>>>>>` while every gate in the tree stayed
green*, because **no gate reads prose for markers.** **The owning lane resolved
it upstream while this landing was in flight** — both resolutions kept both sides
in order and dropped nothing, and **the duplicate work is itself the argument**:
two roles found the same corruption by scanning, and neither could have been told
by a gate.

**Three instances is no longer a recipe defect; it is a MISSING GATE**, and the
distinction decides who fixes it: a recipe defect is fixed by the role that owns
the recipe, **a missing gate is owed by the tools lane and covers every future
merger.** *The scan proving itself on the day it was ruled is the argument for
promoting it out of a coordinator's habit and into `docs_check`.*

**And verify before declaring a merge ready: `git log -1 --format=%p` must
show TWO parents.** That is the check the failure mode demands, because
every other signal — the diff, the build, the gates — looks correct. It is
§5.4a's shape in git metadata: **the artifact reads clean while the thing
that makes it a merge is missing**, and only a check aimed at the metadata
can see it.

**The order is `stage → build → rebase`, or `rebase → build`.** Never both
at once, and note that this is a *same-clone* hazard: it is not prevented
by the §7.1 build lock, because the lock serializes builds against each
other and a rebase is not a build.

> **"A red from a torn tree is not evidence of anything."**

**AND THE TREE MUST NOT MOVE WHILE YOU QUEUE — enforced, not asked.** A queued
tenure reads the source at **build** time, not at enqueue time, so an edit made
while waiting silently changes what the verdict is *about*. Measured
2026-08-23: the Lean tier nearly reported **"instN green"** for a run that
would have built **instN + weak'**, because the queue wait outlasted the tree.
`tools/triad.sh` now stamps the **working tree**'s hash plus `HEAD`
**into the ticket** at enqueue, re-takes it at acquire, and on a difference
prints `TREE CHANGED SINCE ENQUEUE (<enq> → <now>)` and **refuses**.
`--build-current-tree` proceeds for a lane that batched deliberately — and
prints the **same line**, because the run is about a different tree either way.
A6's prose is the rule; this is the gate, and **fixes live in gates.**

(§5.4a's provenance law, third instance — and the only one where the
misleading number reads *dirtier* than the truth rather than cleaner.)

It **discharges nothing** — an owed build stays owed, and the debt survives
until a clean run. And it **convicts nothing** — it is not grounds to call
master broken. Both directions matter: the same non-evidence must not be
laundered into a green either, on the theory that the red was spurious.
Re-run clean; that is the only thing that settles it.

---

#### VENDORED FIXTURES — where they live, and what they must carry

Every language lane wants a source file beside its model: a `.go`, a `.c`, a
`.js` the Lean model is *about*. **They live BESIDE the model** —
`Examples/<lang>/<case>/<file>.<ext>` next to that case's `guards.lean` — and
that is now safe to do, which it was not.

**The measured history, because it is the reason the rule can be stated at
all.** The Go lane vendored `bitlen.go` beside its model and the tenure went
from **91 seconds to 37 minutes**: a non-Lean file under `Examples/` widened
the build target to the whole `Examples` library. They worked around it by
deleting the sibling and quoting the source into the docstring. With the
classifier's reachability rule the same tenure is **129 seconds**, and the
workaround is no longer needed.

Two rules make it hold:

* **A PROSE MENTION IS NOT A REFERENCE.** A fixture named only in a docstring
  or a comment is invisible to `lake` and classifies `docs`; one reached from
  **code** (`include_str`, `load_c_program … from`, an `[[input_dir]]` member)
  is a build input and widens the scope, correctly. This matters precisely
  because an attribution header is what makes a lane name the file in prose —
  the convention below would otherwise fight the classifier.
* **THE FIXTURE CARRIES ITS ATTRIBUTION AND LICENCE**, in the file, at the
  top. The precedent is the Go lane's: `nat.go` from `crypto/internal/fips140`
  reproduced with **BSD-3-Clause, "Copyright 2009 The Go Authors"**, per
  `docs/go-charter.md` §1.4's ruling that in-tree copies are taken under the
  repository's single instrument. This is §8 step 0's *licence and provenance
  are registry fields, not a detail discovered later*, applied to a single
  file instead of a corpus.

And the instruments **skip** these fixtures rather than reading them as code:
`tools/sites.sh` scans `*.lean` only, and `tools/dupes.sh` scans `harness/`
and `tools/` only — `Examples/` holds 62 `.py` fixtures that are corpus, not
implementation. Both filters are now explicit and self-tested, because a tool
that read a Go constructor as one of ours would produce exactly the confident
wrong number it exists to prevent.

#### THE LANE TOOLS — one line each, and the law each one implements

Every tool below runs **no Lean** unless its own line says otherwise, so it is
safe outside a tenure (A11), and every one has a `--self-test` that executes
its refusal paths rather than describing them (§5.4).

| tool | what it is for | the law it implements |
| --- | --- | --- |
| `tools/triad.sh` | the build protocol AS CODE — lock, ticket, tenure, gates | §7.1, §7.1a (base 1-6, A4-A16) |
| `tools/triad.sh --classify` | size the triad to the diff and STATE what the green covers | §5.4a, §7.1 rule 4 |
| `tools/diagnose.sh` | annotate a build log with cause, fix and the law's home | §7's *"the summary LOCATES; the full log COUNTS"* |
| `tools/check.sh` | one file, against a warm clone's oleans — and it names the case | §7.1 rule 3 and its warm-clone amendment |
| `tools/check.sh --iterate` | the proof-iteration loop, lock-free on measured conditions | A17 (draft) |
| `tools/check.sh` (verdict) | after any run: `TRUSTWORTHY` vs `NOT A MEASUREMENT: <why>` | *a counter that counts goals reaching a fallback reads an error as a success* |
| `tools/sites.sh` | price a constructor change by the sites that DESTRUCTURE it | §5.4a's pattern-position law |
| `tools/analogues.sh` | how many proved analogues a statement shape has, and how long | the Lean tier's tractability estimate |
| `tools/new-proof.sh` | scaffolds for the four recurring proof shapes, laws inline | `docs/statement-cookbook.md` |
| `tools/backlog-index.sh` | generate `docs/backlog/INDEX.md`; `--check` gates its staleness | §9.5, §5.5 |
| `tools/laws.sh` | which laws have a gate, and which are only prose | §9.7's audit cadence; *fixes live in gates* |
| `tools/substrate.sh` | the substrate contract per tier, by SHAPE | §3.4 (STMT-19..22), §8.5 (STMT-67) |
| `tools/dupes.sh` | duplication, counted rather than remembered | §2.4 (MEAS-28) |
| `tools/editions.sh` | thin siblings, and no edition-parameterised definition | §2.4 (STMT-59, STMT-60) |
| `tools/backlog-index.sh --ensure-driver` | configure the generated index's merge driver, once per clone | §9.5; *fixes live in gates* |
| `tools/docs_check.py` | doc-embedded blocks match the tree | the marker convention |
| `tools/ci.sh` | the gate set, run as one — **and the one tool here that CAN start Lean** | A11 (host-gated `lake`), §5.4 (refuses unknown arguments) |
| `tools/laws.sh --gate-set` | ENUMERATE what each gate is pointed at; `UNRESOLVED`, never guessed | §5.4b |
| `tools/lakeinfo.sh` | the lakefile's globs, read ONCE and sourced by both protocol tools | §5.4a (*the lakefile decides it*), MEAS-28 |
| `tools/argv.sh` | ONE value-taking-flag guard, sourced by all eleven tools — refuses, never defaults | §5.4b (discovery, not a list), MEAS-28 |

**THE PREAMBLE'S BLANKET CLAIM NOW HAS ONE STATED EXCEPTION, WHICH IS THE
POINT OF STATING IT.** *"Every tool below runs no Lean unless its own line says
otherwise"* was true while `ci.sh` was absent from the table — and absence is
not an exemption, it is a **hole**. `ci.sh` runs `lake` on a GitHub runner and
**refuses to locally**, which is a fact a lane must be able to read here rather
than discover from a load average. Its `--self-test` also does not exist by
design: the flag **refuses**, and the tool's guards are exercised through
`--verify-guards` under a sentinel that stubs `lake`. **A tool whose exception
is written down is a documented exception; a tool left out of the table is an
undocumented one**, and the second reads exactly like coverage (§5.4b).

**AND A RUN IS NOT A MEASUREMENT UNTIL IT HAS BEEN READ.** The successor
lane's instrumented proof run counted **"0 open arms" twice** while it was
(a) looping in `simp` until the heartbeat timeout and (b) erroring inside a
`first` chain — `split` fails **hard**, escapes the chain, and never reaches
the fallback the counter counts.

> **A counter that counts goals reaching a fallback reads an ERROR as a
> SUCCESS.**

It is `#print axioms` on a failed statement wearing different clothes: **a
success signal that survives the failure it should report.** So `tools/check.sh`
now closes every run with the exit code, the warning classes (naming any that
is not `declaration uses 'sorry'`), the two runaway modes called out by name
whether or not they fired, and a **one-line verdict** — `TRUSTWORTHY: exit 0,
sorry-only warnings`, or `NOT A MEASUREMENT:` followed by every reason. Axiom
lines are reported **only** from a run that was a measurement.

**`tools/sites.sh` is the one to reach for before pricing any substrate
change**, because three lanes priced one constructor change three different
wrong ways in a week. Measured on this tree for `unsupported`: **21 types
declare a constructor by that name**, and the tool excludes **1250** hits —
1207 by position, 43 by prefix — to report **9 destructure + 15 construct**.
A bare name grep would have returned roughly 1274.


## 8 THE FOUNDING CHECKLIST

The order below is the C lane's measured order, which worked: M1 landed in
seven inches over roughly two sessions, endgame-neutral by construction. A
founding lane produces these in this sequence, and **no step's claim is
real until an instrument re-derives it.**

0. **The registry row** (§1.2) — tag, edition tokens, authority, oracle,
   corpus, and **state (founding vs consolidation)**. Proposed until step 1
   ratifies it.

   **The corpus entry carries its LICENSE and PROVENANCE, at this step and
   not later.** Twice now the answer changed the corpus: the C tier's
   219 `.otag` files split c-testsuite into an ISC half and an LGPL half,
   and the SV corpus turned out to be unlicensed, privately provenanced,
   and to **vendor the very standard it tests against** (§1.2). A corpus
   that fails either test is disqualified before a line is written, and
   "we can sort the licensing out later" is how a repository acquires
   something it cannot ship.
1. **The construct CENSUS and its instrument**, on a real corpus, to the
   §5.4 contract. **The scope corpus is a SUITE** (§5.6) — a driver program
   discovers only its own vocabulary. A tier may also name **one exemplar**
   for its proof library, and names it **by stating the theorem**; if it
   cannot state one, it does not need an exemplar yet.
2. **The AUTHORITY declaration** — the spec document and edition, or the
   reference implementation and release line; where both exist, the §4.2
   precedence statement; and for a spec tier, the §4.3 mapping table.
3. **The PROFILE** — the implementation-defined facts the corpus depends
   on, as a schema every host must satisfy, with a stop-condition if two
   hosts disagree. Not a pinned machine: the C lane's question dissolved
   when it stopped anointing one.
4. **The ENVELOPE schema** — `language_version` first-class (§1.5), the
   node vocabulary DERIVED from step 1's census rather than chosen, and a
   check that the two cannot drift.
5. **The extractor** — one per language (§1.6), all three refusal paths
   RUN.
6. **`LeanModels/<Lang>/`** — the AST, the ingester, and structural
   `#guard`s the census independently knows. No semantics.
7. **DECIDE FUEL'S FATE — before writing the interpreter, not after.**
   The fuel-free fragment gets the shared `mvcgen` for ~120 lines of
   `@[spec]`; the fuel-recursive points get the tier's own threshold
   assembly and mvcgen makes no progress there (§3.4). The two routes
   differ in the interpreter's TYPE, so this is not a proof-layer choice
   that can be deferred — and a tier that also wants kernel-reducible runs
   (`#guard` at a fixed fuel) has already chosen fuel.
8. **`LeanModels/<Lang>/<Ver>/`** — the semantics, and the manifest
   (§5.5) starting the same day.
9. **SEPARATE THE SPEC HALF FROM THE INTERPRETER HALF — from theorem one.**

   > **An estate that separates them is cheap to re-found; one that
   > interleaves them is not.**

   Classify every theorem by whether its **STATEMENT mentions the
   interpreter**. Measured across the whole sunfish estate: **949 theorems
   = 615 mathematics (65%) + 334 interpreter-facing (35%)**. Under a
   definition swap the mathematics **recompiles unchanged** — the 35% is
   the entire re-founding scope, and **four files re-found to nothing at
   all**.

   **AND THE METRIC MUST NOT BECOME A TARGET — a corollary the Go lane
   stated by watching its own number FALL.** Go's split moved **63% →
   58.6%**, and **that is CORRECT.** Fuel theorems do not transport, so:

   > **A rung that adds fuel-bearing constructs moves the split DOWN.
   > Holding it flat would mean fuel facts were written into spec-shaped
   > statements.**

   That is this step's own trap, and it is Goodhart's law with a specific
   mechanism: the ratio is a **diagnostic of where statements live**, not a
   score to maximise. A lane optimising for a flat 65% would achieve it by
   **smuggling interpreter facts into mathematical statements** — producing
   exactly the interleaving the step forbids, while the metric applauded.
   **Read a falling split as evidence the discipline is holding under a
   rung that genuinely added interpreter surface.**

   **The decisive part is that the split was not made for this.** The
   calmness lane separated its spec half from its interpreter half **for
   proof-engineering reasons, long before any rebuild existed** — and that
   choice is now worth **two thirds of the migration cost**. This is the
   family's own doctrine arriving from the other direction: §0.1
   principle II draws the trust boundary between definition and library,
   and this is the same boundary drawn through **theorem statements**, with
   a price tag attached.

   Concretely: a theorem that can be stated about the mathematics should
   be, and the interpreter-facing statement should be the thin layer that
   connects it.

   **MEASURED AT A SUBSTRATE CHANGE — the law paying off with a zero.**
   ES's `es_never_undefined` and `es_never_orderDependent` transferred
   across the Core payload landing with **ZERO edits**, because they are
   stated about **the tier's own cause constructor** and not about `Halt`.
   The substrate moved underneath them and the statements did not mention
   it. **A theorem survives a change to the thing it does not name** —
   which is the same discipline as step 9's spec/interpreter split, applied
   to the choice of *what a statement is about* rather than to which half
   of the estate it lives in. A tier writes this discipline in on day one because it
   costs nothing then and cannot be retrofitted cheaply — the 35% is not
   work you can decide to have done differently after the fact.
10. **A GREEN BUILD IS NOT A TERMINATION ARGUMENT.**

    > **When recursion goes through a RECONSTRUCTED node or an OPAQUE
    > callee, state the measure — `termination_by` on the whole mutual
    > block. Take the PARTS; never rebuild the node.**

    Measured, and the way it surfaced is the point. The C tier's inch 5
    killed termination inference by passing `evalExpr ctx` as a **closure
    through an opaque `ctx.call`** — and that **exposed a latent defect
    inch 3 had already built green on**: `evalExpr`'s aggregate cases
    **reconstruct** the node (`evalLValue ctx (.member base field arrow ty
    sp)`), which is **not a syntactic subterm**. The earlier green rode on
    slack elsewhere.

    So the defect was **two inches old and passing** before anything made
    it visible, which is why this is a **§5.4a** instance and not merely a
    Lean tip: **the green was never evidence of termination — it was
    evidence that inference had found some other route.** A rebuilt node
    looks like the node you matched, and the elaborator's willingness to
    accept it today is not a property of your definition.

    The discipline is cheap and it is a *statement*, not a tactic: destructure
    to the parts and pass the parts, and where the recursion genuinely
    leaves the syntax — an opaque callee, a closure — **say the measure out
    loud** so the argument lives in the file rather than in the
    elaborator's mood.

    **AND ITS SHARPER SIBLING — a definition that COMPILED and was
    UNSOUND.** The Lean tier's first definition required the structure's
    sort to be **`IsAlwaysZero`**. That is unsound: `instL` turns `Type u`
    into `Prop` at `u := 0`, so a **projected data field yields `False`** —
    the arena's proj-of-imax-prop family, which **the official kernel
    itself failed at v4.28.0**. The kernel's own test is **`!isNeverZero`**
    — *maybe* zero, not *always*.

    **What caught it was the validation lemma.** `TrProjP.instL` was
    **unprovable** against the wrong definition, and that is the entire
    detection mechanism:

    > **A definition that merely compiled would have shipped the
    > unsoundness. The proof is what refused it.**

    This is §0.1's trust boundary as a *work order*: **write the validation
    lemma before declaring a definition done.** A definition is a claim,
    and compiling is not how a claim is checked — the same relation step 10
    draws between a green build and a termination argument, one level more
    dangerous because the artifact was not merely unproven but wrong.

    **The polarity rule that falls out, worth carrying wherever universe
    levels are modelled:**

    * **`MaybeZero` REFLECTS along instantiation** — it *discharges
      hypotheses*;
    * **`IsAlwaysZero` TRANSPORTS forward** — it *supplies conclusions*;
    * **`ProjSound` goes ∀ → ∃.**

    Getting the polarity backwards is exactly how a hypothesis-shaped
    condition ends up asserted as a conclusion, which is what happened.

    **AND ITS PAIR, from the same lane and the same definition — the SECOND
    defect the obligations caught in the lane's OWN definition rather than in
    the tree it targets** (`29f868e`, on master; censused by **reading**,
    before a tenure was spent on it). `TrProj.wf` concludes `VExpr.WF env U Γ
    e'`, which unfolds to *"`e` has a type"* — so it needs the projected field
    typed **unconditionally**. `ProjSound` typed it **only inside the Prop
    case**:

    > **When the structure's sort is not maybe-Prop, the definition said
    > nothing whatever about `v`.**

    So `wf` is **unprovable against it** — not hard, unprovable. The fix hoists
    the field's typing **out of the implication**, leaving the Prop-squash as a
    condition on the **levels alone**: **strictly stronger** (the field is typed
    in every case, which is what `wf` consumes), **identical soundness
    content**, and **transports unchanged** — `MaybeZero u → IsAlwaysZero w`
    under `instL` becomes the same implication on instantiated levels,
    discharged by proofs already written.

    > **A DEFINITION WHOSE GUARANTEE LIVES INSIDE AN IMPLICATION GUARANTEES
    > NOTHING WHEN THE ANTECEDENT FAILS. Check what the definition says when
    > its INTERESTING case does NOT apply.**

    **The two defects are the same shape seen twice** — polarity backwards, and
    a guarantee trapped under a hypothesis — and both share the property that
    makes this section worth reading: **neither was found by the compiler.**
    One was found by a **proof**, one by a **census**, and both definitions
    elaborated perfectly the entire time. **A definition cannot be type-checked
    into meaning what you intended**; the only instruments that reach it are the
    obligation that consumes it and the reading that asks what it says in the
    boring case.

    > **RIDER — THE HONEST SIGNATURE.** Upstream's redundant hypothesis was
    > **OMITTED rather than accepted-and-ignored** (*"`ProjSound` already
    > carries it"*). A parameter a definition does not use is a **false
    > advertisement of what it depends on**, and it costs every consumer a
    > premise to discharge for nothing. **Take what you use; if a hypothesis is
    > redundant, say where its content already lives.**

    **A CONGRUENCE WALKER'S COMPLEXITY IS SET BY ITS DISPATCH, and budget
    cannot fix it.** The `mono_with` technique — a walker with a
    **backtracking `first`** at each node — is **LINEAR on bind spines**
    and **EXPONENTIAL on `ite` chains**. Measured: **~22 nested `ite`s
    timed out at 200 000 heartbeats.**

    > **Raising heartbeats trades a WRONG answer for a SLOW one.**

    **CORRECTED — the real cause was TRANSPARENCY, not dispatch shape.**
    The first diagnosis (recorded here as *"a search where a case analysis
    was available"*) was the plausible one and not the measured one. Two
    causes, both found by looking rather than by reasoning:

    * **`apply` at DEFAULT TRANSPARENCY whnf-unfolded tier constants** to
      hunt for an `ite` underneath — descending *through* `applyBuiltin`.
      **The actual timeout was the whnf reconciliation of two 200-line
      bodies.**
    * **recursive backtracking re-planned a whole subtree per leaf
      failure.**

    The three fixes are each aimed at one of those, and none is a budget:

    * **`repeat'`** — one step per goal, kept, so **a leaf failure is an
      open leaf and never a parent re-plan**. That is what makes it
      **linear**;
    * **the leaf closer runs FIRST, guarded by `done`** — which stops the
      transparency descent into named lemmas' definitions before it
      starts;
    * **the early `refl` under `with_reducible`** — it succeeds on
      syntactic equality and, crucially, **FAILS FAST** instead of
      attempting the 200-line whnf.

    **The transferable form**: when a tactic is exponential, ask what it is
    *unfolding*, not only what it is *trying*. A backtracking search is
    visible in the tactic text; a transparency setting is not, and it was
    the expensive half here.

    **AND `<f>.mutual_induct` EXISTS** — it concludes the **whole mutual
    conjunction at once**, which is the right shape for a mutual block.
    One trap: **the conjunct order is NOT source order**, so match on what
    the goal actually presents rather than on the order the definitions
    were written in.

    **AND A SHAPE THAT DEFEATS EQUATION THEOREMS ENTIRELY.** A ~210-line
    `if fname == … else if …` chain produces **"failed to generate
    equational theorem"** — so **`unfold` is the only door**; `simp only`
    and `rw` **cannot open it**, because both need the equations that were
    never generated. Worth knowing before designing a dispatcher that
    shape: the definition still *works*, but it becomes unreachable by the
    tactics that rewrite with it.

    **AMENDED AT THE LANDING — the exponent was real, the diagnosis was
    half right, and the fix is smaller than the prediction.** The walker
    now closes **every** arm of `Monadic.fuelMono` (61 arms across two
    mutual blocks, plus a 19-deep `ite` chain) at the **default 200 000
    heartbeats**, and no goal-head dispatcher was written. Two mechanisms
    were doing the damage and only one had been named:

    1. **The backtracking `first` re-plans a SUBTREE per leaf failure** —
       the named cause, and the cure is `repeat'`, which takes **one step
       per goal and KEEPS it**. A failure at a leaf must be an *open leaf*,
       never a parent that reconsiders. That alone makes the descent linear
       and it needs no dispatch table.
    2. **`apply` unifies at DEFAULT transparency** — the cause that had not
       been named, and the more expensive one. `apply PyLe.ite` will
       happily **whnf-unfold a tier constant** to find an `ite` underneath
       it, so the walker descends *through* `applyBuiltin` instead of
       stopping at `applyBuiltin_mono`, and a reflexivity probe on two
       200-line bodies differing only in one variable tries to reconcile
       them by unfolding. THAT is what "timed out at whnf" was.

    The two cures are one line each: **run the leaf closer FIRST, guarded
    by `done`** (so a named lemma is reached before `apply` can unfold past
    it), and **make the reflexivity probe `with_reducible`** (so it
    succeeds on syntactically equal subtrees and fails *fast* otherwise).

    > **"Syntax-directed" is bought with TRANSPARENCY CONTROL and a
    > non-backtracking driver, not with a dispatcher.** Before writing one,
    > check whether the walker is descending through definitions it should
    > be stopping at — a tactic that unfolds is a tactic that has left the
    > syntax.

    And the equation-theorem row stands with its number corrected: the
    chain is **19 `if fname == …` arms** (a tool reported 45 by counting
    the nested `match vs with` arms as top-level ones — the shape was
    settled by READING the source, and a tool's arm count is a candidate,
    not a finding).

    **AND A TACTIC-MACRO TECHNIQUE that turns a per-arm hand proof into one
    line — measured on `heapEqFuelMono`, 14 arms, axioms `[propext]`.**
    Tactic macros are **hygienic**, so **a top-level tactic cannot see
    induction hypotheses bound inside a proof**, and **`assumption` cannot
    instantiate a ∀-quantified IH.** The fix is to stop expecting the macro
    to find them: **pass the IH names in as `ident` arguments.** That is
    what collapses fourteen hand-written arms into
    `split <;> auto ihE ihL`. Hygiene is not an obstacle here — it is the
    reason the macro needs to be *told* what a human reader would have
    inferred from the goal.
11. **CONSUMING A GENERATED OR EXTRACTED MODEL: its relations are ITS OWN
    CONSTANTS.**

    > **Check the definition before importing a library's lemmas about a
    > same-named relation.**

    Measured on the Wasm tier. Its spec-extracted model defines its own
    **`Forall₂`** as **zip-based** —
    `∀ t ∈ xs₁.zip xs₂, P t.1 t.2` — while **Mathlib's `List.Forall₂` is
    INDUCTIVE and a different constant.** The two are not
    interchangeable in the way that matters: **zip truncates, so the
    zip-based relation does not imply equal lengths.** The Mathlib
    `forall₂_*` route cannot be pointed at the model **POINTWISE**, and
    importing it that way costs a red rather than a shortcut.

    **HALF-REHABILITATED BY A DEEPER SEARCH, and the correction is worth
    more than the finding was** (Wasm; **queued — conditional on that
    landing**). This text first said the route *"cannot apply at all"*.
    **Mathlib ships the crossing itself: `List.forall₂_iff_zip`** — and
    its side condition is **a length equality**, which is *exactly* what
    `Resulttype_sub`'s constructor already carries.

    > **The length-blindness that made the API inapplicable is the same
    > fact that supplies the bridge's premise.**

    So the API does not apply **pointwise**; it applies **through a
    one-time bridge**, and **paying it once restores the whole library
    downstream.**

    > **A generated model's relation being NONSTANDARD does not ORPHAN it
    > from the library. Look for the IFF that CROSSES — its premise is
    > often already carried by the generator's extra fields, so the same
    > quirk that blocks direct reuse can FUND the crossing.**

    **Note what changed and what did not.** The measurement was right:
    those constants are different, and the pointwise route is red. **What
    was wrong was the quantifier on the conclusion** — *"does not apply"*
    where the evidence supported *"does not apply directly"*. A negative
    about a library is a claim about a **search**, and §9.7's rule for
    negatives applies to it exactly: *an obstruction that is only
    encountered is not measured* — **try the nearest alternative
    formulation** before recording the door as shut.

    **And the practical order this gives a lane**: when a generated
    relation blocks a library, do not price a hand-rolled replacement
    first. **Price the BRIDGE first** — one `iff`, whose premise you may
    already be holding — because a bridge is bought once and a
    replacement is maintained forever.

    **THE BRIDGE HAS NOW BEEN PAID, and the price confirms the ordering**
    (Wasm O3, `fd96fce`, on master). `rt_bridge` pays it **once**, and
    `rt_sub_app` **collapsed to `exact List.rel_append h1 h2`** — a
    hand-rolled replacement would have been maintained forever to reach
    the same line.

    **AND THE SHAPE OF THE CORRECTION IS ITSELF A LAW, because the
    compiler REFINED the claim rather than refuting it.**

    > **"Does not apply at all" is a claim about a LIBRARY, and only
    > WRITING THE BRIDGE measures how much weaker the true statement is.**

    The original finding was **right about the lemmas and wrong about the
    library**, and those are different claims with different evidence:
    *these lemmas do not fire* is settled by a red, while *this library
    cannot reach this model* is settled only by **attempting the
    crossing**. §9.7's rule for negatives — *an obstruction that is only
    encountered is not measured* — is what separates them.

    **So the correction is recorded as a REFINEMENT, with both halves,
    not as an erratum.** An erratum deletes the finding and takes its
    correct half with it; a refinement keeps *the lemmas do not apply
    pointwise* — which is still true, still useful, and still the reason
    the bridge is needed — and adds the quantifier the evidence actually
    supported.

    **AND THE LANE'S PRIOR-ENTRY HYGIENE IS THE SAME DISCIPLINE POINTED
    BACKWARD**: it flagged its own overstatement **unprompted** and
    **preserved the finding's correct half**. Compare the Lean tier's
    form — *"entries 17 and 19 predate the finding and should be read
    with the qualifier attached, rather than rewriting them."*

    > **A qualifier may attach to a RANGE of dated entries. Rewriting
    > them would destroy the record of what was known when.**

    That is the annotation norm (§5.4b) at a second scale: one entry takes
    an annotation, a *range* takes a **standing qualifier** — and both
    beat the edit that would make the ledger read as though the lane had
    never been wrong.

    **THE GENERATOR'S EXTRA PREMISES ARE THE TELL, and reading them is the
    cheap check.** The generator emits `Resulttype_sub` with a **separate
    explicit length premise** — which is precisely the fact that the
    relation does *not* carry length equality, written down by the
    generator itself:

    > **A generated model's extra premises tell you what its relation does
    > NOT carry.**

    So the premise list is not boilerplate to be discharged; it is a
    **specification of the gaps**, and a lane that reads it first learns
    what no library lemma can supply — **and, per the rehabilitation
    above, what the bridge to the library will cost, because those same
    premises are the price of crossing.** The tell reads in both
    directions: **what the relation lacks, and what you already hold.**

    **And what DOES transfer is the FACTORING, not the lemmas.** Aaron
    Lee's Isabelle `list_all2` is inductive, so his closer has **no
    counterpart** here — but his **factoring** (reflexivity, both split
    orientations, transitivity) does. That is the general shape when
    consuming a generated model: **the proof architecture ports; the proofs
    do not.**

---

## 8.5 REGISTERED CAMPAIGN ITEM — THE ADEQUACY MILESTONE

Named here so it is a scheduled artifact rather than a standing caveat.

> **`twinAgrees` — an adequacy theorem relating the deep interpreter to its
> monadic twin over the same AST.**

* **Why it is a milestone and not a caveat.** It is the required artifact
  on **every** route (§3.4 clause b): the bridge's far side and any future
  definition swap both go through it, so it is on the critical path whether
  or not Python ever migrates. Until it exists, the monadic form is a
  second semantics with no theorem tying it to the trusted one, and §0.1
  principle I forbids treating it as the definition.
* **What does NOT discharge it.** The differential corpus. **1 394 cases**
  validate the *deep* interpreter against CPython; they say nothing about
  the twin, and the twin's fidelity gap is already known and stated (name
  resolution consults the static globals fold first; the twin's does not).
  An executable twin joining `diff_test` would buy evidence, not a theorem
  — and would cost a second maintained interpreter under the
  model-matches-code law.
* **GATED ON `bound_refines_fuelModel` closing.** That is the campaign's
  own assembly point — `RecursionStep` first, then
  `bound_refines_fuelModel` — and it is the moment the flagship estate
  stops absorbing re-proof cost from an interpreter change. Starting
  adequacy earlier competes with the campaign for the same files.
* **What it unlocks, priced.** The **5 343-line** substrate saving (§3.4)
  becomes collectable, and §3.4 clause (c)'s erosion begins: new work
  monadic, old theorems transported on demand, the deep interpreter
  retiring gradually or never.
* **RE-SCOPED — on corrected counts, adequacy is LIKELY NEVER NEEDED for
  this migration.** Transporting a file's theorems across the bridge beats
  proving adequacy for that file above a crossover of roughly **100
  theorems**, and on the corrected classification (step 9 above) **no file
  clears it.** So the expected path is theorem-by-theorem transport, and
  `twinAgrees` is a **contingency** rather than a gate on the critical
  path.

  **The general law is untouched, and the distinction matters.** *Any route
  that introduces a second semantics owes an adequacy theorem* — §3.4
  clause (b) — remains family law. What the counts changed is the
  probability that **this particular migration takes that route at all**:
  transport is cheaper per file than adequacy, so the second semantics
  never has to become the definition. A future migration that *does* swap
  a definition wholesale owes `twinAgrees` exactly as before.

  **What still decides it**: the spike, which fixes the **deep-statement
  ceiling** — the point past which a single statement is too entangled with
  the interpreter to transport. Until that number exists, "likely never"
  is a measured expectation and not a closure, and this item stays
  registered rather than retired.

---

## 9 THE STANDING STRATEGY — what every lane does next

Thomas's standing directive: **audit the learnings regularly, define the
updated strategy, share it with the agents.** This section is that
strategy. It is sourced entirely from `docs/duplication-audit.md` and is
the thing the coordinator broadcasts; when the next audit lands, this
section is what it revises.

**The one-line diagnosis behind all six items:** *the contract lives in
prose, and each lane hand-implements it.* **Prose cannot be run**, so a
lane's implementation is only as good as its reading, and a defect in one
reading is invisible to every other lane. Every item below moves a rule
from prose into something executable.

### 9.0-pre REPORT-THEN-CONTINUE — the lane cadence, ruled 2026-08-24

**Standing change, effective now, for every lane.**

> **AFTER REPORTING A LANDING OR A VERDICT, PROCEED IMMEDIATELY TO YOUR NAMED
> NEXT RUNG. Do not await acknowledgment.**

**Stop only when BLOCKED, and the blocks are three:**

* **(a)** a **RULING** you need and do not have;
* **(b)** a **MERGE YOU CONSUME**;
* **(c)** a **TENURE VERDICT** not yet returned.

**THE RATIONALE IS MEASURED, AND IT CONVICTS THE COORDINATING ROLE.** Thomas
**twice** observed the fleet at near-zero activity, and **both times the cause
was an ack-gated loop** — every lane reporting, then parking, while the queue
drained.

> **The trough was a COORDINATOR ARTIFACT, not a work shortage.**

**Which is this register's own instrument-artifact law arriving at the
coordination layer** (§7.1a's A17 defect): *a day's economics set by a
mechanism nobody was measuring.* There the proxy was monotone and closed a gate;
here the ack was a **serialization point** nobody had priced — **and both were
invisible for the same reason: the cost fell as WAITING, which no artifact
records.**

**And the asymmetry that makes report-then-continue the right default**: a lane
that continues when it should have waited produces **work that may need
redoing**; a lane that waits when it should have continued produces **nothing,
and leaves no trace that it did.** *The first failure is visible and bounded;
the second is invisible and unbounded* — which is why the three blocks are
enumerated rather than left to judgment.

**For this lane specifically**: the architecture lane is **event-driven by
charter**, so it lives in exception (a) by construction — it lands what
dispatches bring. **The standing §9.0 family snapshot is its continuous work**,
and it now carries the fleet line below.

### 9.0 THE GOAL IS COMPLETION — and a milestone is a WAYPOINT

**From Thomas, 2026-08-23. This is the highest authority in this document, and
it reframes every item below it.**

> *"It's not enough to stop at 'we proved one function works.' The goal is to
> COMPLETE the lean-surfaces project for the target languages. That's months of
> work or more — don't call the goal done after a day."*

**WHAT "DONE" MEANS IS PER TIER, AND IT IS MEASURED BY THAT TIER'S OWN
CONFORMANCE SUITE.** Each lane's endgame is **full-spec support**, and the
number that says how far away it is comes from the suite the tier is judged by:

| tier | the suite that measures completion |
| --- | --- |
| **ECMAScript** | **test262** |
| **C** | **gcc.c-torture** |
| **Ada** | **ACATS** |
| **SystemVerilog** | **sv-tests** |
| **WebAssembly** | **the Wasm spec suite** — *see the relational-model boundary case below: this tier scores by OBLIGATIONS, not tests* |
| **Go** | **the stdlib reach instrument** |
| **Python** | **the refusal surface + the flagship theorem** |

> **EVERY LANE LEDGER CARRIES ITS STANDING SPEC-COVERAGE NUMBER, UPDATED PER
> LANDING, STAMPED WITH ITS SHA.**

That is the stamp discipline (MEAS-10) applied to the **one** number that says
how far the tier is from done — and it belongs in the **ledger**, not only in a
charter, for the reason §7.2 already gives: **a ledger is appended per landing,
so the number moves with the work, while a number in a charter is a copy the
code cannot see.**

**AND THE TABLE ABOVE HAS A BOUNDARY CASE, WHICH IS A FACT ABOUT A MODEL'S KIND
RATHER THAN A LANE'S EFFORT** (Wasm's next-corner census, `0f44b74`, merged).
The Wasm tier **cannot build a scoreboard at all**: *every other tier can, because
every other tier's model EXECUTES* — this one's is **a set of inductive `Prop`s**,
and an inductive relation does not run against a test file.

> **A TIER WHOSE MODEL IS RELATIONAL SCORES BY OBLIGATIONS, NOT BY TESTS. The
> asymmetry is STRUCTURAL, not effort.**

**And the escape is a trap the charter already declined**: an executable
interpreter would give the tier a spec suite — and it is **§8.4's declined
endgame wearing a different hat.** *A missing instrument is not automatically a
gap to close; when closing it requires the thing the charter refused, the honest
move is to change the UNIT of the number, not to build the refused thing under a
new name.*

**So the completion doctrine gains a second unit and keeps one meaning.** *Full
spec support* is still the endgame; what differs is **what a denominator can be
made of** — tests where a model runs, **discharged obligations where it
relates.** *Do not read a relational tier's number against an executable tier's
and call the difference progress.*

**AND THE ROADMAP LAW REACHED A ROADMAP ITEM BEFORE IT WAS SCHEDULED** (same
census). The soundness endgame was priced as *"port the Isabelle ladder"* — and
opening it found **Isabelle ITSELF at 10 lemmas / 77 incomplete.**

> **There is no ladder to port; it is ORIGINAL MECHANISATION.**

**This is the frontier law arriving one level up, on a PLAN rather than a
score**: a later roadmap item priced from behind the current one had **never been
observed at all**, and the observation cost one census. *An endgame described by
the artifact it would reuse is a claim about that artifact — and it is checkable
today, for less than it costs to discover at the rung.* **The cheapest audit a
roadmap admits is opening the thing it says it will copy.**

**AND THE NUMBER ITSELF WAS SELF-DEMOTED BY THE LANE THAT PUBLISHED IT — 40/66
CORRECTED TO 33/66 PLUS 8 PARTIAL** (ES, destructuring `a48be18`; instrument
`7ea36e7`, ticketed). *"Every N/66 I have given you came from the scrape."*

> **ACCIDENTALLY CORRECT IS WORSE THAN WRONG. Nothing announces the day the
> accident ends.**

**The mechanism is exact and worth carrying**: the old scrape was right **for
four inches**, because each of those inches happened to implement **every arm it
added** — so the proxy and the truth moved together for reasons that had nothing
to do with the proxy. **And it ended quietly inside the very inch whose number
was being reported.**

**A wrong instrument gets fixed; a LUCKY one gets trusted**, and trust is
accumulated at exactly the rate that makes the eventual divergence expensive.
*This is the expiry law (§5.0a) with the subject changed from an argument to an
instrument* — **a coincidence has an expiry date nothing in the tree tracks
either** — and it explains why *validate in both directions* is not pedantry: **a
proxy agreeing with the truth on every case you have looked at is the observation
a lucky proxy and a correct one both produce.**

**AND A DENOMINATOR CAN BE CHOSEN FOR MOTION LEGIBILITY, WHICH IS A LEGITIMATE
REASON AND NEEDS SAYING** (SV's `slotStep`, merged `365578f`). §9.0's line reads
**"3 of 15 regions driven"** rather than an `N/N` —

> **the number that actually MOVES.**

**A denominator that cannot change for months reports the same digit through
every landing**, so a lane reading its own scoreboard learns nothing from it and
stops looking. *Choosing a sub-denominator whose motion is visible per inch is
not a softer number; it is a number with a derivative.* **The honesty condition
is the one §9.0 already imposes** — say which denominator, and never let the
legible one silently replace the completion one. **Both live in the ledger; the
completion number is the endgame, the moving one is the instrument.**

**AND THE SAME LANE OWNED A COST IT HAD CREATED, WHICH IS THE HARDER HALF OF
PRICING HONESTLY** (SV, same landing). Writing `slotStep` in `SvM` first
**DOUBLED the adequacy obligation** — *"the adequacy lemma now carries both
obligations at once — that's my doing."*

> **A DESIGN CHOICE THAT ENLARGES A LATER PROOF IS A COST THE LANE INCURRED, NOT
> A DIFFICULTY IT DISCOVERED.**

**The two are indistinguishable at the moment the proof gets hard**, and the
default attribution is the flattering one: *the obligation is large* reads as a
fact about the problem. **Recording which half was self-inflicted is what lets a
later lane consider the other ordering** — and it costs nothing but the sentence.

**AND THE REAL BLOCKER WAS FOUND BY LOOKING RATHER THAN BY REASONING**: there is
**no trace-producing driver**, so there is **nothing for `cycleOf` to project.**
*The next rung is the smaller unblocking thing* — **whose prerequisite landed two
inches ago for an unrelated reason**, which is §9.0b's shared-prerequisites-first
rule paying without anyone having planned it.

**And the lane declined to price the proof, with a reason this register should
adopt verbatim:**

> **"I'll price the proof itself once `runSlots` exists and I can see the REAL
> GOAL SHAPE, rather than estimating it from prose."**

**Which is the frontier law's own discipline turned on an estimate instead of a
score.** *A proof estimated from the prose describing its statement is priced
from behind the wall that hides its goal* — and the honest move is not a wider
band but **naming the observation that would make a band possible.** **Refusing
to price is a legitimate output when the prerequisite for pricing is a named,
scheduled artifact.**

**AND A CHARTER CAN BE OVERTAKEN BY ITS OWN SCOREBOARD — flagged rather than
silently re-read** (C, `34ad979`). The charter's *"39-unsupported frontier,
rung-at-a-time"* is now **a 197-item frontier whose top two entries belong to
the SCOREBOARD, not the SEMANTICS.**

> **A frontier description written before the instrument existed is a claim the
> instrument can now refute — and the honest move is to FLAG IT AGAINST THE
> CHARTER, not to re-read the charter charitably.**

**The charitable re-reading is the failure mode, and it is nearly invisible**: a
lane that quietly interprets *"39-unsupported"* as *"the semantic frontier,
whatever the scoreboard says today"* keeps the charter true **by making it say
less every time the number moves.** *A document that survives every measurement
has stopped being checkable.*

**Ruling: the three instrument items land as ONE inch — and then the frontier is
honestly semantic.** *Separating instrument debt from semantic debt is what
makes the remaining number a statement about the language rather than about the
harness.*

**THE STANDING TABLE, SNAPSHOT 2026-08-24** — every number moved on this date,
and it is recorded here as a **dated snapshot**, not as a live figure: **the
lane ledgers are the live copies** (a number in a charter is a copy the code
cannot see), and this exists so the family can be read in one place.

| tier | coverage | declared divergences |
| --- | --- | --- |
| **Python** | flagship **TYPED + merged**; chain **4/9**; **all 3 serving surfaces done (scoped)** | **2** |
| **Go** | **687 / 3 803** | — |
| **ECMAScript** | **38 / 66**, register live | **1** |
| **WebAssembly** | **4 / 5** | — |
| **Ada** | statement tier **RUNNING**; **ACATS 0 / 4 188**, honest | — |
| **SystemVerilog** | **18/21** live envelopes · **11/11** stepper constructors · **0 / N** | **2** |
| **C** | **gcc.c-torture 67 / 300** scored, **failed 0**; five landings (**0 → 24 → 24 → 28 → 67**) | — |
| **analog** | **8 / 24** grounded; first inch merged | — |
| **SoftFloat** | **1 / 12** + declarative spec + `roundQ` | — |
| **Lean tier** | **0 / 27**, `Name` pairs pending | — |

**Read the zeroes with §9.0's own counting rules and they are not all the same
zero.** **ACATS 0/4 188** is *honest* — the suite is wired and the tier has not
scored on it. **c-torture 0** *was* the runner-does-not-exist-yet zero — **and it retired
inside this snapshot's own date**, which is the finding below. **`0/N`** in
SV is *the denominator itself is not yet fixed.* **Three different states
wearing one digit**, which is precisely the conflation §9.0's denominator, sign
and numerator rules exist to keep apart — *and a family table is where they are
most likely to be read as one number.*

**AND A DATED SNAPSHOT AGES WITHIN ITS OWN DATE.** C's row was written at
**0 (no runner)** and, on the same date, passed through **24 → 24 → 28 → 67 of
300** across **five landings** — so *"snapshot 2026-08-24"* named a day during
which the row it stamped changed four times.

> **A snapshot's stamp must be as fine as the fastest thing it stamps. A date is
> not a granularity when a lane lands five times in one.**

**The remedy is not a finer clock — it is the pointer the block already
carries**: *the lane ledgers are the live copies.* **A stale cell in a dated
table is harmless exactly as long as no one quotes it**, and the failure mode is
a reader treating a same-day stamp as *current* rather than as *one reading among
several that day.* **So the stamp is a sha's job, not a date's** — and where a
row is expected to move within the day, **the honest cell is the ARC, not the
endpoint**, which is why C's row now carries all five numbers rather than the
last one.

*A row that shows its path cannot be misread as a live figure.*

**And the `declared-divergences` column is deliberately BESIDE the coverage
number, never inside it** (§5.0a): **5 rows across 3 tiers**, all gated both
ways by the shared checker.

**AND THE SNAPSHOT NOW CARRIES A FLEET LINE, IN THREE NUMBERS** — because the
one-word version was the defect filed above:

> **`N lanes with assigned rungs · M executing · K building`**

**Never "N lanes live".** The three can differ in every pair, and the compressed
form **answers whichever question the reader brought.** *This line is the
coordinating role's own correction, carried in the place the family's numbers
are read.*

**AND IT IS A `###` SECTION, NEVER A `##` ENTRY — a requirement this rule owed
from the start and did not carry** (found 2026-08-24 by the heading guard, three
lanes deep). §9.0 asked every lane for a standing block and **said nothing about
its heading level**, so Ada, Go and the analog tier each independently wrote
`## SPEC COVERAGE — …` — **a standing section wearing an entry's syntax**, which
is precisely the case §9.5's two-remedies ruling calls **demote, never
id-ify**: giving it an id would put it in the index **as an entry that does not
exist.**

> **A standing block in a per-lane ledger is a `###` SECTION. Only landings are
> `##` ENTRIES.**

**The three existing headers are old-valid and are their lanes' to demote** —
one line each, no id, no renumbering. **And the lesson is the one §9.5a already
paid for, arriving through a different door**: this rule was written for readers,
**the generator reads the ledgers too**, and *a rule that specifies a document's
CONTENT while leaving its SYNTAX to taste has left the syntax to be decided
three times.* **Say the level, or three lanes will each pick one.**



**AND THIS IS WHAT THE INSTRUMENTS WERE FOR.** Everything this document has been
minting — suites driving scope (§5.6), coverage as
`stated / (stated + refused + out-of-tier)` (§5.5), the four refusal causes and
their separate retirement schedules (§5.2), reach censuses (§9.0b) — exists to
make that number **honest and re-derivable**. A completion goal without an
instrument is a wish; the instruments were built first, and this is the target
they were built for.

**AND GO'S TABLE IS THE TEMPLATE — the first lane to land the standing number,
and the shape the other tiers' ledger heads should copy** (`fef0b79`, on
master). Three properties, and each one exists because the naive version of the
table would mislead:

* **TWO DENOMINATORS, with the choice's cost stated.** The number moves **3.5
  points** depending on which denominator is chosen, so both are published and
  the gap is named. **A single coverage figure hides a modelling decision**;
  publishing the spread makes the decision visible instead of settling it by
  whichever number reads better.
* **THE SYNTACTIC-UPPER-BOUND GUARD.** The table measures **syntactic**
  coverage, which is **an upper bound** — and it carries the rule that keeps the
  bound honest:

  > **A syntactic-only win must NEVER be banked there.** Recognising `fmt.Println`
  > as a package call **is not running it.**

* **THE CEILING IS THE CURRENT VOCABULARY.** The number is read against what
  the tier can step **today**, which is the retracted `+0` law's lesson
  (§9.0b) applied to a coverage figure rather than to a rung: **a coverage
  number is a delta against a vocabulary, and it moves when the vocabulary
  does.**

**The other tiers' ledger heads cite this table's shape**, not its numbers: two
denominators or a stated reason there is one, the upper-bound guard wherever the
measure is syntactic, and the vocabulary the ceiling is taken at.

**AND THE TARGET ITSELF MUST BE TYPED, WHICH IS RUNG 1 OF ANY CHAIN** (R-track,
`docs/sunfish-flagship-chain.md`). The flagship existed **only in prose**.

> **A GOAL THEOREM NOBODY HAS TYPED IS ONE NOBODY CAN TYPECHECK AGAINST.**

> **A chain document's FIRST RUNG IS THE STATEMENT, and a WAITING lane cannot
> cite an UNSTATED theorem as its target.**

**AND RUNG 1 HAS NOW BEEN PAID, WHICH SUPPLIES THE LAW'S ECONOMICS** (R-track,
chain doc merged `68327fb`; `flagship.lean` ticketed). The campaign's namesake
theorem cost **ONE scratch elaboration.**

> **The rung listed FIRST, blocking the most WAITING triggers, was the CHEAPEST
> item on the board — and it had never been anyone's task**, because every
> archived ladder ends *"…and then `bound_refines_fuelModel` assembles."*

> **A goal theorem that only ever appears as the LAST LINE OF PLANS will never
> be written. Type the target before the path to it.**

**Three properties, and the third is why this outranks a scheduling
observation.** The statement is **usually cheap** — it is a type, not a proof.
It makes **every progress claim falsifiable**, because a claim of progress
toward an unwritten theorem cannot be checked against anything. And:

> **It is the only artifact that can tell a lane it has been serving something
> it never checked.**

**A path is measured against its target**, so a chain with no typed target
measures its rungs against **each other** — which is internally consistent,
locally green, and unfalsifiable in exactly the way §5.3 keeps convicting.
**The cost asymmetry is the practical argument**: an unwritten target is
indefinitely expensive to be wrong about and one elaboration to be right about.

**AND ASSEMBLY-DIFFICULTY ZERO IS THE DESIGN GOAL THAT FOLLOWS.** The strong
induction is discharged **once, in the assembly file**; every side condition is
`omega`'s; the theorem reduces to **exactly two named obligations with no proof
shape.**

> **No part of the flagship's difficulty should live in its ASSEMBLY — and now
> none does.**

**The reason to state it as a goal rather than a happy outcome**: difficulty
parked in the assembly is difficulty that **every future re-founding pays
again**, and it is invisible in the obligation list, so a lane reading *"two
obligations remain"* believes it. **An assembly that is hard is an obligation
list that lies about its own length.**

**AND THE ARC CLOSED: `bound_refines_fuelModel` IS ON MASTER** (`230a7b1`) —
**typed, assembling, certified.** The theorem that had spent every archived
ladder as the words *"…and then it assembles"* is now a constant in the tree.

> **The typed-target law's first full cycle: STATED (one scratch elaboration) →
> ASSEMBLED (difficulty zero, by design) → MERGED.** R-track's §9.0 stands at
> **4/9**, with rung 3 closed on **finiteness-as-object**.

**AND A MILESTONE SCOPED BY MEASUREMENT AGAINST THE DIVERGENCE THAT COULD HAVE
UNSEATED IT** (pyc, `fcb1463`). Of `bound()`'s **four genexps exactly one
iterates a dict**, and it **creates and steps inside a single expression with
arguments pre-evaluated** — so **real play never enters the divergence window**,
and rung 9's discharge **STANDS, SCOPED**, with the row carrying
`scope_against_real_play` and **the §9.0 line stating what would have changed
it.**

> **A milestone survives a divergence only by MEASUREMENT against it — and the
> §9.0 line says what would have unseated it.**

**The alternative was available and would have been defensible**: bank the
milestone, file the row, and let the two sit in different documents. **What
makes this stronger is that the two were made to MEET** — the divergence was
measured against the exact code the milestone rests on, and **the answer is
recorded where the milestone is read, not where the debt is.** *A reader of the
number learns the risk without going looking for it.*

**AND A §9.0 NUMBER CAN BE CERTIFIED RATHER THAN COUNTED** (R-track, `2444584`,
merged). The chain doc's **4/9 was inside the tree the tenure certified**, so:

> **4/9 became true at exactly the moment the tenure went green — never a claim
> running ahead of its evidence.**

> **A standing number that lands in the SAME TREE as its last rung is
> SELF-CERTIFYING. One updated afterwards is a REPORT ABOUT a green, not part of
> one.**

**This sharpens the §9.0 stamp discipline into something structural.** The
stamp rule says *carry the sha*; **a self-certifying number does not need to
carry one, because it IS the certified artifact** — and the difference shows the
moment someone doubts it: a stamped number sends the reader to a commit to
check, **a certified number is already inside the thing the reader is checking.**
*Where the number can ride the tenure, riding it beats stamping it.*

**AND §5.0a HAS CLOSED ITS LOOP OPERATIONALLY — the milestone is
UNCONDITIONAL** (pyc's green, merged; master at `0380260`). **3 of 3
flagship-serving surfaces (scoped), `declared-divergences: 2`, 136 witnesses,
0 DIVERGE** — with **the shared checker running IN the gates: 2 tiers, 4 rows,
8 guards, every row gated both ways.** And the sentence that is the whole
justification for the ruling that created the register:

> **The invariant holds BECAUSE the divergence was moved into the REGISTER
> rather than left in the SCOREBOARD.**

**That is the design being load-bearing rather than tidy.** `DIVERGE` is zero
**and** the tier has two known differences — which under the old vocabulary was
a contradiction to be resolved by either **lying about the zero** or
**abandoning the invariant.** The register makes both unnecessary: **the
scoreboard keeps a number that means something, and the differences keep an
owner, an age, and a gate.**

**AND THE PYC DEPENDENCY IS DISCHARGED, pending its green** (`3ea2f2a`,
ticketed): **`bound()`'s `unsupported` census is ZERO**, closing rung 9's pyc
dependency — **on green the lane's §9.0 reads 3 of 3 flagship-serving
surfaces.** Recorded **conditional**, per the stamp discipline: the census is
run, the ticket is not.

**And the rung recorded a unit-family instance on the way through: THE RECIPE
TRANSFERRED UNCHANGED AND THE FUNCTION DID NOT.**

> **The two look alike in the SOURCE and are different constants in the TREE.**

**A recipe is a shape a lane can carry between sites by reading**; a function is
an object with an identity the elaborator tracks. **Transferring the recipe is
free and transferring the function is a claim** — and the two are
indistinguishable in a diff, which is where the frame-versus-loop distinction
had to be made explicitly rather than inherited. *The same family as
`bitLenSpec` existing twice (§2.4): sameness in the source is not sameness in
the tree, in either direction.*





**This closes a gap in §9's WAITING rule** (`-46`), which required an
**executable trigger** and said nothing about the **target**. A trigger that
fires against an unwritten theorem tells the lane to start work it cannot check
it has finished — so the pair is now complete: **a state names the trigger that
ends it AND the statement that defines done.** And the failure is quiet, because
prose about a theorem reads exactly like the theorem right up until someone
tries to elaborate it.

**AND A DECLINED ALTERNATIVE IS RECORDED WITH THE MEASUREMENT THAT DECLINED
IT.** The same document declined `twinAgrees` **on the plan's own pricing** —
transport pays only above **~100 mostly-mechanical theorems in one file**, and
**no file clears it** on the corrected count (§8.5's re-scoping).

> **Record the fork WITH the computed price, so a later lane finds the price
> COMPUTED rather than re-deriving it.**

**A declination without its number is a decision that must be re-litigated every
time someone new reads the plan** — and re-litigating it is expensive precisely
because the number was expensive to get. This is the provenance law pointed at a
**road not taken**: the measurement that settled it is the only part that
survives contact with a lane that disagrees.

**AND SV IS THE SECOND LANE TO LAND ITS STANDING NUMBER, with two disciplines
the table's shape did not yet name.**

**(a) LIVE IS THE HONEST DENOMINATOR — 18/21 envelopes.** Three of the
twenty-one are not live, and counting them would let a **vacuous row read as
agreement**: a row that ran nothing is not a row that agreed.

> **A coverage number's denominator counts what could have DISAGREED.**

That is §5.3's vacuity ruling arriving in the denominator rather than in a
verdict, and it is the more dangerous position, because a denominator is
**quoted without its definition** far more often than a verdict is. **The
inflation is invisible and always in the flattering direction** — dead rows
raise the numerator's ceiling and never lower it.

**(b) AND A NUMERATOR MAY BE EARNED BY FORWARDING, IF A THEOREM SAYS SO —
11/11 stepper constructors, six of them through the delegating arm.**

> **They are not reimplemented, they are FORWARDED — and the `agrees` theorem
> proves the forwarding, which is why they cannot drift.**

**The claim being made is precise, and it is worth copying because the naive
version of it is wrong.** *"Six constructors are handled"* would be a coverage
claim resting on **a reading of the code**; *"six are forwarded, and here is the
theorem that the forwarding is faithful"* is a coverage claim resting on **a
proof**. Delegation normally *weakens* a coverage number — it is the classic
place where two implementations drift — and a theorem is exactly what converts
it from a liability into a legitimate numerator entry.

**AND AN UNCLOSABLE OBLIGATION IS ADMITTED IN THE ARTIFACT'S OWN OUTPUT, NOT IN
A CAVEAT DOCUMENT** (analog F1). The tier's **model validity is architecturally
unclosable**, and `#assurance_report` prints **`model validity: MISSING`, 12
sites** — in the report a reader is already looking at.

> **A standing disclosure lives where the CLAIM is served, not where the
> apology is filed.**

**The two placements have different half-lives, which is the whole argument.** A
caveat document is read **once, by whoever is looking for caveats**; the
artifact's output is read **every time the claim is used**. An
architecturally-unclosable gap is precisely the kind that outlives everyone who
remembers it, so it has to be **attached to the thing that keeps being
consumed** — *keep it visible whenever this tier is described.*

**And it is the reason "unclosable" is not a synonym for "acceptable"**: the
disclosure does not discharge the obligation, it **prevents the obligation from
being forgotten** while remaining open, which is the same service §9.7's
*named, not counted* performs for a denominator.

**AND A SUSPICION ABOUT THE CRITICAL PATH, REFUTED — WHICH REDIRECTED THE NEXT
INCH** (SoftFloat, `mul` stated, ticketed). `mul_correct` is **one term, no
tactics**, and the coordinator's suspicion — *`roundQ` on the path* — was
**refuted by reading the obligation**: it names **CORE's
`roundWithAccuracy`.** `roundQ` **stays the independent cross-check, off the
critical path.**

> **It redirects the next inch from proving things about OUR algorithm to
> proving them about THE ONE THE TIERS ACTUALLY RUN.**

**Which is the point of the anti-circularity rule arriving as a scheduling
consequence** (cookbook §24): a spec that names no algorithm leaves the
obligation pointing at **whatever the consumers actually execute** — and the
moment someone assumes it points at the lane's own implementation, **the next
inch is aimed at the wrong artifact.** *An obligation's subject is a fact to be
read, not inferred from who wrote the file.*

**Sixth coordinator hypothesis corrected in a day**, which has stopped being
notable and is now the expected traffic — *the asymmetry MEAS-201 warned about,
running in the healthy direction as routine.*

**AND A RESIDUAL CARRIED AS A HYPOTHESIS, NOT A `sorry`.**

> **Type-checked rather than described — and NO `sorryAx` to poison
> neighbouring receipts.**

**The second clause is the load-bearing one.** A `sorry` does not merely mark
one gap; it **contaminates every axiom print in its neighbourhood** (§0.1
II(a)), so a residual left as a `sorry` **costs the receipts of theorems that
have nothing to do with it.** A hypothesis costs its consumers a premise —
visible, local, and discharged where someone is looking.

**AND THE §7.4 OMISSION PAID ITS DIVIDEND**: **no overflow side condition**,
because **`ReprQ` deliberately carries no upper bound.** *A stated omission
collecting its return* — the decision recorded as *"we are not covering this,
and here is why"* turned out to be **the reason a later obligation is smaller**,
and neither the omission nor the dividend would have been legible if the bound
had been quietly folded in.

**AND THE NUMERATOR'S HALF OF THE SAME DISCIPLINE, from SoftFloat — third
instance, and the lane excluded its own work to get it right.** Its §9.0 number
is **1/12**, with **21 real, landed theorems EXCLUDED from the numerator**,
because they are not what the family's definition of that number admits:
*"counting them would be the flattering direction I have already had to correct
twice."*

> **The DENOMINATOR counts what could have DISAGREED; the NUMERATOR counts only
> what the family's own definition ADMITS.**

**AND A THIRD UNIT QUESTION INSIDE THE NUMERATOR: ORIENTATION** (Wasm O2/O4,
`6bd3ca1`, on master; §9.0 = **4/5**). The two duals consumed **opposite
orientations of the same split lemma**.

> **A lane that had proved only one would be exactly HALF DONE AND NOT KNOW
> IT** — the name is in the numerator either way.

> **When a lemma family has an ORIENTATION, completeness is counted PER
> ORIENTATION, not per lemma NAME.**

**This is the unit family (§5.4a) arriving inside a coverage count**, and it is
the hardest instance to notice because **the artifact is genuinely there**: the
lemma exists, elaborates, is cited, and closes the goal it was written for. Only
its **dual consumer** reveals that the name covered half a fact. **The
two-orientations census reading is what paid off here** — it was taken before
the work, and it is the reason the second orientation was not discovered by a
lane finding its proof does not apply.



**Both halves are now stated, and they fail in opposite directions**, which is
why neither alone is enough: a padded denominator **understates** progress while
looking rigorous; a padded numerator **overstates** it while looking
industrious. **The second is the tempting one** — the 21 theorems are real work,
landed and green, and the only thing wrong with counting them is that they do
not answer the question the number asks.

**AND A FOURTH THING A NUMBER CAN BE MISSING: ITS POPULATION** (C lane recovery;
verify at landing). J.1(16)'s domain was carried as **7 named sites**. The
census measured the population it is a residue OF: **320 call sites → 215
orderable → 208 all-pure → the same 7.**

> **A RESIDUE WITHOUT ITS POPULATION IS A NUMBER WEARING A CONTEXT IT DOES NOT
> HAVE.**

**The seven were RIGHT the whole time**, which is what makes this worth a row
rather than a correction: **nothing was wrong with the residue, and everything
was missing around it.** Rung B's domain was read as **215** because that was
the last number anyone had; the residue had **no denominator**, so a reader
supplied the nearest one — the same reflex as §3.2's unlabelled count, arriving
through a filter chain instead of through a sentence.

**And the chain is the deliverable, not the endpoint.** *320 → 215 → 208 → 7*
records **what each filter removed**, so a later lane can ask whether the filter
was right; **"7 sites" records only that someone once believed seven.** *A
residue is a claim about everything it excluded.*

**AND A STATE PARTITION WRITTEN BEFORE THE FIRST RUN IS A HYPOTHESIS — the C
tier's first number convicted the landing that named the rule** (C inch 6,
merged `add6ad9`; **gcc.c-torture 24/300 scored, failed 0**). `not-parsed`
reported **233** against a manifest saying **30**: **clang-refused and
ingester-refused pooled under one token** — *in the landing that states the
zero-states rule.*

> **A state partition written before the first run is a HYPOTHESIS; the FIRST
> RUN is what tests it.**

> **The split is only as good as its FINEST REAL SEAM, and you do not know where
> that seam is until the instrument runs.**

**Author-blindness again, on the freshly written law** — and the useful part is
that a partition **cannot** be validated by reading: every token in it looks
distinct on the page. **The seam is a property of the corpus**, and the corpus is
the one thing the partition's author has not yet consulted.

**AND THE SPLIT PAID IMMEDIATELY**: **195 of 203 are ONE defect** (clang omits
`col` for line-only locations), so **199 of 300 are gated on a single schema
decision.**

> **A SCOREBOARD'S FIRST JOB IS NOT TO BE HIGH — IT IS TO SAY WHICH ONE THING TO
> FIX NEXT.**

**AND THAT SENTENCE NEEDED A QUALIFICATION THE NEXT LANDING SUPPLIED** (C,
`7eccf52` + `34ad979`, both merged; **24 → 28/300, with 267 of 300 reaching the
interpreter against 67 two landings ago**).

> **A SCOREBOARD REPORTS THE FIRST BLOCKER, NEVER THE ONLY ONE.**

*"199 gated on X"* means **"199 REACH X first"** — and **how many were gated on
X *and something else* is a fact only the run AFTER the fix can produce.**
Measured: **195 of the col-gated tests had `name:null` underneath**, and **four
moved.**

**AND THE LAW WAS THEN APPLIED PRE-EMPTIVELY BY A LANE TO ITS OWN CENSUS, WITHIN
THE HOUR OF PUBLISHING IT** (ES's double redirect; scoreboard approved, landings
pending). The decisive fact was *"no test can reach a verdict"* — corrected to
**"no test can reach a FAILURE MESSAGE"**, because the four intrinsics sit
**entirely in failure formatting**: *a passing test touches no intrinsic at all.*

> **A BLOCKER'S SCOPE IS PART OF THE BLOCKER. "Nothing gets through" and
> "nothing that FAILS gets through" prescribe different rungs.**

**The correction is small in words and total in consequence** — the first version
prices the intrinsics as the gate on all scoring; the second prices them as the
gate on **diagnosis**, which is a different rung at a different position. *And it
was found by the lane asking the first-blocker question of its own number before
anyone else could.*

**This is the healthiest form the law takes.** *A first-blocker claim is an
arrival count, so its scope is exactly the set that ARRIVES* — and a lane that
states the blocker without stating the traffic has published a number whose
denominator is implied by a sentence.

**So yesterday's law stands and its arithmetic does not.** *Which one thing to
fix next* is exactly right; **what a scoreboard cannot tell you is how much
fixing it buys** — the number attached to a blocker is **a count of arrivals, not
a count of departures.**

**AND PREDICTING A BUCKET IS NOT PREDICTING THE RESIDUAL.** The second miss
predicted **the largest bucket within 3** and **missed the score by more than the
score** — on a bucket (**refused-libc, 1 → 38**) that **had never had a chance to
be observed.**

> **A RESIDUAL IS A DIFFERENCE, SO IT INHERITS THE ERROR OF EVERY BUCKET YOU DID
> NOT PREDICT.**

**Which is why a confident prediction can be accurate and useless in the same
run**: the predicted quantity was right, and **the reported quantity was a
subtraction over a partition the predictor had only partly enumerated.** *Predict
the thing you will report, or report the thing you predicted.*

**AND THE STRONGEST OF THE THREE, because it explains the other two:**

> **A FRONTIER MEASURED FROM BEHIND ANOTHER FRONTIER IS A LOWER BOUND ON
> ITSELF.**

> **Each wall you remove is the FIRST HONEST MEASUREMENT of the next one — and a
> queue of blockers priced from behind the first of them is measuring its own
> ignorance.**

**Third instance of one shape in a single day** — *col hid name; ingestion hid
libc* — and it was **named by the lane's own law before the run confirmed it.**
**This is the completion framing's sharpest practical constraint**: a roadmap
built from today's frontier is **not a plan with uncertain estimates, it is a
plan whose later items have never been observed at all.** *The only way to price
the second wall is to remove the first.*

**AND THE ARC CLOSED WITH THE THIRD OUTCOME — A PREDICTION THAT HELD, AND HELD
BY STRUCTURE** (C, `b57e983`, merged; **28 → 67/300**). Two misses had already
paid for the discipline; this is the thing the discipline was for.

> **A BAND WHOSE FLOOR IS ARITHMETIC AND WHOSE WIDTH IS A NAMED IGNORANCE CAN BE
> RIGHT ABOUT A FRONTIER IT CANNOT SEE.**

**The floor was not a guess.** It was **28 already scored plus 36
exit-conversions that CANNOT hide a wall** — a test refusing on `exit(0)` **had
already run to completion**, so converting it can only add. *A floor built from
tests whose completion was ALREADY OBSERVED is arithmetic, not optimism.* The
width carried the **named unknown**: how much of the layout-freed work the next
wall would absorb.

**And both halves of "either way the row pays" landed in the same run.** The
**fourth hidden wall appeared exactly as the frontier law predicts** —
`unsupported` absorbed **~28 of the 31 layout-freed tests** — **and the
prediction held anyway**, because the band had been drawn wide enough to contain
it. **A point estimate over the same evidence would have been wrong by 30, and
would have called the SHAPE wrong too.**

> **A band that names its ignorance survives the discovery it could not have
> made. A point estimate over identical evidence does not.**

**AND A FOURTH OUTCOME JOINS THE TRILOGY: THE PREDICTION KILLED BEFORE ANY CODE
WAS WRITTEN, WITH THE DIAGNOSIS UPGRADED** (Go `§G27`, `fa625f5`, merged).
`strconv` alone measures **`+0`** —

> **"My prediction didn't just overshoot; it NAMED THE WRONG CONSTRUCT."**

**25 of 26 files are stringer output needing METHODS plus `strcat`** — *neither
of which is `strconv`.* **An overshoot is a quantitative miss and a
wrong-construct is a categorical one**, and the register should not let the
second hide inside the first: *a number that is too large invites a correction
factor; a number about the wrong thing invites nothing, because there is no
factor that fixes it.*

> **REPORT WHETHER A MISS WAS IN THE MAGNITUDE OR IN THE SUBJECT. Only the first
> is calibration data.**

**AND THE SAME LANE CORRECTED ITS STANDING NUMBER DOWNWARD AND SAID WHAT
SURVIVED** (739→717, 644→629).

> **A WRONG BASELINE AND A RIGHT DELTA IS THE HONEST DESCRIPTION.**

**The deltas survive because both sides shared the gap** — which is the one
composition rule that makes a corrected history usable rather than discarded, and
it needs stating because the instinct on discovering a wrong baseline is to
withdraw everything built on it. *A difference computed twice through the same
error is not contaminated by it; a level is.*

**AND THE LANE FLAGGED ITS OWN STREAK BEFORE ANYONE COULD READ ONE**: §G28's
destination **equals §G26's**, so *"the thing being tested is the corrected
baseline, not a fourth clean prediction — I'll say which rather than let it read
as a streak."*

> **A RE-RUN AGAINST A CORRECTED BASELINE IS A VERIFICATION, NOT A NEW
> PREDICTION. Count it in the column it belongs to.**

*Streaks are the one statistic in this register that accumulate without anyone
deciding to keep them* — nobody writes down *"prediction #4"*, and yet the fourth
green reads as one. **Which is why the lane, not the reader, has to label it.**

**And it was killed pre-code, which is where a wrong-construct miss is nearly
free** — after the code it would have arrived as an inch that landed and moved
nothing, indistinguishable from a hard problem.

**So the trilogy is complete, and its three outcomes are genuinely distinct**: a
miss **about the instrument** (predicted and reported were different quantities),
a miss **about the residual** (a difference inherits every bucket you did not
predict), and a **hold by structure** (a floor that could not fall, a width that
admitted the unseen). *Only the third is repeatable on purpose — and it is
repeatable precisely because NEITHER OF ITS TWO PARTS WAS AN ESTIMATE.*

**Which retires the version of prediction this register started with.** The value
was never a hit rate; **it is that each of the three outcomes taught something no
green could have** — and the one that held taught the most, because it is the
only one that can be *designed* rather than discovered.

**AND THE DESIGNED VERSION HAS NOW RUN THREE TIMES CONSECUTIVELY EXACT** (Go,
`+76 / +7 / +52`), with the mechanism stated rather than admired:

> **PRICE THE RUNG BEFORE WRITING THE CODE, SO THE NUMBER CANNOT BE FITTED
> AFTERWARDS.**

**Which is what makes a hit evidence at all.** A prediction written after the
work is **a description with a confidence interval bolted on**; the ordering is
the entire experiment, and it costs nothing but sequence. *Three exact calls
priced afterwards would be worth less than one miss priced in advance* — and the
register's own trilogy is the proof, since **both misses paid and neither would
have existed if the number had been written last.**

**AND THE SAME LANE ACCEPTED A ROW IT COULD NOT WIN, WHICH IS THE OTHER HALF OF
PRICING HONESTLY.** Two behaviours alias in **opposite directions** — spread
aliases, packing is fresh — so:

> **A model with ONE code path for both fails one row whichever way it chooses.**

**Naming that is a result, not an excuse**, and the distinction is testable: *an
excuse names a cost, a result names the ROW THE COST FALLS ON and why the other
choice moves it rather than removes it.* **A known-unwinnable row left visible in
a scoreboard is worth more than a scoreboard with a code path added to hide
it.**

**AND THAT LAW IS NECESSARY AND NOT SUFFICIENT — CONFESSED BY THE LANE THAT
PRODUCED THE STREAK, WHICH IS THE STRONGEST POSSIBLE SOURCE** (ES, same
landing). *"Every number I have given you so far is a vocabulary proxy…"*

> **"THE FOUR INCHES OF EXACT PREDICTION-VS-ACTUAL HAVE BEEN MEASURING MY OWN
> INSTRUMENT AGAINST ITSELF."**

> **WHERE PREDICTOR AND SCORER SHARE AN INSTRUMENT, AN EXACT MATCH IS A
> TRANSCRIPTION CHECK, NOT A CALIBRATION.**

**So pricing before the code is one of TWO conditions, and this register had only
carried the first.** Ordering removes the fitting; **independence removes the
tautology** — and the second is invisible in exactly the way the first is
visible, because *a prediction and a score computed through one instrument agree
for reasons that have nothing to do with the world.* **An exact match is the
signature of the defect, not evidence against it:** two independent estimates of
a real quantity land near each other, **not on each other.**

**Which retires the reflex of reading a streak as calibration, and I am recording
that this register was reading it that way.** *Four exact inches is the least
likely outcome of a sound calibration and the most likely outcome of a shared
proxy* — and the observation was available the whole time, in the digits.

**The remedy is structural and cheap: the predictor and the scorer must not be
the same instrument.** Predict in one vocabulary and score in another, or predict
a quantity the instrument does not compute. **A lane that cannot arrange that
should report its numbers as a proxy's, which is what this lane did** — *the
confession is the correct output when independence is unavailable.*@@MARK@@

**AND A FRONTIER ENTRY BECOMES ACTIONABLE WHEN ITS INSTRUMENT COMPONENT IS GONE
AND SAYS SO.** After the layout work, the **54 remaining `no-layout` are ENTIRELY
struct/union.**

> **The instrument's share of that number is gone.**

**A mixed bucket purified into a single named cause** — and note that **the
number did not have to fall to improve.** It went from *"some of this is us and
some of it is C"* to **one cause a reader can price**, which is a different kind
of progress from a score moving and is invisible in the score. *A scoreboard inch
should report WHICH of the two it got*; a lane reading only the totals cannot
tell a purified bucket from a stuck one.

**AND A BUCKET'S INTERNAL DISTRIBUTION DISTINGUISHES A FRONTIER FROM AN
ARTIFACT.** The remaining libc frontier is **4 entries under four distinct names
with no dominant one** — **the shape a genuine libc frontier has.** The **36-exit
spike** it replaced was **one oracle convention wearing a libc costume.**

> **A REAL FRONTIER IS FLAT AND WIDE. A SPIKE INSIDE A SINGLE BUCKET IS AN
> INSTRUMENT'S SIGNATURE.**

**And this is a test a lane can run WITHOUT FIXING ANYTHING** — before choosing
the next rung, look at how the bucket's mass is spread. **One name holding most
of a bucket is a hypothesis that the bucket is misnamed**, and it is the cheap
half of the frontier law: *you do not always have to remove the wall to discover
it was not one.* **The expensive half remains** — a flat bucket still has to be
walked through to be priced.



**Which is the answer to the question §9.0's completion framing keeps
provoking**: a low number is not a problem to be managed, it is **a measurement
whose value is its resolution.** *24/300 that names one schema decision is worth
more than 200/300 that names nothing.*

**AND THE EIGHT-WAY ZERO-STATE LINE SUMS TO 300.**

> **Nothing unaccounted for is the property the split EXISTS to give — a
> CONSERVATION CHECK is the scoreboard's own integrity gate.**

**A partition that does not sum is not a partition**, and the check is free: it
catches double-counting, dropped rows and silently-absorbed categories **in one
arithmetic identity**, without knowing anything about what the categories mean.
*Every zero-state vocabulary in this family should carry one.*

**AND THE VOCABULARY NEEDS A SECOND AXIS, WHICH THE FIFTH WALL SUPPLIED ON
SCHEDULE** (C, `b57e983`; `timeout` **0 → 2**).

> **A BUCKET THAT HAS NEVER BEEN NON-ZERO IS NOT A MEASURED ZERO; IT IS A BUCKET
> NOTHING HAS REACHED YET.**

**Which is this scoreboard's whole doctrine seen once more from the inside.** The
partition summed, every row was accounted for, and **one accounted row was
reporting the FRONTIER'S POSITION rather than the tier's behaviour** — a `0`
meaning *no test got this far*, printed in the same column, in the same
typeface, as a `0` meaning *we handle this*.

**And this is §5.2's gate taxonomy met again in a new artifact, minus the thing
that made it safe there.** *Empty because the corpus does not reach it* is the
first of the three kinds of empty gate — **but a gate records its emptiness WITH
ITS REASON, and a scoreboard cell records an integer.** *The same distinction
that is written down at a gate is erased by a table.*

> **Only FRONTIER MOTION converts an unreached zero into a measured one, so a
> zero's kind is a fact about the RUN, not about the row.**

The cheap discipline is one the eight-way line already supports: **a row's zero
is a measurement only once a test has ARRIVED at it and LEFT** — readable
directly off the conservation check, since an unreached bucket is one whose mass
is still sitting in some earlier wall. *A zero you have never seen a candidate
for is a prediction wearing a result's clothes.*

**AND A REFUSAL-BASED TIER'S HONEST NUMBER READS DIFFERENTLY FROM A PASS
RATE.** **24 scored, 0 failed** —

> **The tier does not get torture tests WRONG. It DECLINES them.**

**And the 3 UB refusals NEVER retire, because THEY ARE THE PRODUCT.** *That is
not a permanent debt* (§5.0a admits none) — **a refusal that is the tier's
deliverable is not owed to anyone**, and the distinction is exactly the one the
permanent-row ruling turns on: **a debt is something the number waits on; a
principled refusal is part of what the number MEANS.**

**AND A THIRD AXIS: A COVERAGE BOUND HAS A DIRECTION, AND MUST STATE IT**
(analog census). Go's syntactic measure **OVER-counts** — an **upper** bound.
The analog tier's grounding grep **UNDER-counts** — a **lower** bound:
`dram_bank_256x32` reads as ungrounded while being grounded semantically under
another spelling, and the instrument **flags it `NO-GROUNDING-WITNESS` in its
own output** rather than silently scoring it.

> **"SYNTACTIC ⇒ UPPER BOUND" IS NOT GENERAL.** The direction depends on whether
> the measure can produce **false positives** or **false negatives**, and a
> measure can do either.

**AND THE SHARPEST VIOLATION OF THAT RULE CAME FROM THE LANE THAT WROTE IT** (Go
`§G27`). *"The coverage table's own guard says it measures SYNTACTIC coverage, an
upper bound — and I wrote that guard and then used the number as if it were
executable."*

> **A GUARD IN PROSE IS OBEYED BY WHOEVER IS READING IT, AND ITS AUTHOR IS THE
> LEAST LIKELY PERSON TO BE READING IT.**

**This is the docstring-expiry family entered from the instrument side**, and the
authorship detail is the finding rather than an embarrassment: *writing the
caveat is what discharges the feeling that produces re-reading it.* **A qualifier
an author has already internalised is a qualifier that author will never see
again** — which is the argument for the sign living in the instrument's OUTPUT,
beside every number it prints, rather than in the table's header.

**AND THE THIRD INSTANCE OF ONE-AST-KIND-TWO-THINGS CAME WITH THE RIGHT STANDING
CONCLUSION:** *"I should have gone looking for it rather than tripping over
it."*

> **A SHAPE WITH TWO INSTANCES DESERVES A SWEEP FOR THE THIRD.**

**Two is where a family becomes searchable**, and the sweep is nearly always
cheaper than the third incident: *the second instance supplies the query.* **This
register has been recording families and waiting for their members to arrive; the
rule now is that the second member triggers a search rather than a note.**

**So a coverage number now carries three things, and they fail independently**:
the **denominator** (what could have disagreed), the **numerator** (what the
family's definition admits), and the **SIGN** (which way the number is wrong).
**And a FOURTH axis arrived from the analog tier's A13** (`130dd20`, ticketed):
**DIRECTIONAL COMPLETENESS.**

> **A kit built from SETTLING circuits is complete for settling and silently
> missing a direction for REGENERATING ones. Decay and growth are not one
> obligation with a sign flipped — only ONE of the two falls out of
> `add_one_le_exp`.**

**A kit's completeness is relative to the corpus that built it**, and the failure
is silent because the missing direction is not a hole in a list — *it is a
lemma-shaped absence that nobody notices while every deck they own settles.*
**The generalization is the one the other three axes already teach**: a number, a
kit and a library all describe the corpus that produced them, and **the honest
statement names that corpus rather than the artifact.**
**Two lanes quoting bounds in opposite directions and neither saying so is how a
cross-tier table becomes unreadable** — 40% upper and 40% lower are not the same
40%, and the difference is invisible in the digit.

**AND THE AUDIT THAT FOUND IT PAID BY NOT FINDING WHAT IT LOOKED FOR** (same
landing). The coordinates were **fine**; the blocker was **the deck's PHYSICS** —
a sense amp *regenerates*.

> **From the PROOF side the missing direction would have surfaced as a failed
> `exact` deep in a tactic block. From the COORDINATES it surfaced as a property
> of the deck's physics BEFORE A TACTIC RAN.**

**Which is the clearest statement this register has of what a structured audit
buys**: not a faster path to the same error message, but **an error stated in the
domain's vocabulary instead of the prover's.** *A failed `exact` says a step did
not close; a regenerating sense amp says which physics the kit does not cover* —
and only the second tells a lane what to build.

**And an audit's value is not conditional on its hypothesis being right.** The
coordinate list was built to find a free coordinate and found none; **the pass
that found nothing is what promoted the real blocker into view**, because
eliminating the cheap explanation is what leaves the expensive one legible.
*Report an audit that confirms its subject as a result, not as a wasted tenure.*

**AND A KIT IS SHARED ONLY WHERE IT IS IMPORTED** (same landing).

> **Three decks having it says NOTHING about the fourth. Import closure is a
> PER-CONSUMER fact.**

**The same unit defect the fleet line already carries, in the substrate**: *"the
kit is shared"* is a summary of a set, and the coverage question is always
**which members**. §3.1's grep discipline is the mechanical form — *list who
imports it* — and this adds the direction lanes actually get wrong: **not who
would be affected by moving it, but who is not getting it at all.**

**And the instrument naming its own uncertain rows is the honest form of a lower
bound**: not *"we may be under-counting"* in a caveat, but **a labelled row in
the output**, countable by whoever reads it next. *A caveat is prose; a flagged
row is data.*

**AND AN AUDIT'S SCOPE DECLARATIONS BELONG IN ITS OUTPUT, WHICH IS THE SAME RULE
ONE LEVEL UP** (QoL's census self-correction, `771ed1c`, merged). Three defects
in the audit instrument, and the visibility clause is what makes them a law:

> **Neither the REACH nor the LABELLING was stated in the table — which is what
> let a wrong row look authoritative.**

**A table is read by people who will never open the instrument**, so an
undeclared scope is not a gap in the audit, it is **a false claim of
completeness** made by the layout: rows present, no boundary drawn, therefore the
boundary is the corpus. *The flagged-row rule above says an instrument names its
uncertain rows; this says it names the EDGE OF ITS OWN REACH in the same place.*
**An audit that knows its limits and prints them elsewhere has not printed
them.**

**AND THE CORRECTION ITSELF IS THE ITEM, BECAUSE IT WENT THE UNFLATTERING WAY.**
The attractive hypothesis — an inversion window in which R-track's refusals were
wrong — was **killed by reading two `printf` lines:**

> **"THE INVERSION NEVER HAPPENED — the arithmetic was always `100-f`; only the
> LABEL moved."**

**Both parties wanted the sharper finding, and neither got it.** *"I'd rather say
that plainly than accept the more flattering version — the sharper finding would
have been more valuable, and it isn't what the evidence shows."* **R-track's
refusals were real and correct; no failure window exists.**

> **A HYPOTHESIS BOTH PARTIES WANT TRUE IS THE ONE THAT NEEDS THE CHEAPEST
> CHECK RUN FIRST — because nobody in the conversation is positioned to doubt
> it.**

**This is *claims, not claimants* in its hardest direction: not a lane correcting
a coordinator, but a lane correcting a story that flattered them both.** The
register has been collecting the healthy-direction evidence; **this is the first
instance where the incentive pointed at the FINDING rather than at a person**,
and the cost of getting it wrong would have been a law minted on an incident that
never occurred. *Two `printf` lines is the entire price of not doing that.*

**AND THE FAMILY IS COMPLETED BY A LANE RETRACTING ITS OWN MOST INTERESTING
HYPOTHESIS** (R-track, merged). *"I had one datum — a label string — and produced
a mechanism from it, then reported the mechanism as a finding. It was checkable
and I didn't check it before reporting."*

> **A GUESS OFFERED AS A FINDING IS A DEFECT EVEN WHEN THE GUESS IS
> REASONABLE.**

**Reasonableness is the aggravating factor, not the mitigation.** *An unreasonable
guess is discarded by the next reader; a reasonable one is adopted*, and it
propagates with the authority of the report that carried it. **The defect is not
the inference — it is the CHANNEL**: a mechanism inferred from one datum is a
hypothesis, and publishing it in the slot reserved for measurements strips the
one label that would have told anyone to check.

**And the walkback was done properly, which is the part to copy**: the earlier
readings were re-filed **UNKNOWN, not "artifact."** *Replacing a wrong mechanism
with a different mechanism is the same defect twice* — **the honest replacement
for a retracted explanation is the absence of one.**

**So the incentive-at-the-finding family now has all three of its directions**: a
lane correcting a coordinator, a lane killing a story that flattered both, and **a
lane retracting the most interesting thing it had said.** *The third is the
hardest, because nothing external forces it and the finding was the lane's own
contribution.*

**AND THE INSTRUMENT RETIRED ITSELF IN FAVOUR OF THE MECHANICAL CONTROL** (same
landing).

> **"The GUARD remains the durable answer; this sweep is ONE-TIME EVIDENCE, not a
> repeatable instrument."**

**A sweep that answers a question once and a guard that answers it forever are
different artifacts, and the sweep is the one that rots.** *Keeping it invites a
later lane to re-run it and trust a number whose corpus assumptions have
expired* — the expiry law above, applied to an instrument instead of an argument.
**An instrument that states its own single-use scope is doing the same work as a
row that names its retirement condition.**

**TWO MORE LANES' NUMBERS, and one is calibration evidence in its own right.**

* **ES — 38/66 kinds**, in-vocabulary **2 869 → 4 118**, **+1 249 matching its
  census prediction EXACTLY.**

  > **A census that predicts its own gain TO THE UNIT is calibration evidence,
  > not just a number.**

  Every other reach figure in this document is a **measurement**; this one is a
  **prediction that was then measured**, which is the only way an instrument's
  accuracy — as opposed to its output — is ever established. **An instrument
  that has never predicted has never been tested**, and a lane that can hit its
  own forecast to the unit has earned the right to schedule on forecasts.

  **AND THE DISCIPLINE'S PURPOSE IS RE-FOUNDED BY TWO MISSES IN ONE DAY** (C,
  both merged). The lane's own words:

  > **Not calibration, but a repeatable way of discovering that THE THING BEING
  > PREDICTED WAS NOT THE THING BEING MEASURED.**

  **Two of three predictions missed for STRUCTURALLY INVISIBLE reasons — and
  that is the YIELD, not a failure of the predictor.** A prediction that lands
  confirms an instrument; **a prediction that misses for a reason nobody could
  have seen names a seam in the measurement**, which is the more valuable
  return and the one a lane cannot get by being careful.

  **So the calibration row's ambition shrinks and its usefulness grows.** *An
  instrument that has never predicted has never been tested* stays true; what
  changes is **what a miss is evidence OF** — not *the predictor was sloppy*
  but **the predicted quantity and the reported quantity were different
  quantities**, and the run is what distinguished them. *A discipline whose
  failures are informative does not need a high hit rate to be worth running.*

  **AMENDED, AND BY THE PREDICTING LANE ITSELF — the second exact match was
  DEFLATED BY ITS OWN AUTHOR** (ES, on `+1,249`). *"Both numbers come from the
  same vocabulary instrument, so an exact match confirms the implemented set
  equals the priced set — it is not independent evidence that anything
  passes."*

  > **An exact match is evidence about the PRICING INSTRUMENT only when the
  > PREDICTOR and the SCORER are INDEPENDENT. A same-instrument match verifies
  > TRANSCRIPTION, not truth.**

  **Both halves stand** (MEAS-181). The original is right that *an instrument
  that has never predicted has never been tested* — **prediction remains the
  only way accuracy is established.** What it did not say is **what a match is
  evidence OF**, and the answer depends entirely on whether the thing scoring
  the prediction is the thing that made it. **Same instrument: the two numbers
  agree because they are one number computed twice**, which is worth having —
  it catches transcription error — and is **not** the claim *"the priced work
  landed."*

  **And the deflation is the register-grade part**, not the correction: **the
  author of an exact hit argued against their own headline.** *A calibration
  claim volunteered downward by the party it flatters is the only kind that
  needs no re-reading.*
* **Lean tier — the export corner NAMED, NOT COUNTED, its 28th obligation**: a
  byte-level round-trip conditional on core's unproved `Json.parse ∘ compress`,
  so **27 stays the denominator.** Same family as the vacuity-in-denominator row
  above, arriving through the opposite door — **not a dead row inflating the
  denominator, but a live obligation deliberately kept out of it** until its
  premise is proved. **Named so it cannot be forgotten; uncounted so it cannot
  flatter.**

**AND THE RIDER THAT MADE §5.6's SELECTION CRITERION ROUTINE: WHEN THE
DISCRIMINATOR HAS NO CORPUS WITNESS, IT MOVES INTO THE CALL.** Copy-by-value is
the fixed-array value model's decider, and **the corpus does not do it**:
`a[:]` outnumbers bare-identifier copying **1 911 to 152**, and in the 76
unlocked files **1 407 `[N]T` occurrences yield 23 possible copies** — all six
in-reach candidates being trivial wrappers taking `*[N]byte`, **pointers
precisely to avoid copying.**

> **No corpus witness is not a dead end; it relocates the discriminator.** The
> `(function, argument)` law says the case is a **call**, so a decider the
> corpus never exercises is supplied by **choosing the call**, not by
> commissioning a program.

**This is the moment that law stopped being a description and became a
procedure**: census for a witness → if none, move the discriminator into the
call → confirm the call is one a caller would write. Go ran exactly that
sequence and it produced `runtime.printuint` with one array and two operations.

**A MILESTONE IS A WAYPOINT, AND THE REGISTER RECORDS IT AS ONE.**

> **"The exemplar is complete" describes an EXEMPLAR. It never describes a
> TIER.**

**The failure mode already has a name here**: it is the construct-versus-verdict
naming law (§5.4) at the scale of a project. *"First full function-level theorem
about a vendored program"* names **what was achieved** and stays true; *"the tier
is done"* would be a claim about **a suite number**, and only a suite number can
settle it.

**And the reason a waypoint reads as an ending is worth stating, because
nothing about the waypoint is wrong**: a completed exemplar is the first thing
in a tier that **feels finished** — it has a theorem, clean axioms, and a name.
**The defect is entirely in what a reader infers next**, which is why the
correction belongs in the register rather than in the landing.

> **THE OPERATIONAL TEST: a claim of completion cites a SUITE NUMBER and its
> SHA, or it is a claim about an artifact and not about a tier.**

**DEFERRED-UNTIL-CONSUMER UNLOCKS ARE AUTHORIZED WHEN THE DEFERRAL'S CONSUMER
IS COMPLETION ITSELF.** This document has been strict that *adding a snapshot
without a consumer is designing against nothing* and *predicting a consumer is
not having one* (§3.4). Under a completion goal, one consumer is now standing:

> **THE SPEC SURFACE IS A CONSUMER. A deferral whose trigger was "when someone
> needs it" is unlocked when COMPLETION needs it.**

**First instance: Go's `go/types` extractor tier** — deferred while nothing
consumed selector resolution, and now required, because the stdlib reach the
tier is measured by runs through it (§5.4a's *value or reference* split names it
as the extractor's work).

**And the guard that keeps this from licensing speculative building, because it
would otherwise retire a law that has paid for itself:** completion authorizes
**the work**; the census still authorizes **the order** (§9.0b). *"Completion
needs it eventually"* is true of every construct in the language and therefore
prices nothing — **the reach census says which unlock is next, and the
conjunctive law says which ones must ship together.**

**AND ONE OBSERVATION ABOUT WHY CORPUS-DRIVEN SELECTION WORKS, recorded because
it reads as luck and is not** (Go, `4bda5af`). The exemplar was reachable at all
because `bigmod.bitLen` **hand-rolls its loop to avoid the lookup table**
`bits.Len` uses — the crypto source says so in its own comment — and lookup
tables need exactly the array types and indexing the tier does not have.
**The census picked the one function in the neighbourhood that does not need the
construct the tier lacks, without knowing that was why.**

> **Corpus-driven selection finds the frontier's traversable point BY
> CONSTRUCTION: a ranking over what the tier can EXECUTE is already filtering
> for what the tier can PROVE about.**

The lane did not identify the constraint and then hunt for a program obeying it;
it ranked the corpus by what the tier could run, and the constraint was
satisfied **silently**. That is the argument for ranking by executability rather
than by interest: **a selection rule defined over the tier's own capability
cannot pick an unreachable subject**, and a human choosing *"the interesting
function"* routinely does.

**And the honest limit is in the same census, which is what makes it a strategy
rather than a happy accident**: the next inch — `math/bits`, 49 exported
functions, 26 with plain integer signatures — is blocked on **exactly the eight
table-driven ones**. So corpus selection both finds the traversable point **and
names the wall**: the census that picked `bitLen` also priced the next step, and
it priced it in constructs rather than in effort.

**AND A LANE MAY BE *WAITING*, BUT ONLY WITH AN EXECUTABLE TRIGGER** (Lean
tier, `38766b4`). The tier is now WAITING, and what makes that a **state**
rather than a euphemism is that the thing it waits for is **a command's output,
not a feeling**: *a **DRIFT** in the obligation census's `real` count, or
`VEnv.addInduct` / `VInductDecl.WF` leaving `proof_layer.definitional_stubs` —
which is **PR #43 landing**, and unblocks 15 of 24.*

> **WAITING NAMES AN EXECUTABLE TRIGGER, OR IT IS A EUPHEMISM FOR STOPPED.**

**AND UNDER §9.0's COMPLETION GOAL THE RULE TIGHTENS: WAITING IS A PROPERTY OF A
SLICE, NEVER OF A LANE.**

> **A blocked slice waits. The LANE's foreground moves to a new censused
> corner.**

**First instance: the Lean tier** — the upstream-blocked obligations keep their
trigger and their standing guard duty, and the lane's foreground work is
re-censused rather than suspended. **A lane that has nothing to do because one
slice is blocked has not measured its corpus**, which is §9.0b's partial order
read as a work queue: the blocked slice is one node, and a census that produced
only one node was not a census.


**The trigger has to be something a periodic run can ANSWER**, which is why the
form matters: *"when upstream is ready"* is unfalsifiable and ages into silence;
*"when this number moves"* is a check with a verdict, and the lane can be wrong
about it in public.

**AND THE ENABLING CONDITION IS AFFORDABILITY, which is the half a lane skips.**
The standing duty here is **pure Python over out-of-tree corpora — no Lean, no
tenure, no ticket** — so it can run at any cadence. **A waiting duty priced at a
tenure is a duty that will not be run**, and an unrun duty is a plan (§5.4b).
So the two halves are one design: **name a trigger a cheap command can answer,
and keep the command cheap enough that nobody has to decide whether to run it.**

### 9.0a CENSUS-FIRST APPLIES TO THE LEMMA, NOT ONLY THE OBLIGATION

**§9.7's duplication instance for this tick, owned by the lane that paid
for it.** The successor proved `heapEqFuelMono` (14 arms, clean axioms)
and half of `evalCompareOpH` before discovering that
`LeanModels/Python/Obs.lean` **already carried all of it**: `Res.le` and
its congruences — **identical, in the same namespace, a hard name clash
waiting** — plus `heapEqMono`, `evalCompareOpH_mono`, `valContains_mono`,
and **the trunk's full `fuelMono` with ~15 corollaries.**

The cause, in the lane's own words:

> *"I applied census-first to the proof OBLIGATION and never ran the one
> grep that would have found existing monotonicity work."*

**That is the census law with a blind spot, and the blind spot is
structural rather than careless.** Censusing the *obligation* asks *"what
must be true?"* and is the discipline this document has been prescribing
since §1. It does not ask *"has someone already made it true?"* — and a
lane that has correctly censused its obligation feels **finished with
census-work** precisely when the second question is still unasked.

> **Before proving `X_mono`, grep the tier AND `Core` for
> `_mono|Mono|\.le\b`. The grep that would find your own work already
> done is the one most worth running.

**AND THE GREP THIS SECTION PRESCRIBES HAS ITS OWN FALSE POSITIVE — in the
tier it was written for.** In the monadic Python tier **`Mono` means
MONADIC**: `callInMono`, `runScriptMono`. So the recommended pattern
returns hits that have nothing to do with monotonicity, and the rule that
governs it is the ladder's, applied to itself:

> **A grep's hits are CANDIDATES TO READ, never findings.**

That is the same discipline SoftFloat's census reached by a different route
— *candidates kept apart from the count, resolved by reading* (§5.4a). A
prescribed grep is not exempt from the law that prescribed it.**

It is also the retrieval laws' fourth face (§5.4a): *the search that agrees
with your prior* is about believing a hit; *count the pattern position* is
about pricing; *file the residue* is about reporting; **this one is about
starting** — the grep you skip because you already know what you are about
to build.

**AND THE FAMILY GAINS ITS SHARPEST MEMBER — AN 8-SECOND RED THAT WAS WORTH
MORE THAN A GREEN** (SV; the lane's own words). §L87 recorded an obstacle: four
do-stepping lemmas the tier needed did not exist. **They existed in `Obs.lean`
the whole time — same namespace, one import away, out of scope**, because the
work-in-progress file imported `SelfCheck`, which does not import `Obs`.

> **EVERY SYMPTOM OF A MISSING LEMMA IS ALSO A SYMPTOM OF A MISSING IMPORT.
> Before recording an obstacle as "X does not exist", grep the namespace across
> the TREE, not the imports in scope.**

**The two failures are indistinguishable at the point of use** — an unknown
identifier reads identically whether nothing defines it or something does, one
import away — and the diagnosis a lane reaches for is the expensive one. This is
the **second time in one tier** that a lane "needed" what it already had, and
**both were found by building**, not by reading: §9.0a's opening instance
(`heapEqFuelMono`, already in `Obs.lean` with ~15 corollaries) and this one.

**Note the direction, because it is why the section keeps collecting these**:
the failure is **flattering to the plan**. *"The lemma does not exist"* converts
a five-minute import into a scheduled inch, and nothing contradicts it — the
build agrees, loudly, every time.

> **RIDER — the same grep, run FORWARD: pre-flight a name-collision check for
> every name a landing DECLARES.**
>
> **AND ITS SECOND HALF, which the clash check does NOT cover** (SV): a clash
> check finds **duplicate declarations** — names you DECLARE that already exist.
> It says nothing about **identifiers that resolve NOWHERE** — names you USE
> that no module in the closure defines. **An import-reachability check
> completes the pair**: resolve every capitalized identifier a new file uses to
> its defining module, and confirm that module is in the closure.
>
> **The two halves are the same query pointed in opposite directions**, which is
> why they are stated together: *what am I about to shadow* and *what am I about
> to reference that is not here.* The second is the one that produced the
> 17-second red above, and the one a lane skips because the build "will just
> tell you" — which it does, in whatever vocabulary the missing name happens to
> trigger.
>
> **And its one false positive was NOTED, not papered over**: a **docstring**
> naming another tier's type resolves nowhere and is not a defect.
> **Comment-stripping is the known fix**, and recording the false positive with
> its remedy is what keeps the check from being quietly narrowed to make the
> noise go away (§5.4b: a de-dupe could silently shrink a set). The tree-wide namespace grep that finds what
> you already have is the identical query that finds what you are about to
> shadow, and §9.0a's opening instance had *"`Res.le` and its congruences —
> identical, in the same namespace, a hard name clash waiting."* One grep,
> two defects, opposite directions.

**AND CENSUS-FIRST HAS NOW SHOWN ITS STRONGEST FORM — the census run AFTER a
plan, refuting the plan's premise before it is paid for** (Go, `69ea58a`). The
rung was scoped as *"the table functions need array types and indexing"*. They
do not: **all four tables (`len8tab`, `ntz8tab`, `pop8tab`, `rev8tab`) are
untyped STRING constants**, `Len8` is `int(len8tab[x])`, and the acceptance case
is **string indexing plus a type conversion** — no arrays, no slices anywhere in
it.

> **A census is worth running even when the plan is already written. Especially
> then: the plan is the hypothesis, and the census is the only thing that can
> refute it before it is paid for.**

**Two things make this the strongest instance rather than another one.** It is
the **second** time the corpus corrected a rung's definition *before a line of
it was written* — and the **first time it corrected an entry this lane had
already published.** A published entry is the hardest kind of premise to
re-examine, because it has already survived a review and been cited; the census
had no way of knowing that and refuted it anyway.

**The practical rule that falls out**: *census-first* is not a phase that ends
when planning ends. **Re-run the census at the moment the plan becomes
expensive** — the inch before the work, not only the inch before the design —
because that is the last point at which a refutation is free.

### 9.0b RUNG SCHEDULING — a reach census does not just RANK; it PARTIALLY ORDERS

Two laws from the same measurement (Go, `4618380`) — **and one of them has since
been RETRACTED BY MEASUREMENT, which is recorded in place rather than deleted
(`5b3602f`).** Read the retraction first; it changes how the section's own
numbers are quoted.

**THE FIGURES THIS SECTION FIRST CARRIED ARE WITHDRAWN.** *"1 289 of 3 084 —
41.8%, rising to 74.8%"* **counted `SelectorExpr` as steppable**, which §G8 had
already ruled `go/types` work and the walker refuses. The reproducible figure
for the family as landed is **512 → 604 of 3 803 files**.

**And the reason the old number could not simply be re-checked is the sharper
lesson, and it is §5.4's contract, violated:** that reach table **left no
instrument** and its **vocabulary was unrecorded**, so it could not be re-run at
all — only replaced. A table is not a census.

> **A NUMBER PRODUCED BY A ONE-OFF SCRIPT IS A NUMBER THAT CAN ONLY BE
> WITHDRAWN, NEVER CORRECTED.**

MEAS-2/MEAS-3 exist for exactly this: a named instrument at a fixed path, with a
`--compare` mode, is what makes a wrong number **fixable** instead of
**disposable**. It is now `construct_census.go --reach`, which splits
`ArrayType` (`go/ast` spells `[]T` and `[N]T` with one node) and **keeps the
vocabulary as data**.

**AND THE FOURTH REPRODUCTION HAS PROMOTED ONE PROXY FROM UNRELIABLE TO
ACTIVELY MISLEADING** (Go `§G26`, merged).

> **SELECTION COUNT IS NOW THE MOST RELIABLE WAY TO PICK WRONG.**

`fmt` carries **9.5× `strconv`'s selections** and **one-sixth its reach.**
**Four reproductions is past the point where this is a caution** — *a proxy that
is wrong four times out of four is not noise, it is a signal with the sign
reversed*, and the register should say so in the imperative: **rank by reach,
and treat a high selection count as evidence AGAINST picking a package**, since
the thing selections measure is how much surface a package touches, not how much
of it the model can execute.

**AND A CANDIDATE WAS SKIPPED WITH A LAW RATHER THAN A PREFERENCE** — `syscall`:

> **A PACKAGE THE MODEL WILL NEVER RUN IS NOT ONE IT CAN BE CREDITED FOR.**

*Reach is a claim about execution, so a denominator that includes the
unexecutable is inflated at the source* — and this is the numerator/denominator
discipline reaching **rung selection**, where it decides what work gets done
rather than how a finished number reads. **Skipping it is not a gap in the
scoreboard; counting it would have been.**

**(1) THE `+0` LAW — STATED HERE, THEN RETRACTED BY THE NEXT MEASUREMENT.
What it said:** *a construct measuring `+0` is not cheap, it is unreachable —
not a rung at any price, strictly downstream of whatever co-occurs with it.*

**What refuted it:** `RangeStmt` **measures `+0` alone** and is **worth `+9`
inside the family it shipped in** (`5b3602f`). The premise was that a `+0` is a
*property of the construct*. It is not:

> **A CONSTRUCT'S DELTA IS A FUNCTION OF THE CURRENT VOCABULARY, NOT A PROPERTY
> OF THE CONSTRUCT. A `+0` is a reading of TODAY's walker, and it moves when the
> walker does.**

So maps (`+8/+14`) and interfaces (`+4/+7`) are **not disqualified** — only
**still small**. The corrected reading of a `+0` is *"nothing is blocked ONLY by
this, at this vocabulary"*, which is a fact with a **timestamp**, not a
precedence fact (MEAS-10, arriving where a law was being minted rather than a
number).

**WHY THIS ONE WAS WRONG IS WORTH MORE THAN THE LAW WAS.** The error was
**generalizing a differential to a property**. `+0` is a *delta* — it is defined
relative to a baseline — and the whole content of a delta is the state it was
taken against. Reading it as a property of the construct is **the state-stamp
failure committed at the level of a LAW**, and it is easy precisely because a
construct feels like a fixed thing while a walker feels like a moving one.

> **When a law is minted from a DELTA, the law inherits the delta's baseline.
> State the baseline in the law, or the law is a measurement pretending to be a
> principle.**

**What survives, and it is the part worth keeping**: the census still induces a
partial order — some constructs really are reachable only behind others — but
**a single `+0` does not establish it**, because the same construct can be
`+0` alone and positive in company. That is the conjunctive law below, and the
retracted law was its shadow: **both readings come from the same fact — deltas
are not additive — and only one of them is true.**

**(2) THE CONJUNCTIVE LAW — PROMOTED FROM LANE OBSERVATION TO FAMILY LAW, on
its third independent reproduction.**

> **Some constructs have value only as a FAMILY. Ship any one and almost
> nothing moves; ship the family and the reach steps.**

**And it is the law that SURVIVED the retraction above, on the same evidence
that killed the other one** — `RangeStmt` being `+0` alone and `+9` in company
is the conjunctive law's cleanest possible instance, restated as a refutation.

Measured, in the sharpest instance yet: `ArrayType` alone **+528**, `SliceExpr`
alone **+27**, `RangeStmt` alone **+29** — **sum of parts 584** — and **all
three together +1 019**, a **1.7×** gap, taking reach from **41.8% to 74.8%**.
The lane's first two reproductions were §G1's bundles and §G4's switch family;
**this is the first where the parts are individually near-worthless in single
digits**, which is what makes the law's failure mode concrete: **a lane pricing
these three separately would have rejected all three.**

**Three independent reproductions is this document's own evidence bar** (§9.3's
convergence standard), so it is family law from here rather than a Go
observation: **price a candidate rung against the FAMILY it belongs to, and
report both numbers** — alone, and jointly. A per-construct table with no joint
column is not just incomplete; **it systematically under-prices exactly the
rungs worth taking.**

**AND A THIRD LEVEL, measured: BUNDLE → FAMILY → PACKAGE-FUNCTION** (Go E1,
`4a9f9ec`, on master). §G21 priced `math/bits` at **+7** from the package
ranking. E1 built the mechanism and it measured **+0**.

> **A FILE NEEDS EVERY FUNCTION IT CALLS, NOT THE PACKAGE'S NAME.**

The 7 files are the fiat64 curves, `math/big/arith.go` and `strconv/itoa.go`,
and what blocks them is `Add64` (2 077 sites), `Mul64` (1 038), `Sub64` (186)
and `Div` — **all MULTI-VALUE RETURNS**, which block **88% of `math/bits`' call
sites.** So the conjunctive law has a third granularity: **constructs bundle
into families, and families bundle into the CALLABLE SURFACE a file actually
needs.** Pricing a package by its ranking prices **a name**; the file needs
**every function in the call**.

**AND A THIRD USE, with a CALIBRATION PREDICTION attached** (Go §G23,
`9a6d6ad`). Reach was **unmoved deliberately and said so in the plan**, and the
next rung is **fully priced in advance at `+7` with all prerequisites
discharged.**

> **A plan that prices its next rung EXACTLY is making a falsifiable claim, and
> the landing either confirms the instrument or corrects it.**

**Owed at that landing**: if it lands at **exactly +7**, it is recorded beside
ES's exact-to-the-unit prediction as **calibration evidence** (§9.0) — *an
instrument that has never predicted has never been tested*, and this lane will
then have predicted twice and hit twice. **If it lands elsewhere, that is the
more valuable row**, because a missed prediction with all prerequisites
discharged says something about the *pricing method* rather than about the work.

**AND A CENSUS CAN RETURN THAT A PLANNED RUNG DOES NOT EXIST AS A RUNG** (Go's
`fmt` census; §G25 building). **Every `fmt` entry point is variadic**, so:

> **`fmt` without variadics is not a rung at all** — the census **did not rank
> two options, it DISSOLVED one.**

> **The ordering isn't a choice.**

**A third thing a scheduling census can return**, beside *this is worth more* and
*this is already done*: **the candidate was never separable from its
prerequisite.** *A ranking presumes the items are alternatives, and the most
useful census result is sometimes that they are not.*

**AND AN ASSUMED BLOCKER MEASURED TO ZERO.** Variadics are worth **17× `fmt`'s
marginal** (**+52 vs +3**), and the surprise is inside the `fmt` number:
**38.9% of `fmt`'s selections are Fprint-family and add `+0`.**

> **`io.Writer` / interfaces **are not** the binding constraint — and I would
> have assumed they gated them.**

**Third confirmation that CALL-SITE FREQUENCY IS NOT REACH**, and the sharpest,
because **the assumed blocker was not merely over-weighted — it contributed
nothing.** *An assumption about what gates a construct is a claim about the
corpus, and it is exactly as checkable as the construct's count.* The §G25
advance prediction is called: **687 → 739 / 594 → 644.**

**AND A CENSUS CAN RETURN THAT THE WORK IS ALREADY DONE — the strongest form of
the could-have-overturned standard** (pyc inch 3, `3ea2f2a`, ticketed). The
third flagship surface **was already built**: every piece had landed **for a
different reason.**

> **The inch buys no capability; it converts a BELIEVED one into a MEASURED
> one. What was missing was EVIDENCE, not capability.**

> **A census may return "done" — and that answer is trustworthy only from a
> census that COULD HAVE RETURNED OTHERWISE.**

**Which this one could**: it **computed the capture arithmetic on the real
file** rather than checking a list of expected pieces. **A census that only
looks for what it expects cannot report completeness** — it can only report that
its expectations were met, and those two are the same sentence with different
truth conditions.

**And "no capability bought" is a result worth landing, not an embarrassment.**
The §9.0 discipline already separates **coverage** from **claims**; this is the
case where **the capability was real and the CLAIM was not**, and closing that
gap moves a number that had been resting on a belief. *A lane that reports a
zero-capability inch honestly has done the harder half of the work — the half
that is invisible in the tree.*

**AND THE SECOND INSTANCE STATED IT BEFORE THE WORK, which is the reading
becoming a habit** (Ada inch 2, citing Go's precedent by name). The inch moves
ACATS coverage by **exactly 0**, and **the plan says so**:

> **It must not be sold as a coverage rung.**

**A `+0` disclosed in the plan is a different artifact from a `+0` explained in
the retrospective.**

**AND ITS SIBLING, from the other end of a chain: THE LAST RUNG RE-PRICED IN
ADVANCE** (Wasm, `6bd3ca1`). The census found **O5 is not the six-line job O2
and O4 were** — roughly **118 lines of prerequisite that cannot be copied**,
because **no working Lean original exists**, ahead of a **183-line induction.**

> **The LAST RUNG IS THE TALL ONE, and the census says so IN ADVANCE rather than
> after.**

**Same control, opposite sign**: the `+0` discloses that a rung buys **less**
than its position suggests; this discloses that one **costs more**. Both are
statements a lane would rather make afterwards, and both are **worth nothing
afterwards** — a plan that ends *"and then the last one, similarly"* is the
sentence a chain document exists to prevent. **The tell that a chain has not
been censused is that its rungs are all the same size.**

 The first is a lane pricing its own inch honestly while it
still could have chosen a different one; the second is a lane accounting for a
number after the fact. **Both are correct and only the first is a control** —
and it is the cheapest possible one, because at plan time the sentence costs
nothing and afterwards it costs the appearance of progress.

**And the lane read its own `+0` correctly, which is the retracted law paying
off**: *"`+0` means not a rung on its own AT THIS VOCABULARY, not worthless."*
The mechanism is built, gated and correct; what it unlocks is downstream of a
different rung. **That is exactly the reading `2026-08-23-architecture-42`'s
retraction bought**, arriving one inch later in the lane that paid for it.

**AND THE SCHEDULING CONSEQUENCE, which is the part that outranks the number.**
The next rung is **multi-value returns — a WALKER rung** — reached from an
extractor rung.

> **The extractor/walker ALTERNATION is what the census SAYS TO DO, not a
> scheduling convention.**

**An alternation adopted as a convention would be a rhythm; one derived from a
census is a consequence**, and the difference shows the first time the census
says *do two walker rungs in a row.* A convention would resist that; a
consequence has nothing to resist with. **Never defend an alternation the census
did not produce.**

**(3) AND THE SAME ORDERING APPLIES TO OBLIGATIONS, NOT ONLY TO CONSTRUCTS —
SHARED PREREQUISITES FIRST** (Wasm, `f657041`). An obligation list's order is an
artifact of how it was written; the **census-ordered** path takes
`rt_sub_trans` + `rt_sub_app` **before O3**, because **O2 and O4 need the same
pair.**

> **Order the work by what is SHARED, not by what is NEXT. A prerequisite two
> obligations away is worth more than the obligation in front of you.**

This is the conjunctive law with the arrow reversed: there, several constructs
were worth little apart and much together; here **one lemma is worth little to
its own obligation and much to the three that follow.** Both are failures of
**per-item pricing**, and both are fixed by the same move — **price against the
set, and let the census say what the set is.**

**And the counterpart, which keeps the law from licensing bundles:** the family
is what the **census** says co-occurs, not what a lane finds tidy. **Fixed
arrays `[N]T` are 14.6% of `ArrayType` and are NOT in this family** — the rung
declares only what executes (§5.2's deferral hygiene: a declared-but-refusing
construct reads as coverage in every table that counts declarations).

### 9.1 BUG BEFORE REFACTOR

Fix the defects **today**, ahead of any consolidation, because they are
independent of it and cheap:

* **Three `--compare` implementations exit 0 on drift** —
  `c_construct_census`, `wasm_spec_census`, `wasm_suite_census`. A
  `--compare` that cannot exit nonzero cannot gate, cannot run under
  `set -e`, and cannot be the staleness detector §5.4 requires. **A drift
  guard that cannot fail is §5.4a's cleanest instance**: the instrument
  reads green because it cannot read anything else. Sharpest detail — the
  first of the three is the very instrument §5.4 cites as having *fixed*
  the contract.
* **Four copies of a 6-line `git_rev` that all swallow their failure** and
  stamp `null` provenance. Same law, same direction: silent, flattering.
* **AND THE REMEDY FOR A STUCK CHANNEL BECAME A NEW WAY TO BE STUCK** (pyc,
  same inch). `git rebase && echo …` puts the rebase **in an `&&` list, which
  EXEMPTS it from `set -e`** — so the guard added to catch unchecked failures
  **created a differently-unchecked failure.**

  > **`set -e` DOES NOT APPLY INSIDE `&&`. Run the command ALONE and read `$?`.**

  **This is the gate-versus-comment family's recursive case, and it is the one
  worth stating loudly**: *the fix for a silent failure is itself a candidate
  silent failure*, and it inherits none of the scrutiny the original defect
  earned — **because it arrives labelled as the fix.** *A repair to a control is
  a control, and gets the control's audit, not the repair's.*

  **POSTSCRIPT, and the reason this is worth a bullet rather than a footnote**:
  the rebase now **runs standalone with `$?` read separately** — *the recursive
  law's compliant form, landed in the same inch that found the defect.* **A
  control law with a worked compliant form is copied; one with only a
  prohibition is re-derived.**

Three one-line changes and one shared helper. **Not gated on the kit.**

### 9.2 CONSOLIDATION BY TOUCH, never big-bang

The rule for all of it: **a lane converts its own artifact the next time it
opens that artifact for any other reason, in the same landing** — no
deadline, no sweep, and the test is that the committed output is
**byte-identical before and after**.

| shared thing | what it replaces | adopted when |
| --- | --- | --- |
| `harness/censuskit.py` (~160 lines) | ~520 generic lines across **14** instruments; net ≈ −300 | a lane next touches its instrument |
| `tools/triad.sh` (landed) | 6 hand-rolled triad scripts, **38%** violation density | a lane's next build |
| `Core` loader utilities | 32 of 46 common lines across four tiers' loaders | a lane next touches its loader |

**WHERE TWO GENERATIONS OF A TRICK EXIST, PORT THE SUCCESSOR — and record
the PREDECESSOR as the thing it fixed.** Consolidation harvests from a
tier's history, and a history contains superseded mechanisms that still
look authoritative because they are still in the tree and still work.

The measured case: **`py_loop` derived its loop-test value by
Miller-pattern unification**, reading `tv`/`Cont`/`step` off goals
containing metavariables — and the lane honestly recorded *the two shapes
that destroy it*: a surviving `ite`, a destructured state, a full-simp-set
rewrite. **`py_vcgen` then REPLACED that mechanism** with symbolic
evaluation at the invariant shape. Both are in the tree. **A tier that
harvests the first inherits a known-fragile mechanism together with its
known failure modes**, and inherits them silently, because the predecessor
is not marked as superseded — it is merely older.

So the harvest rule is: **take the latest generation, and keep the earlier
one as documentation of the failure it fixed.** The predecessor is not
dead weight — it is the record of *why* the successor is shaped the way it
is, which is precisely what a harvesting tier needs and precisely what a
bare port drops.

**One naming caution that follows from the same archaeology**, because a
harvesting tier will meet it: **`VCGen.lean` is NOT "VC generation."** Its
own header is explicit — layers 1 and 2 (`VC.lean`, `VC2.lean`) specify
STATEMENTS; **`VCGen.lean` specifies SUSPENDED MACHINES**, what a
generator's frame stack still has to yield. That is why its predicates get
**re-defined over a new stepper** rather than replaced by a core word: they
are about suspension, not about verification conditions, and the name
suggests otherwise.

**Why on-touch and not a sweep**: a sweep is a spine-touch that invalidates
every lane's build at once, and the audit's own §9 records this lane taking
a two-minute unlocked Lean run while merely *exercising* the new script.
The migration must never cost more than the defect it removes.

### 9.3 SPAN NAMING — RATIFIED BY CONVERGENCE

**Three lanes independently chose `line / col / endLine / endCol`** (C,
Ada, ES). That agreement is **a measurement of what the neutral names are,
not a taste** — the same standard of evidence §3.6 applies to the SV tier
reinventing the `ρ` layer. The audit also corrects §3.7's count: **six**
span types across the lanes, not three.

`Core.Span` is renamed to those four fields on next touch, its docstring
loses *"Field names mirror CPython's `ast` attributes"* (a correction §3.7
ordered and which has not landed), C's `macroLine?`/`macroCol?` pair is the
named model for **extension**, and Ada's type then has nothing left in it.

### 9.4 VERDICT VOCABULARY — a CONFORMANCE gap, not a design question

§5.1's four names — `MATCH | REFUSE | DIVERGE | TIMEOUT` — plus §5.2's four
REFUSE causes and §5.3's `live` flag are **already law**. Three of seven
emitters have drifted from it; they conform **on next touch**, and
`DIVERGED` dies. `censuskit.row()` is where the law gets enforced instead
of remembered: it rejects an unknown verdict, requires a `cause` on
`REFUSE`, and carries `live` so a vacuous run cannot serialize as
agreement.

**A shared full ROW is REJECTED, and the reasons are the audit's own.** The
per-tier extensions are different *in kind* — Ada grades by membership in
ACATS marking classes, ES's pass condition is *not throwing* over 4 248
negative tests, C carries `outside_vocab`, and §5.1's membership ruling
makes the permitted set *a per-site datum the tier carries*. Flattening
those into one schema is exactly the thick-trunk mistake §2.4 forbids.
**Vocabulary shared, row per tier.** The `MISMATCH`/`PASS`/`FAIL` emitters
predate the law, so their conversion carries a whitelist-semantics decision
that belongs to the Python lane and is **not** taken here.

### 9.5 BACKLOG V2 — per-lane files

`docs/backlog.md` is one file that **collides with itself**: `L2`, `L3` and
`L4` each appear **twice**, and at ~66 landings a day every lane appends to
the same tail. New scheme: **`docs/backlog/<lane>.md`**, appended only by
its own lane, with ids `YYYY-MM-DD-<lane>-<n>` that need **no reservation**
because the lane name makes them unique; `docs/backlog.md` becomes a
**generated index**, which is §5.5's "generated and checked, never
hand-maintained" applied to the repository's own record.

**AND THE HEADING GUARD OVER THESE FILES NEEDED A MIGRATION VOCABULARY, which
is what makes `--strict` adoptable at all** (QoL `22ed755`; measured **18
undated, 8 malformed, across 7 files**). The discriminator is one sentence:

> **AN ID IS ONE TOKEN.**

`G1 — t` yields the id `G1`: **a real entry under an older scheme** — it warns,
it never fails. `INBOUND FROM THE SOFTFLOAT LANE — …` yields the id `INBOUND`,
**five tokens where one belongs**: junk, and what `--strict` fails on.

> **A MIGRATION-TOLERANT GATE DISTINGUISHES OLD-VALID FROM NEVER-VALID, or
> `--strict` can never be adopted.**

**AND THE CENSUS MOVED — 7 MALFORMED, NOT 6 — AND THE COMPOSITION CHANGED,
WHICH IS THE MORE USEFUL FACT** (re-measured here). One of the seven **is not an
entry at all**: `docs/backlog/go.md:11` is `## SPEC COVERAGE — the completion
metric`, **a standing section header** carrying §9.0's own required number. The
other six are INBOUND entries.

> **TWO REMEDIES FOR ONE SYMPTOM, DISTINGUISHED BY WHAT THE HEADING *IS*.** An
> **entry** missing an id gets **an id**. A **section header** gets **demoted to
> `###`** — **never an invented id**, because that would put it in the index
> **as an entry that does not exist.**

**The unit family at the heading level.** The guard reports a **syntactic**
class — *does this `##` parse as `<id> — <title>`* — and **two semantic kinds
sit inside it.** Giving the section header an id would **satisfy the guard and
corrupt the index**, which is every member of this family's shape: *the check
was right; the unit underneath it was two things.*

**And it is why the guard WARNS rather than auto-fixing.** A gate that repaired
its own findings would have written an id onto that header — **the flattering
repair, applied to the one case the gate cannot classify.**

> **A guard that can NAME a defect it cannot CLASSIFY must hand it to someone
> who can.**



**Without that distinction a strict mode is unshippable**, and the reason is
arithmetic rather than taste: a gate that treats every pre-scheme heading as
junk fails on **history**, so it can only be turned on after a tree-wide
rewrite — which is the big-bang §9.2 forbids. **With it, the strict mode's
failure set is exactly the set somebody can fix today**, and history warns
without blocking.

**And the guard was EXTENDED, not duplicated** — undated headings already sorted
last and were being counted **inside the generated file, where the lane that
wrote the heading never looks.** *A count that lands only in an artifact its
subject does not read is a count nobody acts on*, which is §9.5a's own reason
for rendering INBOUND against each owning lane. **Two of the eight were the
tools lane's own and are conformed; the other six belong to lanes that own their
files (§9.5), so `--strict` is not wired into CI yet** — a gate held at
`declared` (§5.4b) on purpose, with the reason recorded rather than the
adoption forced.



**AND A TENURE NAMES ITS BUILD LOG, GREEN OR RED.** `tools/triad.sh` writes
the build to a `mktemp` file and **never deletes it** — there is no `rm` of it
anywhere in the script. What a green tenure lost was not the file but the
**path**, and that is enough: measured 2026-08-23, **56 `triad-build.*` files
coexist in one `TMPDIR`**, from many lanes and many runs.

> **Recover a build log by the PATH the tenure printed; failing that, by
> CONTENT — never by clock.** With 56 of them sharing a directory the newest is
> very likely another lane's. **And the tenure window is not a safe fallback
> either**: measured by the R-track lane, **three `triad-build.*` files landed
> within ninety seconds of one tenure's end** — other lanes' gate-phase builds —
> and the file whose mtime matched was a **gate-phase completion, not that
> tenure's last line**. The reliable key is content: `grep -l` for a symbol only
> that build could have printed (its own theorem name) found **exactly one**
> file.

The green line carries that caveat with it, because the advice is only needed
by a reader who no longer has the line.

**AND THE GENERATED INDEX CONFIGURES ITS OWN MERGE DRIVER.** `INDEX.md` is
generated *and committed*, so it conflicts on every lane's rebase — measured at
**two conflicts in one day for one lane**, and every lane pays it. A driver is
declared in `.gitattributes`, but git ships no `ours`-style driver and **config
is per-clone**, so nobody had one. `tools/triad.sh` and `tools/check.sh` now
call `tools/backlog-index.sh --ensure-driver` on their first run in a clone:
one line when they configure it, silence afterwards. **A fix that needs a human
to type it is not a fix.**

**Migration is append-only and rewrites no history**: the current file is
renamed to an archive, every existing `§Lnn` reference keeps resolving, and
**new landings use per-lane files from that commit on.** It also retires the
race §7.2's push-time re-read rule exists to survive.

#### 9.5a THE INBOUND CONVENTION — filing into a lane that is not yours

Per-lane files answer *"where do I append?"* only while every entry has an
obvious owner. One lane filing a finding into **another lane's** file needs
a convention, or it mints ids in a sequence it does not own:

* the heading is
  **`## <sender-id> — INBOUND FROM THE <X> LANE: <what the owner should do>`** —
  the **id comes FIRST**, as §9.5's id law requires, and **`INBOUND` is a TITLE
  PREFIX, never the id**;
* it carries a **SENDER-namespace id** — `YYYY-MM-DD-<sender>-<n>` — so
  **nothing is minted in the owner's sequence**;
* it tells the owner explicitly to **renumber it or close it**; the entry
  is a *proposal to the owner's record*, not a fact already in it;
* the **generated index renders `INBOUND` as its own class, derived from the
  TITLE PREFIX**, listed against each owning lane, so an owner sees what is
  queued for them without reading their own file for surprises;
* **MIGRATION — entries in the ORIGINAL spelling are OLD-VALID**: the index
  still classes them by their id token and **the guard warns without failing**,
  until the owning lane re-spells them.

**THE BULLETS ABOVE ARE THE RESOLVED SHAPE. HOW THEY GOT THERE IS THE PART WORTH
KEEPING — this convention was IN TENSION WITH §9.5's ID LAW, found by the guard
the same day the law landed, and one of the seven offenders was THIS LANE'S.**
`tools/backlog-index.sh` wants `## <id> — <title>`; §9.5a's heading starts with
the word `INBOUND`, so the generator **invents `INBOUND` as the id** — which is
precisely the *five tokens where one belongs* case that *an id is one token*
(§9.5) calls junk.

**The two rules are both load-bearing and they genuinely conflict**: the index's
INBOUND *class* is derived from that first token, so the convention is what makes
the rendering work, and the id law is what makes `--strict` adoptable. **Neither
can simply give way**, and the resolution is a generator question rather than a
prose one:

> **Recommended: the ID goes FIRST and `INBOUND` moves into the TITLE, with the
> generator classing on the title prefix rather than on the id token.** Both
> laws then hold, and the class survives.

**Routed to the tools lane, not taken unilaterally**, because the generator is
theirs and re-spelling six other lanes' headings to match a shape I chose would
be exactly the cross-lane edit §9.5a exists to prevent.

**AND IT LANDED — the generator now classes on the title prefix and accepts the
original spelling as old-valid** (QoL, merged; `tools/backlog-index.sh` classes
from the title at its `INBOUND` test and warns on the old form without failing).
**The bullets above are amended to match, and that amendment is THIS lane's to
make**: the generator moving is a tense fix; **the convention's CONTENT changing
is a claim change**, which the reconciliation ruling below assigns to the owner.

**AND THE MIGRATION CLAUSE'S JUSTIFICATION IS THE REGISTER-GRADE PART**, because
it is argued from the charter's own authority rather than from convenience:

> **A shape the rules once REQUIRED cannot become a failure the day a new rule
> lands.**

**§9.5a mandated the original spelling**, so **a guard punishing obedience would
be the tool contradicting the law** — and the lanes holding those headings did
exactly what this document told them to. *Old-valid is not leniency; it is the
only disposition consistent with having given the instruction.*

**AND THE PROTOCOL'S SUCCESS CASE, recorded because the failure cases have had
all the attention** (SV, `d20b16d`). An INBOUND was **answered at triage by
INDEPENDENT RE-MEASUREMENT**: SV re-measured its own tier — **zero `Float`, zero
`shortreal`, every `real` is prose** — so **the sender's estimate row comes
off**, and the true need turned out to be **the divider spec layer only.**

> **THE RECIPIENT'S MEASUREMENT, NOT THE SENDER'S, CLOSES THE ROW.**

**This is what the sender-namespace rule is FOR**, and it is easy to lose sight
of while arguing about heading syntax: the INBOUND entry is *a proposal to the
owner's record*, and **the owner's job is not to triage the proposal's
plausibility but to measure the thing it is about.** A sender's estimate is a
**reason to look**, never a finding in the owner's file — and here the look
**changed the answer**, which is the outcome the convention exists to make
routine.

**AND THE ENFORCING LANE CAUGHT ITSELF VIOLATING THE ADJACENT RULE WHILE
CONFORMING TO THIS ONE.** Re-spelling the headings, QoL **minted
`2026-08-23-qol-inbound-1/2` for entries THIS LANE had sent** — ids in the
**owner's** namespace for a **sender's** entry, which is the exact thing the
sender-namespace bullet exists to prevent. **Re-spelled to
`2026-08-23-architecture-27/28`, with the correction recorded in place**, and
those two entries are now **the in-tree exemplar of the resolved shape.**

> **Conforming to one rule is when you are most likely to break its neighbour** —
> attention is on the shape being fixed, and the adjacent constraint is
> satisfied by habit rather than by check.

**Same family as the heading guard convicting §9.5a itself**: the instrument
enforcing a rule met the rule's own author, and here **the lane enforcing a rule
met its own violation of the rule beside it.** Both were caught **because
something mechanical was pointed at the work** — and in both cases the
mechanical thing was aimed at a *different* rule than the one it convicted.

**Recorded rather than quietly fixed, because the shape is the useful part: a
convention in a charter can be a defect in a tool.** §9.5a was written for
readers and the generator reads it too; **a rule about how humans write headings
became an input to a program, and nobody re-checked it against the program's
grammar.**

**AND THE RECONCILIATION REGIME IS RULED, because the ownership norm does not
settle it by itself** (asked by the tools lane after it reconciled this
document's stamp paragraphs at a merge; ratified here). The question: when a
finding and its fix land from **different lanes in the same window**, does the
fixing lane **reconcile the register at the merge**, or is reconciliation
**INBOUND** to the owning lane like everything else?

> **RULING — IT SPLITS, AND THE TEST IS ONE QUESTION: does the edit change what
> the document CLAIMS, or only WHEN it claims it?**

* **TENSE AND STATUS — reconcile AT THE MERGE, by the lane that landed the
  fix.** *"The stamp IS `git write-tree`"* becomes false the moment the fix
  lands, and **the fixing lane is the only party who knows that.** An INBOUND
  would leave the charter **false for the length of a round-trip**, and
  model-matches-code makes divergence a **blocker**, not a queue item.
* **REASONING, LAWS, DATED ENTRIES — INBOUND, always.** A lane reconciling a
  status may **not** restate a law, re-scope a finding, or delete an analysis on
  the way past, and dated entries stay under the annotation norm untouched.

**Two conditions make the first half safe, and the tools lane met both**:
**preserve the reasoning intact** — the analysis is the register's value and
none of it was wrong — and **say in the landing exactly what changed and why.**

**AND THE OWNER STILL AUDITS, which is the half that cannot be delegated.** The
first exercise of this ruling produced a **correct, well-reasoned reconciliation
that also left the section saying the same thing twice**: the fixing lane added
a `RESOLVED` paragraph while this lane's own *"the fix has landed"* paragraph
already stood forty lines below. **Neither edit was wrong — the duplication
existed only in the UNION**, which is exactly what an owner's read catches and a
merge cannot. Consolidated on the way through.

> **Reconciliation-by-edit is right for TENSE and owes an owner's pass for
> COHERENCE. The merge fixes what is FALSE; only the owner sees what is now
> REDUNDANT.**

**AND THE RULE HAS NOW BEEN TESTED AGAINST A DISPATCH, WHICH IS THE CASE THAT
DECIDES WHETHER IT IS A RULE.** A coordinator dispatch instructed this lane to
**annotate another lane's dated entry directly**. It was declined on the
strength of the norm — *a dated record in another lane's document is NAMED,
never corrected in passing* — the finding was landed here, and the annotation
was filed to the owner as `INBOUND`. **The coordinator confirmed the deviation
and recorded the dispatch as the error.**

> **THERE IS NO STANDING EXCEPTION. Another lane's dated record is annotated by
> THAT LANE, from your INBOUND — never by you in passing, and not on
> instruction.**

**Why the confirmation is worth a paragraph rather than a footnote**: an
instruction is the one pressure this norm cannot survive by itself. Every other
temptation to edit across lane lines is a convenience — this one arrives with
authority attached, and *"I was told to"* is exactly the reasoning that would
make the norm advisory. **A landed law is not overridden by a dispatch; a
dispatch that conflicts with one is a finding about the dispatch**, and the
cheap move when they conflict is to land the finding, file the residue, and say
which rule you followed.

**AND THE MEASURED COST, which is the part worth flagging: cross-lane
appends REINTRODUCE the tail race §9.5 just retired.** `es.md` conflicted
on rebase because the owner appended to it concurrently — exactly the
contention per-lane files exist to remove, arriving through the one door
they left open.

**Contingency, and it is a WATCH ITEM rather than a change**: if the race
recurs, INBOUND entries move to **`docs/backlog/inbound/<owner>.md`** — a
file the owner reads and drains but never appends to, which restores the
single-writer property. Not done now, because one conflict is an incident
and not yet a rate; §9.7's light tick is where it would show up as one.

**THE WATCH ITEM HAS FIRED — SECOND OCCURRENCE, 2026-08-23, AND IT LANDED
WORSE THAN THE FIRST.** This lane filed an INBOUND entry into
`docs/backlog/qol.md` in the same window the owner appended `qol-36`. The
first occurrence (`es.md`) was a **rebase conflict**: loud, blocking,
resolved. This one was resolved **wrongly and committed** — `47544f1` shipped
`docs/backlog/qol.md` with **`<<<<<<< HEAD` / `=======` / `>>>>>>> cc3d9ec`
markers in the file**, swallowing neither entry but publishing both inside a
conflict. Fixed here, keeping both halves in order (`qol-36`, then the
INBOUND block); the escalation is recorded rather than the fix alone, because
**the rate is not what changed — the FAILURE MODE is.**

> **A race that conflicts is a nuisance. A race that MERGES WRONG AND COMMITS
> is a defect, and the second is what a rate buys you.**

**AND EVERY GATE WAS GREEN OVER A FILE CONTAINING CONFLICT MARKERS**, which is
§5.4b measured on this repository's own documents: `docs_check` gates *marked
code blocks*, `backlog-index.sh` gates the *index's freshness*, and neither is
pointed at *"is this markdown structurally intact"*. A one-line grep for
`^<<<<<<<`, `^=======$`, `^>>>>>>> ` over `docs/**` is the missing pointer, and
it belongs in `tools/ci.sh` — filed as residue, not landed here (this lane
writes documents, not gates).

**THE MOVE ITSELF HAS A PRECONDITION THE CONTINGENCY ABOVE DOES NOT STATE, and
landing it without the precondition would be a silent-absence defect.**
`tools/backlog-index.sh` globs **`docs/backlog/*.md`, one level deep** — so
INBOUND entries moved to `docs/backlog/inbound/<owner>.md` would **vanish from
the generated index**, defeating the exact property the convention exists for
(*"an owner sees what is queued for them"*). So:

> **The move is CONDITIONAL on the generator learning the subdirectory. Until
> the glob is fixed, moving the files makes the queue invisible — a worse
> failure than the race it retires.**

Until then, the convention stands as written, with one tightening that costs
nothing and would have prevented this instance: **an INBOUND append is a
separate commit, made immediately, never batched behind other work** — the
window is the whole hazard, and it is the only part of it a filer controls.

#### 9.5b THE ROUTING LAW — file the RESIDUE, not the REPORT

> **CHECK WHAT THE OWNER ALREADY LANDED, AND FILE THE RESIDUE, NOT THE
> REPORT.**

Measured: an ES entry arrived **90% redundant**, because the ES lane had
already **accepted, re-measured and sharpened** both findings before the
report was written. **The residue — the `ToInt32` clamp — was the only
thing worth filing**, and it was the part the report buried under the
nine-tenths the owner already had.

This is the retrieval laws' third face (§5.4a). *A grep that agrees with
your prior is the one to re-run* is about searching; *count the pattern
position* is about pricing; **this is about FILING — a report sent without
checking what landed is a duplicate its sender cannot see**, and it costs
the owner the read.

The practical form is the same in all three: **look at the thing itself
before reporting about it.** For a cross-lane finding that means reading
the owner's file first and filing only what is not already in it — which
also makes the INBOUND entry short enough to be cheap to renumber.

### 9.6 WORKSPACE

* **NOW — amendment 13 CoW seeding** (§7.1a). 27 s and 29 MB per clone
  against GB-scale downloads; no protocol change, no new risk. The
  `workspace.sh check` piece is worth having first: ~20 lines, no network,
  and it flags two lanes' branch trap today.
* **NEXT — a shared `.lake/packages`**, pending **one ticketed
  confirmation** of Lake's behaviour with a shared packages directory.
  Amendment 11 already makes Lean execution single-tenant, which is what
  makes this safe to try.
* **REJECTED for now — a shared build workspace.** It buys ~0.43 GB a lane
  and costs torn-tree adjacency, edit-latency coupling, and **spine-touch
  invalidation** — measured at **8 spine moves in 60 commits**. Revisit
  only if `.lake/build` passes ~2 GB per lane, the number at which the
  arithmetic changes.

### 9.7 THE AUDIT CADENCE ITSELF

* **LIGHT — every keeper tick**: the three live checks (lock owner, queue,
  concurrent `lake build` by parentage). The audit found the build lock
  being violated by two lanes for 48 minutes *while it was being written*,
  so this is the check that pays.
**THE FIRST RE-MEASUREMENT HAS LANDED, and the cadence is what produced
it.** Amendment 9's FIFO ticket queue was adopted on the strength of a
failure — the C lane losing five consecutive handoffs while queued first,
and a 43-minute wait under bare spinning. Re-measured by the ES lane, **the
same lane under the same contention acquired the lock in 58 SECONDS**:
roughly a **45× improvement**, and the starvation mode is gone rather than
merely shortened.

That is the point of §9.7 rather than a footnote to it: an amendment
adopted from an incident is a hypothesis until someone re-runs it under the
same conditions. **This is the first strategy item to complete that loop**,
and it is the template for the rest — the exit-code fixes and the 38%
violation density are next, and they are owed the same treatment.

**THE AUDIT HAS AN INSTRUMENT NOW: `tools/laws.sh`.** The cadence above had
been walking the laws by hand, which is the shape §5.4 exists to retire. It
reads `docs/law-index.md`, this section's amendment register and §7's tools
list, and reports for every law the tool that cites its durable home — or
**`NO GATE`**. It then sorts the NO GATE list by **how many lane ledgers cite
the law**, so the next enforcement inch is chosen by **measured demand**
rather than by whoever remembers a rule at the time. First run, 2026-08-23:
**332 laws, 206 cited by a tool, 126 with no gate at all.**

**CORRECTED 2026-08-23, and the correction changed the DISPATCH, not the
headline.** Attribution matched tokens by substring, so **`§9` matched `§9.5`,
`§9.7` and `§9.2`** — one law homed at §9 was credited to seven tools,
including `ada_round_trip.py`. That is the identifier law failing inside the
instrument that measures enforcement. Tokens now match whole, with a boundary.
The headline barely moved (**216 → 215 cited, 116 NO GATE**) because the false
credits and two newly-attributed laws nearly cancelled — but **the demand
ranking moved completely**: §9.2 led at 14 citations and now does not appear
in the top six, because most of that 14 was `§9.x` mentions. **§2.4 is the
head, with seven ungated laws at 8 citations each.**

Two further mechanisms landed with it. A law whose home names a script is
attributed **by identity**, so a law implemented before it was indexed can
say so (`— gate: tools/triad.sh`); and a law the index marks
**`ungateable: <reason>`** is reported in its own bucket rather than as debt,
because re-surfacing a settled finding every audit is how it gets
re-litigated. `PROOF-40` is the first.

**A THIRD CLAUSE, MINTED WITHIN AN HOUR OF ITS OWN CAUSE: A FIXTURE IS NOT
ENFORCEMENT.** Adding a `laws.sh` self-test row that *named* A15 made `laws.sh`
credit **itself** as A15's gate — the instrument counting its own test data as
enforcement. The self-test region is now **stripped before any attribution
grep**, with rows in both directions.

> **An instrument must not read its own fixtures as evidence. Test data
> mentions a law; it does not enforce one.**

That is the self-selection law (§5.4) in the attribution direction: a tool that
searches for text will find the text it contains, and the copy it is most
likely to contain is the one it was built to recognize.

**AND A BUDGET WITH AN HONEST PARTIAL VERDICT.** `--budget` (default 120 s,
progress every 50 laws) stops the run and declares **every count a FLOOR**
rather than reporting a number that happens to be what fit in the time. The
verdict is written to a **file** rather than a variable, for the same reason
`triad.sh`'s watchdog publishes its pid: a subshell's variable does not survive
the subshell, and a verdict that cannot escape its own scope is not a verdict.

Two honesty clauses that make the number usable. **Citation over-credits** — a
tool that mentions a law in a comment is counted — so the NO GATE list is a
**LOWER BOUND on the unenforced set, never a coverage figure.** And **the unit
the count ranks is the HOME, not the law**: laws sharing a `§` share every
token and therefore tie, which is information rather than noise — it says the
*section* is what the ledgers keep reaching for. The report prints both views.

**THE FIRST FULL AUDIT HAS RUN, and its artifact is
`docs/quality-audit-2026-08-23.md` — 56 confirmed / 8 refuted, grouped by
owner, every lane dispatched.** §9.7 described a cadence; this is its first
completed instance, and the aggregate says something about the law
families themselves.

**THE CONFIRMED SET CLUSTERS EXACTLY ON THE SIX MINTED FAMILIES.** Of the
11 HIGH findings: **3 provenance, 4 identifier-in-instruments, 1 absence,
1 vacuous-guard, 2 docdrift.** Not one high finding landed outside a
family this document had already minted.

> **The laws predicted where the defects are.**

**AND THE PROSPECTIVE INSTANCE HAS NOW LANDED, WHICH IS STRICTLY STRONGER**
(Go, `da9a7bc` → `fef0b79`, both on master). The sentence above is
**retrospective**: the families located defects that already existed. This one
ran forward:

* **§G8 wrote the warning in advance** — *"pricing it as reach would be the
  motivated error"*;
* **§G20 then priced `SelectorExpr` as reach**: **+1 189**, 23× the next
  construct;
* **§G21's census caught it before a line was built** — split the way
  `ArrayType` was split (`pkg.F` needs only the import list; `x.f`/`x.M` needs
  types), then measured as **executable** reach with `cmd/` and `unsafe`/C
  excluded: **+203 files, not +503. Overstated 2.5×.**

> **A LAW MINTED FROM ONE LANE'S ERROR CAUGHT THE SAME LANE'S FUTURE ERROR,
> BEFORE IT WAS PAID FOR.**

**That is the strongest evidence the register can produce, and it is a
different kind of evidence from the audit's.** The audit showed the families
were **descriptive** — they named defects that were already in the tree. This
shows one is **predictive**: it was written as a warning about a mistake nobody
had made yet, the lane made it anyway, and **the warning's own instrument was
what stopped it.** A taxonomy cannot do that; only a measured law can.

**And the honest reading of the outcome matters as much as the catch.** The
correction did **not** kill the tier — **+203 on a 587 baseline is still +35%
and still the largest move available**, so the authorization stands and the
tier is **sized on 203**. *A law that catches an overstatement is not a law that
cancels the work; it is a law that prices it.*


That is the strongest available evidence that the minting has been
measurement and not taxonomy: a family invented to describe one incident
would not go on to locate eleven more across seven lanes. It also sets the
cadence's most useful parameter:

> **The LENS LIST for the next audit = the law families minted since the
> last one.**

An audit with no lens list re-reads everything shallowly; an audit aimed
through the families finds the class of defect those families exist to
name. And a family that finds **nothing** on a sweep is itself a result —
either the discipline took, or the lens is wrong.

* **ON EVERY GATE THAT GOES UNCONDITIONAL — re-read the owning lane's
  DORMANCY RECORDS.** A deferral that was correctly filed and genuinely
  harmless stays harmless only while nothing checks it; arming a gate
  **re-prices every wart the artifact is carrying** (§5.4b, the pyslang
  instance). This is a **trigger**, not a tick: it fires on a change of gate
  state, and the thing it reads is the lane's own record of what it knowingly
  left undone.
* **FULL — about every 10 landings**, and the next full audit **re-measures
  its own headline numbers**: the **38%** violation density, and whether
  the three `--compare` exit codes and four `git_rev` stamps are actually
  fixed. An audit that does not re-measure what it reported is prose again.

**CLOSING A ROW WITHOUT A CODE CHANGE — two legitimate closures, and the
condition that makes them legitimate.** An audit creates pressure to answer
every row with a diff, and two of the QoL lane's rows were answered correctly
with none (`a9f7867`):

* **VERIFIED-ALREADY-FIXED** — `triad.sh:497` had been fixed by `4c710e3`, and
  the closure was earned by **re-running the row's own example** rather than by
  reading the diff that supposedly covered it;
* **WOULD-BE-VACUOUS** — the row asked for `a6-guard` to be wired into
  `triad.sh`, and **`triad.sh` never rewrites the tree**, so the guard there
  could never fire.

> **A check that cannot fire is the audit's own VACUOUS category.**

**And its MIRROR is in §5.4b** — *a guard that ALWAYS fires is exactly as
useless as one that never can* — measured by a lane on its own guards. The pair
is one rule: **a gate is a channel, and a channel stuck at either value is
off.**

That is §5.3's ruling — *a check must not report sameness where there was no
content* — arriving at gates instead of at verdicts, and this document had
already made the same move once without naming it: **STMT-61 is reported as a
column (`7/0`) rather than built as a comparison that cannot fire** (§2.4).
Wiring the guard would have raised the **gate count** without raising
**coverage**, which is MEAS-9's *a gate that is a permanent SKIP is a check
pretending* — and, in §5.4b's vocabulary, a gate with no claim at the other
end of its pointer.

**THE CONDITION, and it is the whole of the norm: THE REASON IS WRITTEN WHERE
THE ROW IS.** Both closures went into `docs/quality-audit-2026-08-23.md`
itself, not only into the lane's ledger. A row closed in the lane's ledger
alone is **invisible to the next sweep**, which re-files it — and a re-filed
row that was already settled costs twice: once to re-investigate, and again in
the credibility of every other row beside it.

> **A no-code closure is CLOSED when the audit FILE carries the reason.
> Anywhere else, it is a lane's private opinion of a public row.**

**A THIRD LEGITIMATE CLOSURE, from the pyc lane's triage (staged on its queued
ticket): THE REQUESTED FIX IS NOT THE DURABLE ONE.** A row asked for stale
line-number citations to be re-numbered. Declined, with the reason recorded:
**fixing offsets buys one landing of accuracy** — the next insertion above them
rots them again — and the durable remedy is **lemma names** (§5.4).

> **A row is closed when the CLAIM is true, not when the requested edit has
> been made. An audit prescribes a remedy; the owner may substitute a better
> one, and must SAY WHICH.**

The must-say is the whole safeguard: a substituted remedy that is not named
reads, one audit later, exactly like a row nobody acted on. Note that this
closure and the vacuous one point in **opposite** directions — one refuses to do
too little, the other refuses to do something useless — and both are available
only to an owner who **verified the row first** (§5.4a).

**A FOURTH KIND — INAPPLICABLE, NOT OPTIONAL: THE REQUESTED ARTIFACT HAS NO
SUBJECT** (pyc's 3c-i-c; **ticketed — conditional on that landing**). A
transition theorem was owed for a construct the trunk **refuses to step**, and
**a refusal has neither `GenSteps` nor `GenSilent`** — so there is nothing for
the theorem to quantify over.

> **The theorem is not WAIVED; it has NO SUBJECT.**

**The vocabulary is the whole point, and it is why this is a fourth kind rather
than a variant of the vacuous one.** *Optional* is a judgement about **priority**
and invites a later reader to reinstate it; *inapplicable* is a statement about
**the tree**, and it comes with the condition that would change it — **the day
the trunk steps that construct, the subject exists and the obligation is
live.** A closure that records *"not needed"* loses that trigger; one that
records *"no subject, and here is what creates one"* keeps it.

**The distinction from WOULD-BE-VACUOUS is worth stating**, since both end in
*"do not write it"*: a vacuous check **has a subject and cannot fail**; an
inapplicable one **has no subject at all.** The first is a design error the lane
could commit; the second is a fact about where the tier currently stands.

**AND A DISPOSITION IS A DEBT TOO — the gate gap that let a finding survive two
green landings** (SV, `d20b16d`). An audit disposition recorded **"ACCEPTED,
rewording"** and **the rewording was never applied.** It survived **two green
landings**, because:

> **Recording an ACCEPTANCE is not making the CHANGE, and nothing gates prose
> against its own audit disposition.**

**The three no-code closures above are honest ways to close a row WITHOUT a
diff. This is the fourth state and it is not a closure at all**: a row closed
*with* a promised diff that never arrived. **It reads as the strongest
disposition** — the lane agreed, no argument, no won't-fix — **and it is the
only one with nothing downstream to check it.**

> **A DISPOSITION WITHOUT ITS APPLIED DIFF IS AGED LIKE A DIVERGENCE ROW**
> (§5.0a): registered, aged, and gated — never assumed discharged because it was
> agreed.

**And that is the general shape worth carrying past audits**: *agreement is the
cheapest thing a lane can produce*, so any process that accepts agreement as
completion has made its most persuasive signal its least verified one. **The
gate is not "did you agree" but "does the tree differ".**

**And the audit records what it got wrong**, which is the practice worth
copying more than any item above: it ran Lean outside the lock while
exercising its own new script, and wrote that down — *the refusal path that
is only designed is not one, and the incident that is only regretted is not
measured.*

**AND ITS DUAL, minted by the ES lane from two of its OWN retracted
claims.** The law above covers one direction: a path you never walked is
not evidence. The dual covers **negative claims**:

> **AN OBSTRUCTION THAT IS ONLY ENCOUNTERED IS NOT MEASURED EITHER.**

Two retracted claims, both drawn from a single attempt:

* *"`rfl` failed, so no kernel-reducible substitute exists"* — a failed
  attempt, generalized to a non-existence claim;
* *"`#guard` passed, so the kernel accepted it"* — a passing attempt,
  generalized to a claim about a different oracle entirely (§5.4).

**Neither was measured against an ALTERNATIVE**, and that is the whole
defect. The SoftFloat lane got both right by **replicating the function
with core-only imports and DIFFING THE TACTICS** — running the candidates
side by side rather than reporting the first outcome.

**Practical form:** before writing *"no X exists"* or *"X is unprovable"*,
**try the nearest alternative formulation and record the tactic diff.** A
negative needs a measurement too, and the measurement is a comparison, not
an attempt.

**AND THE WORKED INSTANCE, one seam later: §G8 → §G10** (Go, `6a73111`, on
master; **this document first cited it as `§G9` — the clearing entry is `§G10`,
per the lane's own ladder table**). §G8 recorded three lemmas as **unprovable** — and did the one thing
that made the entry useful: it **named the cause exactly**, that
`lookupLocal name w` is **not definitionally** the match on `w.locals.find?`.
With the opening lemma landed, each of the three is **four lines**
(`lookupLocal_ok`, `loadAddr_ok`, `storeLocal_ok`; `propext` alone).

> **A NAMED BLOCKER IS A NEXT STEP; AN UNNAMED ONE IS A WALL.** *"Unprovable"*
> retires a line of work. *"Unprovable BECAUSE these two terms are not
> definitionally equal"* is a specification of the lemma that would fix it.

**And the honest half of the same entry is the model for how to leave a
blocker.** The seam does **not** settle the induction — it still needs the
for-loop's `ite` congruence and the fuel recursion — and the lane says so, with
the distinction that matters: **the debt is smaller and its next step is
MECHANICAL rather than OPEN-ENDED.** That is what discharging a blocker looks
like when it does not finish the job, and it is a reportable state rather than
a hedge: *the same size of debt, differently shaped, is progress and should be
recorded as such.*

**AND THE LADDER IS NOW COMPLETE, which turns the norm from an anecdote into a
measurable one** (Go, `cd14591`; the lane keeps the table itself):

| rung | the blocker, as NAMED | what it cost to clear |
| --- | --- | --- |
| **§G8** | the monad stack does not reduce at all | **a lemma SET** |
| **§G10** | — cleared by `Obs.lean`'s seam | **10 rows** |
| **§G11** | a dependent-match discriminant will not rewrite | **ONE congruence** |
| **§G12** | — cleared by `run_bind_ok` and friends | **3 rows**, `propext` alone |

ending in **a proved loop**. Read the right-hand column downward: **a lemma set,
then ten rows, then one congruence, then three rows.**

> **A WELL-NAMED BLOCKER NARROWS EACH TIME IT IS RE-STATED. If the next
> statement of the blocker is no smaller than the last, the naming was wrong —
> the lane has re-described the wall rather than located it.**

That is the norm's **test**, and it is what a lane can check without waiting for
the proof: not *"did we make progress?"* but *"is the blocker's next form
narrower than its last?"* A blocker that keeps arriving at the same width is a
symptom being renamed. **And the arc's shape is the argument for naming
blockers at all** — nothing here was a breakthrough; each rung was ordinary work
made possible by the previous rung stating exactly what was missing.

This document's `#guard` probe (§5.4) happens to have the prescribed shape
— `#guard`, `rfl` and `decide` on the *same* propositions — which is why it
could support a claim about the difference between them. Had it run only
the failing half, it would have produced exactly the retracted claim above.

---

## 10 WHAT THIS DOCUMENT DOES NOT DECIDE

* **Whether any of the three new spec tiers is founded, or in what
  order.** The registry rows are PROPOSED and §4.3's observation that
  WebAssembly is the family's best calibration case is an argument, not a
  schedule.
* **WHEN the adequacy milestone starts, and how fast erosion runs.** §3.4
  clause (c) and §8.5 fix the policy — migration by erosion, gated on
  `bound_refines_fuelModel` — but the schedule, and how much old work ever
  transports across the bridge, are the Python lane's on that day's
  numbers.
* **Whether `Run` moves at C's M2 inch 4 or the inch slips.** The trigger
  is fixed (§3.8); the inch is the C lane's.
* **The C lane's three stale citations** (§2.5). Found here, fixed there.
* **`VerilogA.Span`'s rename** (§3.7) — when that lane is next open.
* **`extractors/sv/census.py`'s move** into `harness/` (§1.6) — likewise.
* **SoftFloat's layer-2 build.** §3.5 states the design, corrects the
  premise by measurement and prices the order; the commissioned build
  lane's census is the evidence, and its first step is a corpus census,
  not Lean.
* **Whether any tier's ORACLE declares Annex F.** Unchanged, and still a
  named Thomas-decision. §3.5 answers the Lean-side half only.

---

## 11 WHAT LANDED WITH THIS CHARTER

* **`docs/family-architecture.md`** — this document.
* **`harness/c_clause_delta.py`** — the C17→C23 clause instrument (§2.1).
  Matches on the ancestor-title path because C23 renumbered 6.5, 6.8 and
  5.1.2 wholesale; rescues parent-retitled clauses by title; flags
  heading-only rows `thin` and excludes them from ratio statistics;
  refuses loudly on a missing input, a zero-clause parse and an
  implausible count; byte-identical on a re-run, verified.
* **`docs/c17-c23-clause-delta.json`** — its output, **aggregates plus the
  clauses the C tier cites**. The full 1330-row table is deliberately NOT
  committed: it would be a rendering of the standard's own contents, and
  **no ISO text is vendored in this repository**. Anyone with the public
  drafts re-runs the instrument for the whole table.
* **`harness/c_citation_check.py`** — resolves every ISO citation in the C
  tier against the drafts and reports what the cited clause is actually
  TITLED in the edition claimed (§2.5). Implements the C lane's citation
  convention plus the fourth exclusion this instrument's own run
  discovered; verdicts `ok` / `MISSING` / `AMBIGUOUS`; exits non-zero on
  any problem; refuses loudly when a draft is absent and when it finds
  zero citations. Deterministic, verified. **Its output is deliberately
  NOT committed**: the C lane's retrofit is in flight, so a checked-in
  baseline would be stale within the day and would invite the "fixed
  documentation reports as drift" failure it exists to prevent. The
  instrument is the durable artifact; its output is a live check.
* **`harness/py_version_delta.py`** — the Python version instrument
  (§2.3), in two halves: the `ast` grammar per interpreter, and the
  whole-program corpus executed under each. Missing interpreters are
  reported and skipped loudly; a row it cannot run is an ERROR row with a
  reason. Deterministic, verified.
* **`docs/py-version-delta.json`** — its output across CPython
  3.9.19 / 3.11.11 / 3.12.8 / 3.14.5. 65 script rows, 0 error rows.
* **`docs/backlog.md`** — the record.

**The fuller closed-function measurement is cited and not landed here.**
The 1458-row run behind §2.3's 100.00% value-identity extends
`harness/diff_test.py`'s comparison to exception MESSAGE text, which the
harness does not currently compare — the closed-function surface compares
exception CLASSES only, so today the entire 59-row message delta is
invisible to `harness/cases.json`. **That is an owed item for the Python
lane**, and it matters precisely because §2.4 puts the message renderer in
the version-scoped layer: if the delta layer is a renderer, the cases
surface has to start comparing what the renderer produces, or the layer's
whole cost centre stays unmeasured.

**This charter carries no Lean.** It changes `docs/` and adds two
`harness/` instruments, and it touches no `.lean` file, no `lakefile.toml`,
no `LeanModels.lean` and no `lean-toolchain` — by design, because the
document constrains and the lanes implement. `docs_check` is therefore the
relevant gate and it is green at 73/73 with 19 illustrative-exempt. The
machine was at load 22 under other lanes' builds while this landed, so per
§7.1 no build was started for a change that contains no Lean; the probes
that produced §3.4's and §3.5's toolchain measurements were small
dependency-free scratch files run under `nice -n 19`, which §7.1 rule 3
permits without the lock.
