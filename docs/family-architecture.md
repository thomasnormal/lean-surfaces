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
| SystemVerilog | `Sv` | spec-mirror — IEEE 1800 | `SV2017`, `SV2023` — **PROPOSED** | pyslang frontend; a simulator | **public `sv-tests`** (see below) | **CONSOLIDATION** — 8 166 lines, **98 theorems**, dormant but verified working |
| WebAssembly | `Wasm` | spec-mirror — W3C core **+ official suite** | **PROPOSED** | the reference interpreter **and the `.wast` runner** | the official `.wast` suite | founding |
| ECMAScript | `Es` | spec-mirror — ECMA-262 **+ official suite** | **PROPOSED** | an engine **and test262's harness** | test262 | founding — blocked on SoftFloat (§3.5.3) |
| Ada | `Ada` | spec-mirror — ISO/IEC 8652 **+ official suite** | **`Ada2022`** (spec head) **and `Ada2012`** (suite edition) — RATIFIED | a GNAT toolchain **and the ACATS grader** | **ACATS 4.2**, 4 188 tests | founding — **version pair FORCED** |
| RISC-V | `Rv` | spec-mirror — RISC-V ISA | **PROPOSED** | the ISA oracle | `harness/rv` | consolidation — 2 041 lines |
| Verilog-A | `VerilogA` | extraction — OpenVAF | — | OpenVAF | `Examples/verilog-a` | consolidation — 606 lines |
| SPICE | `Spice`/`Circuit` | extraction — ngspice | — | ngspice | `Examples/spice` | active — 27 675 lines, separate architecture (§6.1) |

The last three carry no edition token today. That is allowed and it is
what §1.4 rules on: **a language earns version directories when its tier
claims an edition, not before.**

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
when a neighbour asserts it, and this one now is.

**One standing violation, flagged and not fixed here.**
`docs/sv-corpus-coverage.md` line 5 records a corpus path under a private
home directory and organization. That breaches the same rule this
correction invokes. It is the SV lane's file and their charter is in
flight, so it is theirs to redact — but it is named here so it is not lost.

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
   the point: **Spice 11, Circuit 11, Verilog-A 1, and ZERO in Python, C,
   SystemVerilog and RISC-V.** The analog lanes need real analysis
   (`Mathlib.Data.Real.Basic`, `Analysis.Calculus.Deriv`,
   `MeasureTheory.*`) and take it; the proof tiers claim core-only and
   *are* core-only. So a founding lane states its own dependency posture in
   its charter — "this tier depends on no package" is a claim about that
   tier, checkable per tier, and false if read as a claim about the
   repository.

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

1. **`unsupported` — out-of-tier construct.** Retires by climbing a rung.
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
host-hook name. **The payload objection dissolves exactly the way `ρ` did**
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

### 5.3 VACUOUS is not a verdict — and neither is MUTUAL REFUSAL

A run that executed **nothing** must never score as agreement.

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

Both halves of §5.3 are the same law: **a check must not report sameness
where there was no content.** Python's
harness carries `"live"`; C's scoreboard carries the statement count. This
is an instrument-level ERROR, not a verdict — a scoreboard that reports it
as MATCH is broken, and one that reports it as REFUSE is lying about
coverage.

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
  the check**, which is the whole of the difference;
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
  **silently** and then convicts the wrong thing;
* a **`--compare`** mode against the committed JSON, because corpora that
  live in other repositories move on their own schedule and staleness must
  be mechanically detectable rather than merely possible;
* **every refusal path RUN, not admired** — a missing input, a zero-row
  parse (an empty census is an instrument fault, never a finding), and a
  rejected input. The third one was a real defect in the C instrument,
  found only by executing the fixture, and this charter's own instrument
  reproduced the lesson: its first answer was a plausible table produced
  by matching renumbered clauses (§2.1), and it was the spot-checks that
  caught it;
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
* **RE-PINNING IS RECOVERY, NOT DERIVATION: find the commit that
  REPRODUCES THE RECORDED HASH.** ES's `ecma262` pin was recovered by
  taking the annotated tag `es2026-errata` → `d89c03f2` and confirming its
  `spec.html` **sha256 is byte-identical to the census's recorded
  `spec_sha256`**. The hash is the anchor; a tag, a date or a changelog is
  a *hint* toward the commit, never the pin itself. **Reconstructing a pin
  from provenance metadata is a guess that looks like a citation** — the
  reproduction is what makes it a fact;
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

> **A NUMBER CARRIES THE STATE IT WAS MEASURED IN. Quote both, or quote
> neither.**

**A FOURTH INSTANCE, and it is the one that flatters hardest: the SEARCH
that agrees with you.** A name collision made a `grep` confirm a prior —
`DRAIN` in `VCGen.lean` is the *generator drain*, 47 occurrences, and not
the short-circuit `DRAIN` trick the searcher was looking for. The hits were
real, numerous, and about something else.

> **A grep that agrees with your prior is the one to re-run.**

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

**MEASURED AGAINST ITSELF — and it caught a THIRD wrong unit: IMPORTS.**
A bound on the breakage from a payload change was taken as the count of
**direct importers** of `Core.Outcome` — **2 files**. That is neither the
identifier nor the pattern position; it is a unit that cannot see the
thing at all, because **a consumer reaches a constructor's shape without
naming its module.** The convicting case: `guards.lean`'s `refusalOf`
matches `.error (.unsupported m)` and **names no Core symbol whatsoever**.

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

**AND THE MOTIVATED-ERROR RULE, from a census that was wrong TWICE before
it was right — and both errors flattered.** SoftFloat's consumer count ran
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

**THE POLICY.**

> **Suites drive scope. ONE theorem-worthy EXEMPLAR per tier drives the
> proof library. The exemplar is chosen for its THEOREM — never for its
> authorship — and no program is commissioned as a driver for its own
> sake.**

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

**`tools/triad.sh --classify` IS OUR-REPO-ONLY BY CONSTRUCTION**, and a
lane pointing it at a foreign checkout will get a confident wrong answer
rather than an error. Two reasons, both structural:

* **the class floor hard-wires our gates** — `docs_check` / `diff_test` are
  named in the classifier's floor and in the default gate set, and a
  foreign project has neither;
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
  iteration);
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
`tools/triad.sh` now stamps the index's tree (`git write-tree`) plus `HEAD`
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
| `tools/docs_check.py` | doc-embedded blocks match the tree | the marker convention |

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
    zip-based relation does not imply equal lengths.** The entire Mathlib
    `forall₂_*` route cannot apply, and importing it costs a red rather
    than a shortcut.

    **THE GENERATOR'S EXTRA PREMISES ARE THE TELL, and reading them is the
    cheap check.** The generator emits `Resulttype_sub` with a **separate
    explicit length premise** — which is precisely the fact that the
    relation does *not* carry length equality, written down by the
    generator itself:

    > **A generated model's extra premises tell you what its relation does
    > NOT carry.**

    So the premise list is not boilerplate to be discharged; it is a
    **specification of the gaps**, and a lane that reads it first learns
    what no library lemma can supply.

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

**Migration is append-only and rewrites no history**: the current file is
renamed to an archive, every existing `§Lnn` reference keeps resolving, and
**new landings use per-lane files from that commit on.** It also retires the
race §7.2's push-time re-read rule exists to survive.

#### 9.5a THE INBOUND CONVENTION — filing into a lane that is not yours

Per-lane files answer *"where do I append?"* only while every entry has an
obvious owner. One lane filing a finding into **another lane's** file needs
a convention, or it mints ids in a sequence it does not own:

* the entry is **headed `INBOUND`**;
* it carries a **SENDER-namespace id** — `YYYY-MM-DD-<sender>-<n>` — so
  **nothing is minted in the owner's sequence**;
* it tells the owner explicitly to **renumber it or close it**; the entry
  is a *proposal to the owner's record*, not a fact already in it;
* the **generated index renders `INBOUND` as its own class**, listed
  against each owning lane, so an owner sees what is queued for them
  without reading their own file for surprises.

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

Two honesty clauses that make the number usable. **Citation over-credits** — a
tool that mentions a law in a comment is counted — so the NO GATE list is a
**LOWER BOUND on the unenforced set, never a coverage figure.** And **the unit
the count ranks is the HOME, not the law**: laws sharing a `§` share every
token and therefore tie, which is information rather than noise — it says the
*section* is what the ledgers keep reaching for. The report prints both views.

* **FULL — about every 10 landings**, and the next full audit **re-measures
  its own headline numbers**: the **38%** violation density, and whether
  the three `--compare` exit codes and four `git_rev` stamps are actually
  fixed. An audit that does not re-measure what it reported is prose again.

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
