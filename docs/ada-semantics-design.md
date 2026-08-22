# The Ada tier's M2: the semantic model, designed

**Status: M2's design, census-first. No interpreter is built here**, and the
inch that builds the first one is §4. M1 is complete and durable
(`docs/backlog/ada.md`, `docs/backlog.md` §L63-§L86): the corpus is censused,
the frontend is built, the envelope is fixed and the ingester round-trips two
fixtures under 30 `#guard`s.

Every clause title cited below was read out of `docs/ada-spec-census.json`
rather than recalled, which is the joined-ladder discipline
(`docs/ada-charter.md` §6.1) applied to this document's own citations.

---

## 0 What M2 inherits rather than decides

Three things are already law and are not re-argued here. They are listed so
the design's actual decisions are visible against them.

| inherited | from | consequence for Ada |
| --- | --- | --- |
| `SemM W ρ = ExceptT ρ (StateT W Halt)` — `ExceptT` OUTSIDE `StateT`, so the world survives a raise; fuel is an INDEX on the step function, never in state | `docs/family-architecture.md` §3.4, instantiated in `LeanModels/Es/Completion.lean` | adopted whole; §1 instantiates `W` and `ρ` |
| Verdicts `MATCH \| REFUSE \| DIVERGE \| TIMEOUT`, four REFUSE causes, `live` | §5.1-§5.3 | adopted; §1.3 finds Ada needs a cause the current substrate lacks |
| **MATCH is MEMBERSHIP** at a bounded-error site, never `⊕` | §5.1 — *minted by this lane*, `docs/backlog.md` §L63 | §1.4 |

And two rulings from the charter that shape M2 more than any of the above:

* **The scoreboard is a TRACE EMITTER** and the ACAA's own `GRADE` issues our
  verdicts (`docs/ada-charter.md` §4.4, §6.3). Validated end to end in
  §L69 — ten checks including both negative cases. **This reaches into the
  monad**, not just the harness: §1.1.
* **Both ladders**: ARM-paragraph coverage AND differential grounding against
  GNAT (§6.1). Every design section below therefore names the paragraphs it
  will make claims about.

---

## 1 THE SUBSTRATE INSTANTIATION

### 1.1 `W` — the Ada store, and the trace is in it from inch 1

Four components, and the fourth is the one no sibling tier has.

```
structure AdaWorld where
  objects   : ...   -- named, scoped; ARM 3.3
  elaborated: ...   -- which library units have elaborated; ARM 10.2
  output    : ...   -- what Text_IO/Report emitted; ARM A.10
  trace     : ...   -- the ACAA event-trace rows emitted so far
```

**Objects, not addresses.** The C tier measured 86 `&`-of-automatic sites and
concluded a C local is an object with an address. Ada v0 has no such
pressure: `'Address` is Clause 13 representation territory, which §2 puts
outside v0, and the 1,374-test target scoreboard reaches it nowhere. So `W`'s
object store is a scoped map, not a byte-addressed heap, **and the day access
types arrive (§3, rung 2) it gains a heap with access values — not an
address space.** Recording the difference now is cheaper than discovering it:
this is the C charter's §2.2(b) decision arriving at the opposite answer for
a different language, which is what a sibling tier is for.

**Elaboration is a first-class `W` component and nobody else's `W` has one.**
Ada library units elaborate in order (ARM 10.2), the envelope already carries
`compilation_units` with `order` as a first-class ORDERED list, and §L74
measured why that ordering could not be re-derived: **680 of 4,810 ACATS
files — one in seven — have a name that is not among their unit names.** The
order is data the tier was handed; `W` is where it becomes state.

**THE TRACE IS IN `W` FROM INCH 1, and that is the grader ruling reaching
into the monad.** The C tier put stdout in `World` because stdout is world
data. Ada's scoreboard does not compute a verdict at all — it emits
`CSTART/CEND/CERR/BSTART/BEND/BERR/EXSTART/EXEND/EXFAIL/EXNA` rows and lets
the ACAA's `GRADE` decide (§L69). An emitter is not something to retrofit:
if the trace is not in `W` from the first statement rule, every rule has to
be revisited to add it. The envelope already carries **`line`, `col`,
`endLine`, `endCol` on every node** for exactly this (`docs/ada-envelope-schema.md`
§0.5), so inch 1 has the spans a `CERR` row needs before it has a semantics
that could produce one.

### 1.2 `ρ` — an exception OCCURRENCE, not a value

The ES tier records a requirement on the substrate's error type: `throw`
carries a `Val` and **not** a closed enum, because a thrown JS value is an
arbitrary language value. **Ada's answer is the opposite, and that is the
point** — the ES charter said this lane would be the second consumer that
settles where such a type lives, and the answer is that it does not need to
be settled centrally, because `ρ` is a parameter and the two languages want
genuinely different things.

Ada does not throw values. `raise` names an EXCEPTION (ARM 11.3, *Raise
Statements and Raise Expressions*, 20 paragraphs), exceptions are declared
entities (ARM 11.1, *Exception Declarations*), and an occurrence carries an
identity plus a message (ARM 11.4.1, *The Package Exceptions*). So:

```
inductive AdaAbrupt where
  | raised (occ : ExceptionOccurrence)   -- ARM 11.3, 11.4
  | ret    (value : Option Val)          -- ARM 6.5, Return Statements
  | exitLoop (target : Option String)    -- ARM 5.7, Exit Statements
```

`Constraint_Error` and `Program_Error` are **not a separate mechanism** —
they are predefined exceptions (ARM 11.1) and travel in `raised` like any
other. That is the family's `.exn`-shaped outcome, and it is why Ada's run-time
errors are an ORDINARY OUTCOME rather than a refusal
(`docs/ada-charter.md` §1.5).

**`goto` is deliberately absent from `ρ`** and is not deferred by accident.
It is measured at **39 of 4,188 tests**, it is intra-subprogram (ARM 5.8,
*Goto Statements*, 8 paragraphs), and putting it in `ρ` would make every
statement rule carry a label-continuation it almost never needs. §3 places it
as its own rung, where the shape can be chosen against the tests that need it
rather than guessed at now.

### 1.3 A FINDING: Ada needs a REFUSAL CAUSE the substrate does not have

`LeanModels/Es/Completion.lean` fixes `RefusalCause` at **three**
constructors — `unsupportedConstruct`, `unmodeledIntrinsic`, `environment`.
`docs/family-architecture.md` §5.2 fixes **four** causes for the family, the
fourth being `order-dependence`. **Ada needs a fifth thing that neither list
has as a constructor**: `undefined`, §5.2's cause 2 — *the language says this
run has no meaning*.

For ES that bucket is expected to be empty and is gated as such; ES has no
undefined behaviour. **Ada has it by name.** ARM 1.1.5, *Classification of
Errors*, defines **erroneous execution** as the class with *no
language-specified bound on the possible effect*, and
`docs/ada-charter.md` §1.5 maps it to cause 2 exactly. Measured scale from
`docs/ada-spec-census.json`: **23 Erroneous Execution paragraphs in clauses
1-13**, 115 document-wide, concentrated in named places — ARM 11.5
(*Suppressing Checks*) and ARM 13.9.1 (*Data Validity*) both carry the
heading.

So the Ada tier's `RefusalCause` is **not** ES's, and this is stated as a
finding rather than silently diverging:

| cause | Ada's meaning | retires? |
| --- | --- | --- |
| `unsupportedConstruct` | out of tier | by climbing a rung |
| `undefined` | **erroneous execution** — ARM 1.1.5 | **never — it is the product** |
| `environment` | outside the modeled slice (a library unit we do not model) | by widening the slice |
| `orderDependence` | an unspecified order the model cannot show unobservable | by a census, per §3.6 |

**The design does not move ES's type.** Two options exist — a `Core`
`RefusalCause` with all four, or a per-tier cause type — and choosing between
them is the architecture lane's call, not this lane's, exactly as the ES
charter left it. What this lane owes is the measurement, which is above.

### 1.4 Bounded errors are MEMBERSHIP sites — never `⊕`

The site class was minted here (`docs/backlog.md` §L63) and is now family law.
The design's obligation is to carry it correctly:

* a bounded-error site carries its **permitted set as a per-site datum**;
* the verdict is `obs (run …) ∈ permitted site`; equality is the singleton
  case, so ordinary sites need no special treatment;
* **never `⊕`.** `docs/statement-cookbook.md` §2 states the trap and it is
  worth repeating because it is Ada-specific: outcome conjunction carries an
  `S ≠ ∅` side condition that makes it a REACHABILITY claim, converting a
  permission into an obligation — *strictly stronger and, for Ada, false*.

Scale, measured: **57 Bounded (Run-Time) Errors paragraphs in clauses 1-13**
(104 document-wide over 40 subclauses). Small enough to enumerate at the inch
that needs one, and the standard has already done the enumeration — which is
the whole reason Ada could surface this class and C could not.

---

## 2 THE v0 SCOPE — the measured honest core

Not "sequential Ada". `docs/ada-charter.md` §3.3 measured that an empty core
clears only 18% and that the first four rungs are not optional in realistic
Ada. v0 is the **cheapest-first scoreboard** of §3.4, re-derived today:

| filter | tests |
| --- | ---: |
| executable classes (A, C, D, E) | 2,633 |
| ...and no tasking | 2,194 |
| ...and needing **no predefined library unit at all** | **1,374** |
| ...of which class C | 1,322 |
| ...**using `Report`** | **1,374 — all of them** |

**Every single one of the 1,374 uses `Report`.** That settles the library
obligation for v0: it is `Report`, natively modeled, and nothing else. The
package is 15 subprograms in 591 shipped lines whose own body needs exactly
two predefined units (`Ada.Text_IO`, `Ada.Calendar`), and the tier may
implement it rather than execute it.

Inside that 1,374, by feature reach:

| core | tests reached |
| --- | ---: |
| no feature bucket at all | 322 |
| within {exceptions} | **517** |
| within {exceptions, access types} | 659 |
| within {exceptions, access types, separate compilation} | 812 |
| ...+ generic instantiation | 834 |

> **v0 = sequential Ada + exceptions + the `Report` surface = 517 tests**,
> and it is the first number the tier can actually score.

---

## 3 THE INCH LADDER, priced

Each rung is a census before it is a build, per §L25's law. Session counts
are anchored to the C lane's measured M2 (~15-20 sessions to its first
score).

| inch | content | reach | price |
| ---: | --- | ---: | ---: |
| 1 | values + the first statement kinds (§4) | — | 1 |
| 2 | `W` + assignment + sequence + `if` (ARM 5.1-5.3) | — | 2 |
| 3 | subprogram calls, the frame, `return` (ARM 6.5) | — | 2 |
| 4 | **exceptions**: raise, handlers, propagation (ARM 11.1-11.4) | — | 2-3 |
| 5 | `Report` natively + the TRACE EMITTER | — | 2 |
| 6 | **THE FIRST SCORE** — 517 tests through the ACAA's `GRADE` | **517** | 2 |
| 7 | `loop`/`exit`/`case` (ARM 5.4, 5.5, 5.7) | — | 2 |
| 8 | access types | 659 | 3 |
| 9 | separate compilation + elaboration order | 812 | 2-3 |
| 10 | generic instantiation | 834 | 3-4 |

**~21-24 sessions to the first real score at inch 6**, with the score arriving
at inch 6 of ten rather than at the end — the shape the C lane's ladder
deliberately took.

Deferred with a reason, not by omission: **tasking** (768 tests, and
`docs/family-architecture.md` §3.6's ∀-schedule machinery is the right home,
not this ladder); **`goto`** (39 tests, §1.2); **representation clauses and
aspects** (unmeasured by construction — §L74's lexical census could not see
them, and the frontend census now can); **floats** (the charter's R4 gate,
and neither host declares Annex F).

---

## 4 INCH 1 — values, and the first statement kinds

**Monadic from day one**, and the spec half separate from the interpreter
half, per the founding-checklist law.

**What lands.** `LeanModels/Ada/Ada2012/Value.lean` — Ada's scalar values and
the one decision that cannot be retrofitted, plus the first statement kinds
of the walker with `SemM` in their types from the first line.

**The one decision that cannot be retrofitted**, and it is Ada's analogue of
the C lane's `close`: **a scalar value carries its SUBTYPE, and a
constraint violation raises `Constraint_Error` rather than wrapping or
refusing.** ARM 3.5 (*Scalar Types*, 63 paragraphs) gives ranges; ARM 4.6
(*Type Conversions*, 98 paragraphs) and ARM 5.2 (*Assignment Statements*, 28
paragraphs) are where the check fires. This is where Ada differs from C most
sharply and most cheaply: C's out-of-range signed arithmetic is UB and must
REFUSE, while **Ada's is a defined raise of a predefined exception** — an
ordinary outcome, not a refusal. Getting that backwards would make the tier
refuse a huge fraction of a suite that is largely *about* constraint checking.

**PLACEMENT: `Ada2012/`, not the trunk**, and the argument is the mirror of
inch 6's. `LeanModels/Ada/{Ast,Json,Load}.lean` are trunk because the AST is
kind-agnostic and provably edition-insensitive (`LeanModels/Ada.lean`).
**Meaning is not**: the ARM has 953 Legality-Rule paragraphs against 572
Syntax paragraphs, and it is the first number that differs between editions.
`Value.lean` goes where the C lane's went.

**ARM citations are carried in the declarations from inch 1**, so the
paragraph map (`docs/ada-charter.md` §5.8) is generated from the tier rather
than written beside it. Each cited paragraph gets `status` and, once inch 6
scores, the tests that witness it — the joined ladder, built rather than
promised.

**The gate**: `#guard`s on the value layer, non-vacuous by the C lane's test
— flip a claim and Lean must report the failing expression. `Constraint_Error`
raised where the ARM says raised, and NOT raised where it does not.

---

## 5 What this design does NOT decide

* **Where `RefusalCause` lives** (§1.3). The measurement is this lane's; the
  type's home is the architecture lane's.
* **`goto`'s shape** (§1.2) — chosen at its rung, against the 39 tests.
* **The tasking model** — §3.6's ∀-schedule parameter is the expected home
  and this ladder does not reach it.
* **Whether `Report` is modeled or executed.** v0 models it; executing its
  real body would need `Ada.Text_IO` and `Ada.Calendar`, and the choice is
  inch 5's with the census in hand.
* **Anything about floats.** The charter's R4 gate stands unchanged.
