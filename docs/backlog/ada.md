# The Ada lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the Ada lane.** Ids are `YYYY-MM-DD-ada-<n>` and need no reservation, because
the lane name makes them unique — which is the point: `docs/backlog.md` has
`L2`, `L3` and `L4` twice each, and this lane spent three landings renumbering
its own section around collisions (`L59→L60`, `L63→L69`, `L85→L86`) at ~66
landings a day.

**Everything before 2026-08-22 is in `docs/backlog.md`** and stays there;
this lane's history is §L63, §L69, §L70, §L74, §L75 and §L86, and every one
of those references keeps resolving. Migration is append-only and rewrites no
history.

---

### SPEC COVERAGE — the completion metric (standing; updated every landing)

Per `docs/family-architecture.md` §9.0: the tier's goal is COMPLETION, the
suite that measures it for Ada is **ACATS**, and this number is how far away
it is. The Go lane's table (`fef0b79`) is the shape being copied — two
denominators with the choice's cost named, the upper-bound guard, and the
ceiling read at the CURRENT vocabulary.

Reproduce it, do not quote it:

    python3 harness/ada_suite_census.py            # the corpus and the ladder
    python3 harness/ada_round_trip.py --self-test  # the extractor's gate

| rung | sha | ACATS language tests | ACATS **core** (clauses 1-13) |
| --- | --- | ---: | ---: |
| M2 inch 1 — the value layer | `9985b05` | **0 / 4,188 (0.0%)** | **0 / 3,996 (0.0%)** |
| M2 Core adoption | `342a1f5` | **0 / 4,188 (0.0%)** | **0 / 3,996 (0.0%)** |
| M2 inch 2 — the statement tier | `9ed43ef` | **0 / 4,188 (0.0%)** | **0 / 3,996 (0.0%)** |
| M2 inch 3 — calls, the frame, `return` | `519baa7` | **0 / 4,188 (0.0%)** | **0 / 3,996 (0.0%)** |

**IT IS ZERO, AND ZERO IS THE HONEST NUMBER.** Nothing has been graded,
because **no grader has run**: there is no statement tier yet, so no ACATS
test can be executed and no verdict emitted. The instruments that will
produce the number exist and are audit-hardened (`harness/ada_round_trip.py`,
`harness/ada_suite_census.py`), and the emitter that feeds `GRADE` is inch 5-6
(`docs/ada-charter.md` §4.4). **Standing a graded run up is a named rung, and
it is the one after inch 2.** A tier that quietly omitted this row until it
had something flattering to put in it would be hiding the only number §9.0
asks for.

**Two denominators, and the gap is 192 tests.** `tests_language` (4,188)
includes the **Specialized Needs Annexes**; `tests_core` (3,996) is clauses
1-13, which is the slice `docs/ada-semantics-design.md` scopes M2 to. The
annex tests are legitimate Ada and the tier must eventually grade them, so
the wider column stays — but ranking against it would rank work this tier
has not scoped.

**CEILING AT THE CURRENT VOCABULARY: 739 core tests (18.5%).** That is the
reach ladder's step 0 — the core tests that use **none** of the nine heavy
buckets (exceptions, tasking, access types, separate compilation,
instantiation, generics, real types, tagged types, `goto`). It is what a
tier could grade if it modelled everything *else* perfectly, and the
vocabulary today is **scalars and one raise** — no statements at all. So 739
is the bucket-free ceiling, **not** a claim about inch 2.

**THE UPPER-BOUND GUARD, in this tier's own terms.** A bucket-reach figure is
SYNTACTIC: it says which tests avoid a construct, never that their semantics
are modelled. **Recognising that a test avoids tasking is not running it.** No
syntactic win is ever banked in the graded column — that column moves only
when a test is executed and `GRADE` accepts the emitted trace. And one
structural fact sets the real entry price: **2,707 of the tests call
`Report.Test`**, so the ACATS `Report` package is a prerequisite of the first
non-zero row rather than a later convenience.

---

## 2026-08-22-ada-1 — THE STANDING STRATEGY, adopted by touch: `DIFFER` was a conformance gap, and this lane was one of §9.4's drifted emitters

`docs/family-architecture.md` §9 landed at `cd0a722`. Five items were
dispatched to this lane; this entry records which were **done**, which are
**blocked and why**, and one where the lane was **already conformant** and
says so rather than claiming credit.

### §9.4 VERDICT VOCABULARY — a real gap in this lane's gate, fixed

`harness/ada_round_trip.py` emitted **`DIFFER`**. §5.1's law is
**`MATCH | REFUSE | DIVERGE | TIMEOUT`**, and §9.4 measured three of seven
emitters as drifted from it. **This lane was one of the three**, and the
finding is worth the sting: the gate was written *after* the family charter
fixed the vocabulary, by an author who had read §5.1 and then chose a word
that felt more precise for a round-trip comparison. That is §9's one-line
diagnosis exactly — *the contract lives in prose, and each lane
hand-implements it* — with this lane as the instance.

`DIVERGE` is now the name; `DIFFER` is gone from the file. The module
docstring states the vocabulary and, more usefully, states **what this gate
cannot emit and why**: `REFUSE` and `TIMEOUT` never appear because a gate
that re-extracts and compares has nothing for a model to decline and no fuel
to exhaust. They land when the SCOREBOARD does (`docs/ada-charter.md` §4.4's
trace emitter), which is the artifact that actually has all four.

`ERROR`, `SKIP` and `VACUOUS` are **not offered as verdicts** — they are
instrument-level outcomes, which is what §5.3 says a vacuous run is. The
distinction is not cosmetic here: this lane shipped a VACUOUS bug in §L75
(a markings check that compared nothing and scored MATCH), and the whole
reason it was catchable is that the two categories are kept apart.

**`censuskit.row()` is where §9.4 wants this enforced rather than
remembered, and it is not landed yet** — so this is conformance by hand, and
the kit is adopted the next time these instruments are opened (§9.2's
on-touch rule).

### §9.1 BUG BEFORE REFACTOR — this lane is NOT one of the three, verified

§9.1 names three `--compare` implementations that exit 0 on drift. Checked
rather than assumed: all three of this lane's censuses
(`ada_spec_census`, `ada_suite_census`, `ada_construct_census`) end their
compare path with `return 1 if drift else 0`. **A `--compare` that cannot
fail cannot gate**, and these can. Recorded because "we were already fine" is
only worth saying when it has been measured.

### §9.2 / tools/triad.sh — ADOPTED, hand-rolled script deleted

This lane's private `.ada-triad.sh` is **gone**. It was written to
Amendments 9 and 11 and it was still lane-private prose-following of the kind
§9.2 exists to end. `tools/triad.sh --self-test` passes **12 of 12 with no
Lean executed**, which is what made adoption safe to do on a machine at load
31. The lane's deferred confirming triad will run through the shared script.

### §9.6 / A13 CoW SEEDING — already this lane's practice, now law

Amendment 13 makes `cp -Rpc` seeding law, crediting this lane's APFS
observation. Both of this lane's clones were seeded that way (13 s each), and
the durability entry in §L86 already reports the measurement that matters
for §9.6's disk arithmetic: **a CoW clone whose `.lake` has never been
rebuilt costs near-zero incremental blocks**, and only starts consuming real
space when its first build runs. That is an argument for the deferred triad
staying deferred while the data volume is at 98%, not only for the CPU.

`tools/workspace.sh` is not landed; the `check` piece is what this lane would
use, and it will be adopted when it exists.

### §9.3 SPAN NAMING — this lane is one of the three that CONVERGED, and it is blocked

§9.3 ratifies `line / col / endLine / endCol` because **three lanes chose
them independently** — C, Ada and ES. This lane's `AdaSpan` already has
exactly those four fields, chosen (see `LeanModels/Ada/Ast.lean`) because the
scoreboard emits the ACAA's `CERR` records and those need a line AND a
position.

§9.3's endpoint is that `Core.Span` is renamed to those names and **"Ada's
type then has nothing left in it"** — i.e. `AdaSpan` disappears into
`Core.Span`. **`Core.Span` is still `lineno / colOffset / endLineno /
endColOffset`**, checked today, so the deletion is blocked on that rename
landing. It is also a LEAN touch, and Amendment 11 now puts every Lean
invocation inside the lock, so it waits for a quiet machine and rides the
deferred triad rather than taking a tenure of its own.

### What this landing did NOT do, and why

**No Lean ran.** Amendment 11 makes the lock cover all Lean execution, the
machine was at load 31 with the data volume at 98%, and every item above is
docs or Python. The one item that needs Lean (§9.3's `AdaSpan` deletion) is
correctly blocked on `Core.Span` anyway.

`docs_check` **83/83**, 23 illustrative-exempt. `ada_round_trip --self-test`
**6/6**. `tools/triad.sh --self-test` **12/12**, no Lean.

### Three corrections to this entry, found by checking rather than assuming

**1. This entry's own commit message was MANGLED, by this lane's own habit.**
The message described the compare fix as ending `with .` — the code snippet
had been eaten. Cause: `git commit -m "…`code`…"` in a double-quoted string
**command-substitutes the backticks**, which also produced a stray
`return: too many arguments` that was easy to read past. Measured: 82
backticks survive across the last 40 commits from other lanes, so this is
**not** a shared trap — those lanes use a heredoc or `-F`, and this lane used
`-m "…"`. Fixed by practice, not by force-push: rewriting pushed history to
repair a commit message would disrupt every lane rebasing onto master, which
is a real cost for a cosmetic gain. **Commit messages go through a
single-quoted heredoc from here on.**

**2. `28b9f5e` fixed SEVEN instruments, not §9.1's three — and it correctly
did not touch this lane's.** Verified by reading the commit's own file list:
no Ada file appears, and all three Ada censuses still end their compare path
with a nonzero return. Checking this mattered because a sweep that "fixed"
an instrument which was not broken is how a working gate acquires someone
else's semantics.

**3. This lane stamps NO git revision, and that is correct rather than a
fourth defect.** §9.1's other finding is four `git_rev` helpers that swallow
their failure and stamp `null`. The Ada instruments have none, because the
corpora are **cross-repo and not git-tracked**: ACATS is pinned by its own
`ACATS_Version` constant plus a per-file `sha256`, and the ARM by the edition
read out of its own front matter. Content pinning is strictly stronger than a
revision stamp for an artifact that lives outside the repository, so there is
nothing here to fix — but "we have no `git_rev`" would have looked like the
defect if it had not been explained.

## 2026-08-22-ada-2 — M2's DESIGN: the substrate instantiated, and Ada needs a REFUSAL CAUSE the substrate does not have

M1 is complete and durable, so M2 begins. `docs/ada-semantics-design.md`
lands — census-first, **no interpreter built**, classified `docs` by
`tools/triad.sh --classify-only` and therefore owing no tenure. Every clause
title in it was read out of `docs/ada-spec-census.json` rather than recalled,
which is the joined-ladder discipline applied to the design's own citations.

### THE FINDING: `RefusalCause` is three constructors and Ada needs a fourth

`LeanModels/Es/Completion.lean` fixes `RefusalCause` at
`unsupportedConstruct | unmodeledIntrinsic | environment`.
`docs/family-architecture.md` §5.2 fixes **four** causes for the family. Ada
needs the one neither list has as a constructor: **`undefined` — §5.2's cause
2, *the language says this run has no meaning***.

For ES that bucket is expected EMPTY and is gated as such, because ES has no
undefined behaviour. **Ada has it by name**: ARM 1.1.5, *Classification of
Errors*, defines erroneous execution as the class with *no language-specified
bound on the possible effect*. Measured: **23 Erroneous Execution paragraphs
in clauses 1-13**, 115 document-wide, concentrated in ARM 11.5 (*Suppressing
Checks*) and ARM 13.9.1 (*Data Validity*).

**This lane does not move the ES type.** Two options exist — a `Core` cause
with all four, or a per-tier cause type — and choosing is the architecture
lane's call, exactly as the ES charter left it. What this lane owes is the
measurement, and that is delivered rather than a patch to somebody else's
file.

### `ρ` is an exception OCCURRENCE, and it VALIDATES the substrate's parametricity

The ES tier records a requirement that `throw` carry a `Val` and not a closed
enum, because a thrown JS value is an arbitrary language value, and notes
this lane would be the second consumer that settles where such a type lives.
**Ada's answer is the opposite and the conclusion is that it need not be
settled centrally at all.** Ada does not throw values: `raise` names a
declared exception (ARM 11.1, 11.3) and an occurrence carries an identity
plus a message (ARM 11.4.1). `ρ` is a parameter, the two languages want
genuinely different things, and both get them.

`Constraint_Error` and `Program_Error` are **not a separate mechanism** —
predefined exceptions travelling in the same arm as any other, which is why
Ada's run-time errors are an ORDINARY OUTCOME and not a refusal.

### THE TRACE IS IN `W` FROM INCH 1 — the grader ruling reaching into the monad

The C tier put stdout in `World` because stdout is world data. **Ada's
scoreboard computes no verdict at all**: it emits the ACAA's event-trace rows
and `GRADE` decides (§L69, validated with both negative cases). An emitter is
not retrofittable — if the trace is not in `W` at the first statement rule,
every rule is revisited to add it. The envelope already carries `line`,
`col`, `endLine`, `endCol` on every node for exactly this, so inch 1 has the
spans a `CERR` row needs before there is a semantics that could produce one.

`W`'s other Ada-specific component: **elaboration order**, which no sibling
tier's world has. It is data the tier was handed rather than derived —
§L74 measured that one ACATS file in seven has a name that is not among its
unit names, so it could not have been re-derived.

### v0 IS 517 TESTS, and every one of the 1,374 uses `Report`

Re-derived today: 2,633 executable → 2,194 without tasking → **1,374 needing
no predefined library unit at all**, of which 1,322 are class C — and
**1,374 of 1,374 use `Report`**. That settles the v0 library obligation
completely: it is `Report`, natively modeled, and nothing else.

Inside that: 322 use no feature bucket, **517 are within {exceptions}**, 659
within {+access types}, 812 within {+separate compilation}, 834
{+instantiation}. So **v0 = sequential + exceptions + `Report` = 517 tests**,
the first number the tier can actually score.

**The ladder is ten inches, ~21-24 sessions, with THE FIRST SCORE AT INCH 6**
— the shape the C lane's ladder deliberately took, rather than a score at the
end.

### Inch 1's one irreversible decision, and it is the mirror of C's

A scalar value carries its SUBTYPE, and a constraint violation **raises
`Constraint_Error`** rather than wrapping or refusing (ARM 3.5, 4.6, 5.2).
This is where Ada differs from C most sharply and most cheaply: C's
out-of-range signed arithmetic is UB and must REFUSE; **Ada's is a defined
raise of a predefined exception** — an ordinary outcome. Getting it backwards
would make the tier refuse a huge fraction of a suite that is largely *about*
constraint checking.

`Value.lean` goes in **`Ada2012/`, not the trunk** — the mirror of inch 6's
argument. The AST is trunk because it is kind-agnostic and provably
edition-insensitive; **meaning is not**, and the ARM's 953 Legality-Rule
paragraphs against 572 Syntax paragraphs is the first number that differs
between editions.

### A tool caught a defect in this lane's old lane name

`tools/triad.sh --lane ada-lane` is REFUSED: *"`-` would break the ticket
parse"*. The ticket format is `<ts>-<pid>-<lane>` and the reaper reads the
pid with `cut -d-`, so a hyphenated lane name silently corrupts the
staleness check. **This lane's deleted hand-rolled script used exactly
`ada-lane`**, and its own reaper would have parsed the wrong field. The lane
is `ada` from here on. This is §9.2's argument in one line: the shared script
validates what a lane-private one merely got away with.

---

## 2026-08-22-softfloat-5 — INBOUND FROM THE SOFTFLOAT LANE: Ada lane's to give floats a gate of its own, or rule them out of tier

*Filed by the SoftFloat lane during its consumer census
(`docs/softfloat-charter.md` §2.4). Id kept in the SoftFloat namespace.*

### THE ADA FLOAT DEFERRAL CITES A GATE THAT IS IN ANOTHER TIER'S CHARTER

`docs/ada-semantics-design.md` defers floats twice, both times to *"the
charter's R4 gate"*:

* line 231 — *"**floats** (the charter's R4 gate, …)"*
* line 285 — *"**Anything about floats.** The charter's R4 gate stands
  unchanged."*

**Measured: `docs/ada-charter.md` contains zero occurrences of `R4` and zero
occurrences of `float`.** R4 is the **C** charter's rung. The Ada lane has
inherited a C gate by mis-citation, and the deferral therefore rests on a
condition no Ada document states — which means nothing can ever discharge it,
because there is no Ada-side gate to satisfy.

**Also measured, and it is the substantive half:** **Annex G — Ada's numerics
annex, which is where IEEE 754 conformance would live — is mentioned nowhere
in the repository.** (Case-sensitively. A case-insensitive search hits
`annex gap` in `docs/backlog.md`, which is §5.4a's name-collision trap and not
a citation.)

**What the Ada lane owes itself here** is a gate of its own: either an
Ada-charter rung that names the float condition in Ada's terms (ARM Annex G,
`Float`/`Long_Float`, and whether ACATS 4.2's numerics tests are in scope), or
a plain statement that floats are out of tier. Either is fine; the current
state is a deferral pointing at another language's rung.

## 2026-08-23-ada-1 — M2 INCH 1 IS GREEN, and the audit found a gate of mine that could not fail

`LeanModels/Ada/Ada2012/Value.lean` — the value layer, **31 `#guard`s** — plus
the four rows of `docs/quality-audit-2026-08-23.md` "## ada". Triad green:
`build exit=0`, `docs_check 88/88`, `diff_test 1427 cases, 0 failed, 116
whitelisted, 1311 matched`.

### THE DECISION INCH 1 EXISTS FOR, verified

`constrain` is this tier's `close`. In range → the value; out of range →
**raise `Constraint_Error`** (ARM 4.6, 5.2). Not a wrap, and **not a
refusal**: the ARM defines the outcome completely, so refusing it would be a
false statement about the language and would refuse most of a suite that is
largely *about* constraint checking. The C lane's `close` refuses at exactly
this position because C leaves signed overflow undefined — same slot,
opposite answer, and the difference is the languages'.

Guarded directly: `!okIs (.int Int8 (-128)) (constrain Int8 128)` — Ada never
wraps. Also pinned: overflow on `+`/`-`/`*` raises, division by zero raises
(ARM 4.5.5(11)), `adaDiv` truncates toward zero and `adaRem` takes the LEFT
operand's sign (ARM 4.5.5(5-6)), and `Boolean` goes through the enumeration
constructor because **`Boolean` and `Character` ARE enumeration types** (ARM
3.5.2-3.5.3) — a tier giving `Boolean` its own constructor models a language
Ada is not.

`adaDiv` is DEFINED here rather than borrowed: `Int.tdiv` is not in this
toolchain's `Int` module (checked), and a tier whose division is "whatever
`/` resolved to" has not decided anything.

### THE AUDIT'S FOUR ROWS — two of them bit my own gate

**`ada_round_trip.py:357` is the one worth reading.** Its docstring said *"the
gate must FAIL a tampered envelope, or it is decoration"* — and **it never
once ran the gate.** Three of six cases asserted `SKIP`, which `check()`
returned because the fixture passed an EMPTY temp dir as `source_root`, so
`regenerate()` bailed before comparing anything. No case reached EDGE 2/3,
the field loop, or the payload compare, and **no case ever produced MATCH**.
The instrument I built to catch vacuity elsewhere was vacuous itself.

Now 11 cases with a source staged under `source_root` and a **stub
extractor** standing in for the frontend: untampered → MATCH, and mutated
payload / `unsupported_count` / markings / unit-name → DIVERGE each.
Stubbing is deliberate — the subject is the COMPARISON, not the parser — and
it also keeps the self-test alive now that libadalang has been purged twice.

**`:331`** — `SKIP` was exempt from `bad`, so a run pointed at the wrong
`--source-root` reported `MATCH 0, SKIP N` and **exited 0**. A gate that
compared nothing passed. `MATCH + DIVERGE == 0` is now an instrument-level
failure naming the root — the same absence-vs-zero defect this gate's own
VACUOUS verdict exists to catch (`2026-08-22-ada-1`), found in the gate.

**`ada_suite_census.py:688`** — a missing or unparseable `VERSION.A` recorded
`"acats_version": null, "language_version": null` verbatim: **an absence
serialized as a measurement.** Now refuses, as does an unlisted major and a
missing `ACATS*.LST`. All four refusal paths RUN, exit 1 each — and running
them **exposed a latent crash**: `clause_of` assumed 7-character ACATS names
and raised `IndexError` on a short one. A traceback is not a refusal. My own
refusal fixture found a bug a real delivery would never have triggered.

**`guards.lean:140`** — vacuous twice over. An all-zero span satisfied
`endLine ≥ line && endCol ≥ col`, so the guard could not detect the very
absence it existed to pin; and `endCol ≥ col` is not a validity property of a
MULTI-LINE span at all (10:40 → 12:5 is legal and would have failed). Now the
positive property, pre-verified against the fixture in Python so no tenure
was spent discovering it.

One regression caused and caught in the same landing: the new manifest
refusal broke the census's own self-test fixture, which had no `ACATS*.LST`.
Fixed by giving the fixture one.

### THE TRIAD DEBT, DISCHARGED

The debt accumulated across `§L63`, `§L69`, `§L70`, `§L74`, `§L75` and
`2026-08-22-ada-*` — every one of which landed docs or standalone Python with
the Lean third unrun — is discharged here. This is the lane's **first landing
with Lean in it**, and it carries the full class floor.

### THREE PROCESS FINDINGS, all of them mine

**1. A module no module imports is never elaborated.** Inch 1's first tenure
was GREEN while `Value.lean` had never been compiled: nothing imported it,
and `LeanModels.lean` deliberately does not import the Ada lane. 78 minutes
of queue bought a docs check. `LeanModels/Ada.lean` now imports it, and
`triad.sh --classify-only` names the modules a green actually covers — it
must be re-run AFTER the code is written, not before.

**2. Anchor-span splicing deletes whatever a previous edit put between the
anchors.** The second RED had one root cause: a `python` replace spanning
`"**ADOPT** (Core.Halt)"` … `"An abrupt completion in Ada"` silently removed
the value section a previous splice had inserted between them, so
`IntSubtype`/`EnumSubtype`/`Val` vanished and every other error cascaded from
`Abrupt.ret (value : Option Val)`. **Verify by re-printing the declaration
order**, which is how the fix was confirmed.

**3. `Except` carries no `BEq` in this toolchain.** The third RED was three
guards comparing an `Except` with `==`. Fixed with an `okIs` helper needing
only `BEq Val` — **not** by declaring an orphan `BEq (Except ε α)`, which
would be a global instance added for a local convenience that the next tier
comparing an `Except` would inherit without asking.

### Adoption, deliberately NOT folded in

Core's `Except (Loud π σ)` is in the tree. The by-shape `Loud`/`Halt`/`SemM`
here are marked **ADOPT** and are replaced by imports as their **own ticket**
— mixing a known three-line fix with a real redesign is how a tenure gets
spent proving nothing. `π = ArmRef`; **`σ = Unit`**, per the family default:
*adding a snapshot without a consumer is designing against nothing*, and the
ACATS grader consumes event traces, not states.

**A candidate consumer is registered rather than claimed**: Core's `Loud` arms
discard state, so a refusal mid-test would discard the event-trace rows
already emitted — and a refused test should still yield a PARTIAL trace, not
nothing. That is σ-shaped. But the scoreboard does not exist until inch 5-6,
so there is no consumer today and `Unit` stands. Predicting a consumer is not
having one; the question gets asked at inch 5.

## 2026-08-23-ada-2 — TICKET: adopt Core's outcome layer (π = ArmRef, σ = Unit)

Replace the by-shape `Loud`/`Halt`/`SemM`/refusal-class definitions in
`LeanModels/Ada/Ada2012/Value.lean` (marked **ADOPT** at `:40`, `:66`, `:131`,
`:150`, `:162`, `:310`) with imports of `LeanModels.Core.Outcome`. Kept a
separate ticket from inch 1 deliberately: mixing a known import swap with the
value layer's real decisions is how a tenure gets spent proving nothing.

**Ada currently imports ZERO Core modules** — its entire closure is `Lean`
plus its own files. That is why inch 1's green transferred across a 53-commit
rebase untouched, and adopting ends that property on purpose: after this
ticket, Core changes can break the Ada lane, and Ada's greens stop being
base-independent. That is the price of the shared substrate and it is worth
paying, but it should be paid knowingly.

### The mapping, and why inch 1 had to land first

Core separates two channels, and Ada needs BOTH — which is exactly the
distinction inch 1 spent its guards establishing:

- **`raiseIn` (`ρ`, state-RETAINING)** — `Constraint_Error` and every other
  Ada exception. ARM 11.4: an exception PROPAGATES; the world survives it and
  a handler may observe it. State-retention is not an implementation nicety
  here, it is the language.
- **`refuse` (`π`, state-discarding)** — constructs outside the modelled
  tier. Not `Constraint_Error`, which the ARM defines completely.

Inch 1's load-bearing guard (`!okIs (.int Int8 (-128)) (constrain Int8 128)`)
is what makes this mapping legible: out-of-range RAISES, so it goes on `ρ`.
Had `constrain` refused, the same construct would have landed on `π` and the
adoption would have wired Ada's most common outcome into the give-up channel.

**`π = ArmRef`** — the ARM clause reference, so a refusal says WHICH rule went
unmodelled and the scoreboard buckets on `RefusalCause.className` while the
clause rides in `.detail`, class-blind.

### σ = Unit stands — and the consumer's mechanism ALREADY EXISTS

Per the family default: adding a snapshot without a consumer is designing
against nothing. The registered-not-claimed consumer (a refusal mid-test
should yield a PARTIAL event trace, not nothing) is still hypothetical — the
ACATS scoreboard does not exist until inch 5-6.

**Correction to my own inch-1 note, from reading the current Core.** I wrote
that "Core's `Loud` arms discard state", implying the partial-trace consumer
would need a mechanism built for it. It would not: **`Core.refuseWith`
already carries a snapshot**, and its docstring says it is kept separate from
`refuse` precisely "so that attaching one is a DELIBERATE act at the site that
has the state — and so that the common case cannot accidentally carry one."
So the inch-5 question is narrowed from *"can this be done"* to *"is
`σ = TraceRows` worth it"*, with the mechanism already paid for. Registering
a consumer remains cheaper than predicting one; the question still gets asked
at inch 5, not now.

### Checks this ticket must perform, not assume

- **`okIs` may or may not survive.** It exists because `Except` carries no
  `BEq` in this toolchain. Core ships `instance [BEq π] : BEq (Loud π σ)` —
  on `Loud`, not on `Except` — so the helper is probably still needed.
  **Verify by compiling, not by reading**: 31 guards depend on it.
- **`Halt` vs `HaltWith`.** `Core.Halt = HaltWith Unit Unit` is payload-free;
  Ada needs `HaltWith ArmRef Unit`. The bare `Halt` spelling is the wrong one
  for this lane — an easy and silent mis-adoption.
- **Re-run `--classify-only` AFTER the edit.** Inch 1's first tenure was green
  while `Value.lean` had never compiled, because nothing imported it. The
  build list must still name all three Ada modules afterward.
- **Declaration order.** Anchor-span splicing deleted a whole section during
  inch 1; re-print the order after editing rather than trusting the diff.

### `Core/Order.lean` is NOT part of this ticket

It landed on master since the last read (`FlatLe`, `FlatLe.iff_rel`, the
`FlatOrder` tripwires) and is the extraction step behind `_mono` corollaries.
Ada has no recursion, loops, or fixpoints yet, so there is nothing to
approximate and adopting it now would be a dependency bought for a use that
does not exist. It becomes relevant when the statement tier gets iteration —
inch 3+ — and should be adopted then, by that ticket.

## 2026-08-24-ada-1 — CORE ADOPTION LANDS: the two-channel mapping, and the ticket's own tenure had gone green over a tree that did not contain it

`2026-08-23-ada-2` ticketed this. What follows first is the state that ticket
was left in, because reconstructing it was half the work and the shape of the
mistake is reusable.

### THE PREDECESSOR'S TENURE WAS GREEN, AND IT WAS GREEN ABOUT THE TICKET

The adoption ticket's tenure ran and returned **`TRIAD DONE (build exit 0,
gates green)`** (`/private/tmp/ada-t7.out`, lock acquired after **7,649 s**
queued, full log `$TMPDIR/triad-build.NU6mws`). Read the verdict alone and
the adoption is done. Read the tenure's own header and it is not:

    tree at enqueue: ea56aea0893c        # == git rev-parse 8326457^{tree}
    build exit=0                          # 4 seconds after the lock opened

**The tree it certified was the TICKET COMMIT — docs only.** A 4-second full
build is a build with nothing to do. `LeanModels/Ada/Ada2012/Value.lean` still
imported `LeanModels.Ada.Ast` and nothing else, and all six `ADOPT` markers
were still in it. The green was true and it was **about a different question
than the one the ticket asked**.

> **A GREEN NAMES A TREE. A TICKET NAMES AN INTENTION. Reading the first as
> evidence for the second is how a ticket gets marked done by its own
> paperwork.**

This is §5.4a's unit law meeting §7.2's *"a queued tenure reads the source at
BUILD time"* from the other side: the family already knows a tree can change
out from under a ticket, and this is the case where **it never changed into
it**. The cheap defence is the one this entry uses — a tenure log is
self-identifying, so the header's `tree at enqueue` is checkable against
`git rev-parse <sha>^{tree}` in one command, and the build's *duration* is a
second witness that costs nothing to read.

### THE ADOPTION, and the mapping is the content

`LeanModels/Ada/Ada2012/Value.lean` now imports `LeanModels.Core.Outcome`.
Deleted: the by-shape `RefusalCause` (four constructors), `Loud`, `Halt`,
`SemM`, `Cause.tag`, and `SemM.refuse`/`SemM.timeout`. **π = `ArmRef`**,
**σ = `Unit`**.

| Ada outcome | channel | Core primitive | why |
| --- | --- | --- | --- |
| `Constraint_Error` and every Ada exception | **`ρ` — state-RETAINING** | `raiseIn` | ARM 11.4: an exception PROPAGATES and a handler observes the world it was raised in |
| a construct outside the modelled tier | **`π` — state-discarding** | `refuse` | the model stopped, not the program; there is no world to hand back |

Inch 1 had to land first because its one load-bearing guard is what makes the
mapping legible: `!okIs (.int Int8 (-128)) (constrain Int8 128)` — out of
range RAISES. **Had `constrain` refused, this adoption would have wired Ada's
most common outcome into the give-up channel**, and every rule that can
produce a scalar would have had to be revisited to get it back.

**The mapping is now MEASURED, not described** — five new `#guard`s
(38 total, up from 31):

* the world is written to 42, then `Constraint_Error` is raised, and **42
  comes back through the raise** — an EFFECT surviving, which is a strictly
  stronger claim than an initial world passing through;
* a refusal's **class and ARM paragraph read back as DATA** (`className`,
  `detail`), never parsed out of prose;
* and both negatives: a raise is not a refusal, a refusal is not a raise.

### THE THREE CHECKS THE TICKET SAID TO PERFORM, PERFORMED

1. **`okIs` survives.** Core ships `instance [BEq π] : BEq (Loud π σ)` — on
   `Loud`, **not** on `Except`. `constrain` returns `Except Abrupt Val`, so
   the synthesis failure the helper exists for is untouched and its three
   sites still need it. The ticket was right to flag this one: reading Core's
   instance list suggests the opposite answer, because a `BEq` *does* arrive
   with the adoption — on the type the helper is not about.
2. **`HaltWith ArmRef Unit`, not bare `Halt`.** `Core.Halt` is
   `HaltWith Unit Unit`; adopting it would have compiled and dropped every
   ARM reference at the type level. Made structural rather than remembered:
   `example (W : Type) : AdaM W = ExceptT Abrupt (StateT W AdaHalt) := rfl`.
   The tier's name is **`AdaHalt`** — a local `abbrev Halt` would have
   shadowed Core's inside this namespace and made the wrong one the one a
   reader sees.
3. **Re-classified after the edit**, and the build list is reported as it
   actually came back rather than as the ticket predicted: `tier`, building
   **`LeanModels.Ada.Ada2012.Value LeanModels.Ada`** — two targets, not the
   "three Ada modules" the ticket remembered, because only one file was
   touched and `LeanModels.Ada` pulls the rest of the tier in as imports.
   The failure mode the check exists for is closed either way: the file is
   NAMED, so it cannot go green unelaborated the way inch 1's first tenure
   did.

Declaration order was re-printed after editing rather than trusted to the
diff (anchor-span splicing deleted a whole section during inch 1); every
declaration from `ArmRef` to `orderDependenceGate` is present and in order.

### ADA DOES NOT NARROW THE CAUSE TYPE, and Go is the reason to say so

The Go tier refuses only through a narrower `GoRefusal` with no `undefined`
constructor, so its empty class is unreachable **by construction** — the
right gate for a language whose spec never says "undefined". **Ada's
`undefined` bucket is expected NON-empty** (ARM 1.1.5, 23 paragraphs in
clauses 1-13), so a narrowing type here would delete this tier's product.
Ada refuses through Core's `refuse` directly, all four classes reachable, and
its expected-empty class is a different one — `orderDependence`, gated by
predicate, now written on Core's `RefusalCause.isOrderDependence` rather than
on a local `match`.

**And a convergence worth recording**: `GoM = SemMWith GoWorld Panic SpecRef
Unit` against `AdaM W = SemMWith W Abrupt ArmRef Unit`. **Two tiers, chosen
independently, whose refusal payload is a citation into their own standard.**
That is the family's convergence standard met on the `π` slot, and it is
evidence that `RefusalCause π`'s parameterisation was cut in the right place.

### THE PRICE, PAID KNOWINGLY

Ada's **zero-Core-imports** property is over. It is the reason inch 1's green
survived a 53-commit rebase untouched; from here, a Core change can break this
tier and this tier's greens are no longer base-independent. `Core/Order.lean`
arrives **in the closure** as `Core/Outcome.lean`'s own import — and **in the
closure is not in use**: nothing here mentions `FlatLe`, and the `_mono`
corollaries it backs are adopted by the ticket that gives this tier recursion
(inch 3+), which is exactly where the ticket put them.

### THE VERDICT — GREEN, and this one was checked against its own finding

Ticket `1787523469336706000-94017-adaadopt`, queued **4,812 s**, tenure
`01:39:03-01:39:47`. Log `/tmp/ada-t8.out`, full build log
`$TMPDIR/triad-build.NyvxqG`, whose first line identifies it:
`lane=adaadopt branch=ada-m2-adopt-ticket tree=e547c47b8c32 head=342a1f5`.

| stage | result |
| --- | --- |
| build | `lake build LeanModels.Ada.Ada2012.Value LeanModels.Ada` -> **exit 0** |
| `docs_check` | 91 marked blocks, **91 ok**, 39 illustrative-exempt |
| `diff_test` | **1,464 cases: 0 failed**, 119 whitelisted-unsupported, 1,345 matched |
| `refusal_census --whitelist` | green |
| verdict | **TRIAD DONE (build exit 0, gates green)**, `LOCK RELEASED (mine)` |

**COVERAGE (§5.4a), as the tenure stated it**: scoped — the green covers the
two named modules and everything they IMPORT; it does **not** cover modules
that import them, nor any untouched tier, and it is not evidence about master
beyond that scope. The gate phase additionally built `leanmodels-run`.
Recorded in `.git/triad-greens` as `class=tier citable=yes full=no`, so it is
citable as an increment base with `--since 342a1f5` — and **it does not meet
the merge bar on its own**, because that bar wants a FULL root and this root
is scoped.

#### A REFINEMENT TO THIS ENTRY'S OWN FORENSICS, found by applying them here

This build also finished in **two seconds**, which is the very shape the
predecessor's tenure was convicted on. It is honest, and the difference is not
visible in the tenure summary at all:

    ✔ [7/8] Built    LeanModels.Ada.Ada2012.Value (422ms)
    ✔ [8/8] Built    LeanModels.Ada (720ms)
    ℹ [4/8] Replayed LeanModels.Core.Outcome

> **`Built` versus `Replayed` is the witness that a module ELABORATED.
> Duration is only a corroborator.**

Eight jobs, six of them cache hits — correctly, since `Core/` is byte-identical
between this branch's base and its own predecessor — and 422 ms of real
elaboration, confirmed a third way by both `.olean` files carrying the
tenure's own timestamp. So the checking order is: **tree identity first**
(`git rev-parse <sha>^{tree}` against the log header), **`Built`/`Replayed`
second**, **the clock third**. The predecessor's 4 seconds and this 2 seconds
are indistinguishable at the third check and opposite at the first two.

#### WHAT MOVED UNDER THIS GREEN WHILE IT QUEUED

Master advanced **26 commits** during the 80-minute queue. Measured rather
than assumed, because after adoption Core is in this tier's closure and the
question is no longer rhetorical:

* **Ada's own elaboration closure is UNTOUCHED** — no change under
  `LeanModels/Core/`, `LeanModels/Ada/`, `lakefile.toml` or `lean-toolchain`.
  The build half of this green therefore transfers across a rebase **by
  construction**, which is the first time this tier has been able to say that
  since adoption ended its base-independence.
* **The GATE inputs DID move** — `harness/cases.json`, `harness/refusal_census.py`
  and four `LeanModels/Python/` files. Two of the three gates read those, so
  the **gate** half of this green does not transfer, and a rebase would owe a
  re-gate under §7.2's *a rebase is a merge, and a merge is not a
  measurement*.

So this branch is pushed **exactly as it was gated**, at base `fd96fce`, rather
than rebased into a state nothing has measured.

### NEXT: INCH 2, CENSUS-FIRST

`W` + assignment + sequence + `if` (ARM 5.1-5.3). The census runs before the
rules, per this lane's standing practice, and the standing spec-coverage row
above is what it has to move — which, as the next entry measures, it will not.

## 2026-08-24-ada-2 — INCH 2's CENSUS: 58 ARM paragraphs, 4.05% of the corpus's nodes, and a reach of ZERO said before the rung starts

Inch 2 is `W` + assignment + sequence + `if` (ARM 5.1-5.3;
`docs/ada-semantics-design.md` §3, rung 2). Per §L25's law the rung is a
CENSUS before it is a build, and per §9.0b a reach census does not only rank —
it partially orders, and it can say a rung is worth doing while moving no
number at all. This one says exactly that.

**"ARM 5.1-5.3" IS AN ADA 2012 RANGE.** Stated here and again where the
paragraph counts are, because it is the load-bearing qualifier on every number
below: **a paragraph range is edition-relative**, so a rung scoped by clause
number is scoped in an edition or it is not scoped at all. The tier stays
**Ada 2012**; the spec census stays pinned to **Ada 2022**; the bridge between
them is a corpus measurement, given in full below.

### THE CORPORA ARE GONE FROM THIS MACHINE, and the content-pinned artifacts are why this census still exists

Measured first, because it conditions everything below: **ACATS 4.2, the ARM's
`RM-*.TXT` rendering, and the libadalang toolchain are all absent** — the
scratchpad purge took `adatools/` and both corpora with it
(`docs/ada-toolchain-census.json` still names the vanished path).
`import libadalang` fails; there is no `RM-05.TXT`; there is no `acats42`.

**Every number below is therefore re-derived from git-tracked, content-pinned
census artifacts** — `docs/ada-construct-census.json` (ACATS 4.2, 4,821
sources parsed, 2,976,861 nodes), `docs/ada-suite-census.json` (ACATS 4.2),
`docs/ada-spec-census.json` (the ARM). That is §L86's durability argument
collecting: a corpus pinned by `sha256` and an edition pinned by its own front
matter outlive the directory they were read from. **What cannot be re-derived
is anything the instruments did not already record** — see the one such gap at
the end, which is the rung's real finding.

**THE INSTRUMENTS ARE FINE, AND THEY SAY SO LOUDLY.** Measured, all five
self-tests today:

| instrument | `--self-test` |
| --- | --- |
| `ada_round_trip.py` | **PASSED** |
| `ada_suite_census.py` | **PASSED** |
| `ada_spec_census.py` | **PASSED** |
| `ada_toolchain_census.py` | **PASSED** |
| `ada_construct_census.py` | **REFUSES** — `libadalang is not importable. It is the tier's frontend and there is no fallback for this instrument.` |

Four of five need no corpus and pass. The fifth **refuses rather than
degrading**, and its refusal message carries the acquisition path and the
exact `PYTHONPATH` / `DYLD_LIBRARY_PATH` shape the ctypes bindings need. That
is the never-hide-errors standard paying out at the moment it is tested: a
frontend census with a silent fallback would have produced a smaller number
instead of no number.

**NAMED RUNG: RE-ACQUIRE — a rung, not a background chore.** Nothing is lost,
but the *reproduce it, do not quote it* line at the head of this ledger is
un-runnable on this box, and that is a defect to clear before inch 2 builds.
Its acceptance conditions, so it is not re-done differently next time:

* **PIN BY CONTENT, the way the census JSONs already are.** ACATS 4.2 is
  pinned by its own `ACATS_Version` constant plus a per-file `sha256`, and the
  ARM by the edition read out of its front matter. The rung's job is to make
  the *acquisition* carry the same pins — a manifest of hashes checked on
  fetch — **so the next purge costs a download and not a reconstruction.**
  That is the whole reason this lane stamps no `git_rev`: content pinning is
  strictly stronger for an artifact living outside the repository, and it only
  pays if the fetch checks it.
* **DO NOT VENDOR THE ARM TEXT INTO THE REPOSITORY.** Fetch at the pin, then
  **cite and paraphrase**. The censuses already record everything a reader
  needs — clause id, title, paragraph count, categories present — and those
  are derived facts, not the standard's prose.
* The frontend (`libadalang`, ctypes over a shared library) is a toolchain
  acquisition, and `harness/ada_toolchain_census.py` already carries the exact
  `PYTHONPATH` / `DYLD_LIBRARY_PATH` shape it needs. That instrument's
  `--self-test` passes today, so the path is documented, not lost.

### THE SPEC SIDE — 58 paragraphs, and `if` is nearly free

From `docs/ada-spec-census.json`, the three subclauses inch 2 owns. **The
range is Ada 2012's; a paragraph range is edition-relative** (the counts are
read off the 2022 census, and the next section is why that is sound here):

| ARM | title | paragraphs | rule categories present |
| --- | --- | ---: | --- |
| 5.1 | Simple and Compound Statements - Sequences of Statements | 23 | Syntax, Name Resolution, Legality, **Static Semantics**, Dynamic Semantics, **Bounded (Run-Time) Errors**, Examples |
| 5.2 | Assignment Statements | 28 | Syntax, Name Resolution, Legality, Dynamic Semantics, Examples |
| 5.3 | If Statements | 7 | **Syntax, Dynamic Semantics, Examples — and nothing else** |
| | **inch 2 total** | **58** | |

**`if` costs almost nothing and it is the most common of the three.** Seven
paragraphs, no Legality Rules, no Name Resolution Rules, no Static Semantics:
the ARM has essentially one dynamic rule to state. The expensive one is 5.2 at
28 paragraphs, and its cost is not the write — it is the TARGET (below).

**ARM 5.1 CARRIES A BOUNDED (RUN-TIME) ERROR, so §1.4's machinery goes live at
inch 2 rather than at some later rung.** The design already fixed the shape:
a bounded-error site carries its **permitted set as a per-site datum**, the
verdict is `obs (run …) ∈ permitted site`, and **never `⊕`** — outcome
conjunction carries an `S ≠ ∅` side condition that turns a permission into an
obligation, which is strictly stronger and, for Ada, false. Inch 2 is where
that stops being a design note. Scale for the whole modelled slice: **57
Bounded (Run-Time) Errors paragraphs in clauses 1-13**, 104 document-wide.

### THE EDITION HAZARD, and the corpus settles it without the ARM

**The spec census is pinned to Ada 2022 (ISO/IEC 8652:2023); the tier's
meaning layer is Ada 2012** (`LeanModels/Ada/Ada2012/`, ACATS 4.2). In clause
5 the editions differ, and one of the differences sits **inside inch 2's
nominal range**:

* **5.2.1 Target Name Symbols** (the `@` of an assignment target), 8
  paragraphs — numbered between 5.2 and 5.3;
* 5.5.3 Procedural Iterators, 37 paragraphs;
* 5.6.1 Parallel Block Statements, 9 paragraphs.

Reading "ARM 5.1-5.3" off the 2022 census would have pulled 5.2.1 into the
rung. **The corpus settles it without needing the 2012 RM text**: libadalang
26 parses Ada 2022 and has a `TargetName` node for `@`, and the construct
census records **zero `TargetName` nodes in 4,821 ACATS sources** — along with
zero `DeclExpr`, zero `ReduceAttributeRef`, zero `ParallelLoopStmt` and zero
`ParallelBlockStmt`. The absence is a fact about the corpus, not about the
parser's vocabulary.

> **5.2.1 is out of inch 2 BY MEASUREMENT, not by assertion**, and the general
> rule it instances is the family's whole versioned-surface premise arriving
> at its smallest possible scale: **a paragraph range is edition-relative, so
> a rung scoped by clause number is scoped in an edition or it is not scoped.**

### THE CORPUS SIDE — 4.05% of nodes, and `if` outnumbers assignment

From `docs/ada-construct-census.json`, ACATS 4.2 entire (4,821 of 4,973
sources parsed; the 152 with diagnostics are class B tests, which contain
deliberate illegalities and are the corpus working as designed):

| node kind | count | ARM |
| --- | ---: | --- |
| `StmtList` | 67,520 | 5.1 |
| `IfStmt` | 21,260 | 5.3 |
| `AssignStmt` | 20,529 | 5.2 |
| `NullStmt` | 8,031 | 5.1 |
| `ElsePart` | 2,236 | 5.3 |
| `ElsifStmtPart` | 987 | 5.3 |
| **inch-2 vocabulary** | **120,563** | **4.05% of 2,976,861 nodes** |

**`if` outnumbers assignment**, 21,260 to 20,529, which is the opposite of
most corpora and is a fact about what ACATS IS: a suite whose dominant idiom
is *check a condition, then report failure*. The cheapest subclause in the
ARM is the most frequent construct in the corpus, so **5.3 is the rung's best
ratio by a wide margin** and should be written first.

**Only 987 `elsif` parts against 21,260 `if`s** — 4.6%. `elsif` is a
list-shaped tail on the rule and costs one recursion; it is not a separate
decision.

**What is NOT in the rung, at the scale it is not in the rung:**

| out-of-tier neighbour | count | wants |
| --- | ---: | --- |
| `CallStmt` | 56,062 | inch 3 (frame, `return`) |
| `HandledStmts` | 26,386 | inch 4 (handlers, propagation) |
| `CallExpr` | 96,592 | inch 3 — **or arrays; see below** |

`CallStmt` outnumbers `AssignStmt` **2.7 to 1**. A statement walker that
handles 5.1-5.3 and refuses calls will refuse the most common statement in the
corpus, which is expected and is the reason the reach below is zero.

### THE REACH IS ZERO, and saying so first is the point

`docs/ada-suite-census.json`: the v0 target is **1,374 tests**, and **all
1,374 use `Report`**. `Report` is a package of 15 subprograms; reaching it
needs subprogram calls (inch 3) and the native `Report` model (inch 5). So:

> **Inch 2 moves the standing spec-coverage row by exactly 0 tests, and it was
> never going to move it.**

That is recorded BEFORE the rung is built, not after it disappoints. §9.0's
guard — *a mechanism rung that unlocks nothing must not be allowed to look
like progress* — applies to a rung's PLAN as much as to its table, and the Go
lane's `+0` row is the precedent. Inch 2 is on the critical path to inch 6's
517 tests through inches 3, 4 and 5; it is not a coverage rung and must not be
sold as one.

### `W` AT INCH 2 — one component live, four declared

`docs/ada-semantics-design.md` §1.1 fixes four components, and the rung's job
is to land the STRUCTURE with only the first written:

* **`objects`** — LIVE. Assignment writes it; a scoped map of named objects,
  **not** a byte-addressed heap (v0 has no `'Address` pressure — Clause 13 is
  out of v0 and the 1,374-test target reaches it nowhere).
* **`elaborated`** — declared, unwritten until inch 9. It is data the tier was
  handed rather than derived: §L74 measured that **680 of 4,810 files, one in
  seven, have a name that is not among their unit names**, so the order cannot
  be re-derived from paths.
* **`output`** — declared, unwritten until `Report` lands at inch 5.
* **`trace`** — declared, and **it must be in `W` from the first statement
  rule**. The scoreboard emits the ACAA's `CSTART/CEND/CERR/...` rows and lets
  `GRADE` decide; an emitter is not retrofittable, and every span a `CERR` row
  needs (`line`, `col`, `endLine`, `endCol`) is already on every envelope node.

### THE ONE MEASUREMENT THE INSTRUMENTS CANNOT MAKE — and it is inch 2's real decision

**What SHAPE does an assignment target take?** ARM 5.2's `assignment_statement`
is `variable_name := expression`, and `variable_name` ranges over a simple
name (in the rung), an indexed component (arrays — not in the rung), a
selected component (records — not in the rung), and a dereference
(access types — inch 8). The split decides how much of the 20,529 assignments
inch 2 honestly covers and how many it must refuse.

**`docs/ada-construct-census.json` cannot answer it.** It is a flat
kind-frequency map — 280 distinct kinds, no parent-child structure — so it
knows there are 20,529 `AssignStmt` and 654,029 `Identifier` and cannot pair
them. And the ambiguity is not incidental: **`CallExpr` (96,592, the
second-most-frequent kind) is libadalang's node for BOTH a function call and
an indexed component**, so even a parent-child pass has to disambiguate by
resolution, not by kind.

> **A frequency census ranks constructs; it cannot answer a question about
> a construct's ARGUMENT.** That is §9.0's discriminator law in the shape this
> tier meets it — and unlike Go's case, the corpus DOES have the witness. It
> just is not in the recorded output.

**NAMED RUNG, and it precedes the build:** extend
`harness/ada_construct_census.py` to record, for each `AssignStmt`, the KIND
of its target child (and for `CallExpr`, whether it resolves to a subprogram),
then re-run it. That needs the re-acquisition rung above. Until it runs, inch
2's assignment rule should be written to **refuse every non-simple-name
target with `RefusalCause.unsupported` citing ARM 5.2**, which is honest, is
countable, and turns the missing measurement into a number the next census
reads off the model itself.

### THE BUILD ORDER, and one line that rides with the rung

**5.3 FIRST, and the corpus is the argument.** Seven ARM paragraphs with no
Legality Rules and no Name Resolution Rules, against **21,260 `IfStmt`** — the
cheapest subclause in the range is the most frequent construct in the corpus.
Then 5.1 (sequences, `null`, and the bounded-error site), then 5.2 (the
assignment, whose cost is the target rather than the rule).

**5.1's BOUNDED (RUN-TIME) ERROR is written as a MEMBERSHIP site, never as
`⊕`** (§1.4): the site carries its permitted set as a per-site datum and the
verdict is `obs (run …) ∈ permitted site`, with equality as the singleton
case. Outcome conjunction carries an `S ≠ ∅` side condition that converts a
permission into an obligation — strictly stronger, and for Ada false.

**5.2 REFUSES EVERY NON-SIMPLE-NAME TARGET**, with
`RefusalCause.unsupported` citing ARM 5.2, until the target-child-kind census
extension has run. This is deliberate and is not a gap being papered over:
**a refusal is how a pending measurement is carried in the model rather than
in a note.** It is honest (the tier is not claiming to assign into an array it
has not modelled), it is countable, and the next census reads the number off
the model itself instead of re-deriving it from the corpus.

**AND ONE LINE RIDES WITH THIS RUNG, NOT A TENURE OF ITS OWN:**

    LeanModels.lean:  import LeanModels.Ada

`LeanModels.lean` does not import the Ada tier. The tier reaches the default
build **only** through `Examples/ada/report/guards.lean` under the `Examples.+`
glob — so a tier whose Examples fixture is ever pruned **silently leaves the
build**, and nothing goes red at the moment it happens. That is the
POINTED-versus-DECLARED ladder with a live rung missing: the tier is *reached*,
but it is not *declared*, and only the second survives a fixture being moved.

**Its price, stated before it is paid.** `LeanModels.lean` is in the **spine**
class (`tools/triad.sh`: *"spine — `LeanModels.lean`, `LeanModels/Core/`, the
shared harness, the lakefile → the full build"*), so the landing that carries
this one line is a FULL build rather than a scoped tier build. Amendment 14
makes a full-tree build **quiet-machine-only — load < 5 and swap < 1 GB** —
and at drafting the box is at **load 6.67 with 8,714 MB of swap in use**. So
the line is scheduled, not squeezed in: it rides the inch-2 landing when the
machine is quiet, and if the machine is not quiet at that moment it waits
rather than converting a tier green into a red full build. A14's own
correction applies if that happens — **after a red, the next build is FULL
again**, because a scoped build extends a green and never recovers from a red.

**AND THE TWO QUIET-WINDOW ITEMS ARE THE SAME WINDOW, so they ride together.**
This tier cannot produce a **full** green until the box is quiet, and it needs
one for two independent reasons that arrived within the hour: the spine line
above is spine-class by construction, and — measured today — **§5.4a-i's
increment chain REFUSES TO START ON A SCOPED ROOT.** Asked to classify a
two-file docs increment against the adoption's tier green, `tools/triad.sh`
answered:

    the green at 342a1f582d9d has NO RESOLVABLE ROOT: it was itself a scoped green
    with no full build under it, so there is nothing sound to classify the increment
    against (§5.4a-i: against the ROOT, never the parent). Take one full green first.

That refusal is the machinery working. A scoped green admits it does not cover
modules importing what it built; chaining onto it would convert an admitted
partial into an unstated one. **So this lane holds no chained evidence, and
does not claim any**: the landing that carries this census is `docs` class on
its own merits — `git diff --name-only 342a1f5 HEAD` is two `.md` files,
nothing in it can change elaboration, and the class's gate (`docs_check`,
91/91 marked blocks, plus `backlog-index.sh --check` in sync) is the whole
gate it owes. One full green in a quiet window retires both items at once.

## 2026-08-24-ada-3 — INCH 2 LANDS: `W` and ARM 5.1-5.3, and the census caught a trap that reads as a semantics bug

`LeanModels/Ada/Ada2012/Stmt.lean`, 695 lines, plus two widenings to
`Value.lean`. The rung was censused first (§2026-08-24-ada-2) and built to
that census: **5.3 first on the corpus's own ratio**, the bounded-error
membership machinery at 5.1, and non-simple assignment targets refused.

### THE FINDING: AN EMPTY LIST IS A LEAF, NOT AN EMPTY NODE

`extractors/ada/extract.py` emits `children` when a node has children and
`text` otherwise. So an `if` with no `elsif` carries its `ElsifStmtPartList`
as a **leaf with empty text** — and **30 of the 31 in the two fixtures are
leaves**.

> **A walker written from the GRAMMAR would match `.node "ElsifStmtPartList"
> _ #[]`, hit ONE `if` in thirty-one, and refuse the rest — and the refusal
> would read as a missing semantics rather than as a wrong encoding.**

That is the sharpest argument for census-first this lane has produced,
because the failure is silent in exactly the way a refusal is *supposed* to
be safe: the model would have said *"I do not model this"* about a construct
it fully modelled. Cross-checked on the else slot by arithmetic: 31 `IfStmt`
minus 9 `ElsePart` is exactly the 22 `null` children the extractor emits under
`IfStmt`.

**Every node shape in the walker was read off `report.json` and
`b371001.json` (3,505 nodes) with a script, not recalled**: `AssignStmt` is
2 children (49 of 49), `IfStmt` is 4 (31 of 31), `ElsifStmtPart` 2, `ElsePart`
1, `BinOp`/`RelationOp` 3 with the **operator as the middle child**, `UnOp` 2,
and `Identifier`/`IntLiteral` are leaves carrying source text.

### `partial` IS OPAQUE TO THE KERNEL, so the whole tier is fuel-structural

`Ast.lean`'s own walkers are `partial`, and a `#guard` stated through a
`partial` definition **cannot reduce** — the ES lane recorded the same fact
about its JSON layer. So every function here is **structurally recursive on
`fuel`**, which is the family's fuel-is-an-index rule paying a second dividend
beyond termination: it is what lets the gate RUN the interpreter instead of
admiring it. `termination_by` is deliberately absent — adding it would force
well-founded recursion and take kernel reduction away again.

**`execStmts` is ONE function over a statement LIST**, not a mutual pair, and
`elsif` is handled by **LOWERING**: ARM 5.3's `elsif` is a nested `if`, so the
rule rebuilds it as one and re-enters the same function. Two guards pin the
lowering — the elsif branch runs when it matches, and the else part survives
the rebuild when no elsif matches.

### THE INCH-1 DECISION NOW FIRES THROUGH A STATEMENT RULE

ARM 5.2 converts the value to the TARGET's subtype and checks the constraint.
`X := 200` into an `Int8` **raises `Constraint_Error`** — it does not wrap and
does not refuse — and because a raise travels on `ρ`, the guard checks that
**the world SURVIVES**: `x` still holds its old value and the trace still
holds its row. That is the adoption's two-channel mapping doing its job one
layer up, and `ofAbrupt` is the single place inch 1's pure `Except Abrupt`
decisions are lifted onto `ρ`.

**The arithmetic is inch 1's, and that is proved rather than asserted** —
five `rfl` examples pin `applyArith` against `addOp`, `subOp`, `mulOp` and
`divOp` at a known subtype, so this is not a second implementation that
happens to agree.

**`Val.univInt` is new, and it is the ARM's own concept.** ARM 3.5.4: an
integer literal is of type *universal_integer*, implicitly converted at its
point of use. `X := 5` cannot be written without saying what `5` is, and
giving the literal a subtype at the literal would decide the conversion before
the semantics could see it — the same error `Ast.lean` avoids by keeping a
literal's source spelling.

### THREE DECISIONS WHERE THE SOURCE OF THE FACT IS STATED

**1. Case folding is a STANDARD fact with a NEGATIVE corpus measurement.** ARM
2.3 makes identifiers case-insensitive, so every lookup and store folds. But
across both fixtures there are **131 distinct case-folded identifiers and ZERO
spelled in more than one case** — so this came from the standard, not from the
corpus, and the entry says which. The witness should exist corpus-wide (ACATS
legacy tests are upper-case, modern ones mixed); checking it belongs to the
re-acquire rung. The fixtures write `X` while the store holds `x`, so every
guard exercises the fold.

**2. A citation whose paragraph could not be checked cites the CLAUSE and
says so BY SHAPE.** The ARM text is not on this machine, so `ArmRef.toString`
was widened: an empty `para` renders as the bare clause. Inch 1 had the text
and cites `1.1.5(9)`; inch 2 does not and cites `5.2`. **Guessing a paragraph
number would have been indistinguishable from having checked one.**

**3. THE EVALUATION ORDER IS UNOBSERVABLE AT THIS VOCABULARY, which is why
fixing one is sound here.** Ada leaves operand order unspecified — normally an
`orderDependence` question. But every expression form in inch 2's vocabulary
is side-effect-free, because the one form that could have an effect is a
function call and calls are refused until inch 3. **No program in this
fragment can observe the order this file happens to evaluate in.** The
question becomes live exactly when calls arrive, and inch 3 owes the answer.
That is the `orderDependence` gate acquiring its first real content: it is
empty here for a reason that can be stated, not merely because nothing has
emitted one yet.

### THE BOUNDED-SITE MACHINERY IS PRESENT AND GATED, WITH NO SITE

`BoundedSite α` carries its permitted set as a per-site datum and
`admits` is MEMBERSHIP — equality is the singleton case, and **never `⊕`**,
whose `S ≠ ∅` side condition converts a permission into an obligation.
**No ARM 5.1 site is instantiated**: the permitted set is a fact about the
ARM's text and the ARM's text is not here. Writing one from memory is exactly
what decision 2 above exists to prevent. So the type is present and gated,
the same discipline the `RefusalCause` ruling applies to an expected-empty
class — a gate needs something to be about. Scale for when the text returns:
**57 Bounded (Run-Time) Errors paragraphs in clauses 1-13**.

### THE SPINE LINE IS DEFERRED, WITH THE MEASUREMENT

`import LeanModels.Ada` into `LeanModels.lean` was to ride this landing.
`LeanModels.lean` is **spine** class, so it makes the landing a FULL build,
and A14 makes a full build quiet-machine-only at **load < 5 AND swap < 1 GB**.
Checked at ticket time rather than assumed:

    load averages: 3.94   swap used: 8,077 MB

**Load passes; swap fails by eight times.** Both conditions are required, so
the line waits. It is not dropped — the tier still reaches the default build
only through the `Examples.+` glob, so a pruned fixture would drop it
silently, and that is the POINTED-versus-DECLARED rung still open. It rides
the next landing that opens a quiet window, together with the FULL green that
§5.4a-i's increment chain needs before it can start on this lane at all.

### THE NUMBER IS STILL ZERO, AND IT WAS PREDICTED

The standing coverage row moves by **0 tests**, exactly as the census said it
would before the rung was built. All 1,374 v0 tests call `Report`, which needs
inch 3 (calls, frames) and inch 5 (the native `Report` and the trace emitter).
Inch 2 is on the critical path to inch 6's 517 tests; it is not a coverage
rung and is not recorded as one.

## 2026-08-24-ada-4 — THE TARGET-SHAPE RUNG ANSWERS, and the answer is that 5.2's refusal was never blocked on the measurement

`harness/ada_construct_census.py` gains the child-kind measurement the census
named as a prerequisite (§2026-08-24-ada-2) and inch 2's ARM 5.2 rule refuses
against (§2026-08-24-ada-3). **The rung ran, and it retires an uncertainty
rather than unlocking code** — which is a better outcome than it sounds, and
the reason is the finding.

### THE NUMBER — ARM 5.2 assignment targets

Measured over the two content-pinned envelopes (3,505 nodes, 49 assignments):

| target shape | count | share | status in inch 2 |
| --- | ---: | ---: | --- |
| `Identifier` — a simple name | **41** | **83.7%** | **modelled** |
| `CallExpr` | 6 | 12.2% | refused |
| `DottedName` — a selected component | 2 | 4.1% | refused |

**This is a SAMPLE, not the corpus.** 49 assignments against the corpus's
20,529, from the two fixtures the hazard census picked — so it is a first
number with the denominator named, and the corpus figure needs the SOURCES
path and therefore the re-acquire rung.

### THE FINDING: THE REFUSAL WAS BLOCKED ON VALUES, NOT ON SHAPES

The rung was scheduled as *"the named rung before 5.2's assignment rule can
widen."* The measurement says the rule **should not widen yet, for a reason
the shape census could not have been expected to give**:

> **The 16.3% inch 2 refuses are not a target-SHAPE gap. A `DottedName`
> target is a record field and a `CallExpr` target is an array element — so
> collecting them needs RECORD and ARRAY VALUES, which this tier does not
> have at all.**

Widening the target pattern without them would produce a rule that recognises
`A (I) := X` and then has nothing to store into. **The refusal stays exactly
where it is, and it is now a refusal with a measured price (16.3% of a
49-assignment sample) instead of an unmeasured one.** That is what the
refusal-as-pending-measurement move was for: the pending measurement came
back, and it re-aimed the next rung from *widen 5.2* to *composite values*.

### AND THE COLUMN A SHAPE CENSUS CANNOT PRODUCE, kept separate

`CallExpr` is libadalang's node for **both a function call and an indexed
component**, so the six above are ambiguous *by shape*. The SOURCES path now
records a `target_resolution` column (`resolve_target`) which the envelope
path deliberately does not have — and the envelope document **says what it
cannot answer in its own `frontend` field** rather than letting a reader
assume the columns mean the same thing.

**The expectation to CHECK when it runs, stated as an expectation:** Ada's
legality rules make a function call ineligible as an assignment target, so all
six should resolve to indexed components or slices. If any resolves to a
subprogram, that is a finding about the corpus or about the instrument, and it
is exactly what a resolution column is for. It is not asserted here.

**A resolution FAILURE is recorded as data, never swallowed** — the
exception's class name becomes the bucket, so a corpus where resolution
routinely fails reports that fact instead of quietly shrinking its own
denominator.

### THE SAME RUN VALIDATED INCH 2's `IfStmt` SHAPES, PER SLOT

The walker's shapes were read off the fixtures by hand; this measures them:

| `IfStmt` slot | measured |
| --- | --- |
| `condition` | `RelationOp` 13, `Identifier` 10, `CallExpr` 6, `BinOp` 1, `UnOp` 1 |
| `then` | `StmtList` 31 — **uniform** |
| `elsif_parts` | `ElsifStmtPartList` 31 — **uniform** |
| `else_part` | `Absent` **22**, `ElsePart` **9** |

The else-slot split is **exactly the 22/9 that inch 2 derived by arithmetic**
(31 `IfStmt` minus 9 `ElsePart`) — now measured directly rather than inferred.
And inch 2's condition vocabulary covers **25 of 31 (80.6%)**; the six it
refuses are `CallExpr`, which is inch 3's.

**The empty-list-as-a-leaf trap, quantified:** `ElsifStmtPartList` arity is
`{leaf: 30, 2: 1}` and `AssocList` is `{leaf: 35, ...}` — so the encoding is
GENERAL, not an elsif quirk, and any future walker over a list-shaped node
meets it.

### WHAT THE INSTRUMENT GAINED, and one thing it can now do without a frontend

* `child_kinds` on both paths: for nine parent kinds, the kind distribution of
  every child SLOT — the parent-child structure the flat map lacked.
* `arity_by_kind`, which is what makes the leaf-vs-node encoding visible.
* `--envelope`, a second input path reading `ada-0.1` envelopes. **Not a
  degraded fallback: it answers a strictly smaller question and labels which
  one.** It exists because the corpus and the frontend are both off this
  machine while the envelopes are content-pinned and in the tree.
* `--compare` now **refuses across measurement kinds** rather than
  subtracting two documents that answer different questions — §5.4a's unit
  family in miniature, where the numbers would subtract cleanly and mean
  nothing.
* `--self-test-envelope`, which **needs no frontend and passes 7/7 here**. The
  full `--self-test` still REFUSES without libadalang and is deliberately not
  softened into a skip: a gate whose main half cannot run does not get to
  report success.

### NEXT

Inch 3 — calls, the frame, `return` (ARM 6.5) — which also owes the
`orderDependence` gate its first real content, because a call is the first
expression form in this tier that can have an effect and therefore the first
one whose operand order is observable.

## 2026-08-24-ada-5 — INCH 3's CENSUS: 178 paragraphs, 16.39% of the corpus, and BOTH of this tier's empty refusal classes get their first real site

Inch 3 is calls, the frame and `return` (ARM 6.1, 6.3, 6.4, 6.4.1, 6.5;
`docs/ada-semantics-design.md` §3 rung 3). Census before build, per §L25.
**The range is Ada 2012's** — a paragraph range is edition-relative, and the
counts below are read off the Ada 2022 census with that qualifier standing.

### IT IS A MUCH BIGGER RUNG THAN INCH 2, ON BOTH AXES

| | inch 2 (5.1-5.3) | inch 3 (6.1, 6.3, 6.4, 6.4.1, 6.5) |
| --- | ---: | ---: |
| ARM paragraphs | 58 | **178** — 3.1× |
| corpus nodes | 120,563 (4.05%) | **487,784 (16.39%)** — 4.0× |

The paragraph weight is not where a reader would guess. **6.4.1 Parameter
Associations is 51 paragraphs — bigger than 6.4 Subprogram Calls (32) and
bigger than 6.5 Return Statements (35).** Binding arguments to parameters is
the expensive half of a call in Ada, and 6.3 Subprogram Bodies is a mere 11.

Node counts (ACATS 4.2): `AssocList` 139,001, `ParamAssoc` 132,134,
`CallExpr` 96,592, `CallStmt` 56,062, `SubpSpec` 23,655, `ParamSpec` 22,000,
`SubpBody` 13,438, `ReturnStmt` 4,902, `ExtendedReturnStmt` 503.

> **The two association kinds together (271,135) outnumber the call kinds
> (152,654) by 1.8 to 1.** The census's own shape says the same thing the
> paragraph count does: inch 3's work is in the ARGUMENTS, not in the call.

### BOTH EMPTY REFUSAL CLASSES GET THEIR FIRST REAL SITE HERE

This is the finding that re-prices the rung, and it comes from the category
column rather than from the counts:

* **`orderDependence` — ARM 6.4.1.** Inch 2 recorded that its evaluation
  order was *unobservable* because every expression form in its vocabulary is
  side-effect-free, and that **the question becomes live exactly when calls
  arrive**. It arrives here: a call's parameters may be evaluated in any
  order, and a function call can have an effect. So the gate this lane wrote
  in inch 1 (`orderDependenceGate`, present and expected-empty) meets its
  first candidate site at exactly the rung inch 2 predicted.
* **`undefined` — ARM 6.4.1 carries an ERRONEOUS EXECUTION category.**
  Measured from `docs/ada-spec-census.json`'s own category list. This tier's
  `undefined` bucket is expected NON-empty (ARM 1.1.5, 23 paragraphs in
  clauses 1-13) and it has had no site until now. **6.4.1 is the first.**

**And a third, one subclause outside the rung's range: ARM 6.2 Formal
Parameter Modes carries a BOUNDED (RUN-TIME) ERRORS category** — 15
paragraphs. The `BoundedSite` machinery landed at inch 2 present-and-gated
with no instance because the ARM text is absent; 6.2 is the nearest candidate
instance and it is adjacent to this rung rather than in it. Recorded so the
re-acquire rung knows which subclause to read first.

### THE SHAPES ARE ALREADY MEASURED, and one of them is the inch-2 trap again

The child-kind instrument (§2026-08-24-ada-4) already recorded inch 3's slots:

| slot | measured |
| --- | --- |
| `CallStmt.name` | `CallExpr` **32 of 32 — uniform** |
| `CallExpr.name` | `Identifier` 103, `DottedName` 12, `AttributeRef` 9 |
| `CallExpr.suffix` | `AssocList` 104, **`BinOp` 20** |
| `AssocList` arity | **`leaf` 35**, 1 → 95, 2 → 27, 3 → 2, 5 → 1 |

Two things to build against:

**1. A ZERO-ARGUMENT CALL'S `AssocList` IS A LEAF — 35 of 160.** The same
encoding that would have made a walker refuse 30 of 31 `if` statements will
make one refuse every parameterless call, and `P;` is the commonest call
shape there is. Inch 2 paid to learn this once; inch 3 gets it for free, and
that is what a census artifact is for.

**2. `CallExpr.suffix` IS NOT ALWAYS AN ARGUMENT LIST.** 20 of 124 are
`BinOp` — a range or slice (`A (1 .. 10)`), which is `OpDoubleDot` at 13,740
corpus-wide. So the suffix slot is overloaded three ways: arguments, an
index, and a slice. **This is the `CallExpr` ambiguity from §2026-08-24-ada-4
reappearing on the other side**: there it made an assignment target
undecidable by shape, here it makes a call's suffix undecidable by shape. The
`target_resolution` column generalises to a `suffix_resolution` one, and both
wait on the same re-acquire rung.

### THE REACH IS STILL ZERO, and this time it is worth saying why precisely

Inch 3 gives the tier calls — and **all 1,374 v0 tests call `Report`**, which
is a package the tier must MODEL rather than execute (inch 5). So having the
call mechanism does not by itself execute one test: the callee has to exist.
The coverage row moves at **inch 6**, and inches 3, 4 and 5 are each necessary
and none sufficient. Said before the rung is built, as with inch 2.

### THE PLAN

`W` gains a frame stack; `ρ` already has `.ret (value : Option Val)` from inch
1, so `return` is a raise that a call FRAME catches — which is the same
two-channel mapping again and needs no new machinery. Core's `zoomIn`/`zoomOut`
are the state boundary for a call running in a smaller world, and they are
already imported. The rung's real work is 6.4.1: named and positional
associations, and the default expressions a missing argument takes.

**`Core/Order.lean` becomes relevant at this rung and not before.** The
adoption ticket parked it with a reason: `FlatLe` backs the `_mono`
corollaries and Ada had no recursion. A call is recursion. It is in the
closure already (Outcome imports it); this is the rung that may put it to use.

## 2026-08-24-ada-6 — INCH 3 BUILDS: calls, the frame, `return` — and `orderDependence` EMITS for the first time

`LeanModels/Ada/Ada2012/Stmt.lean` grows to 1,106 lines and 54 guards. Built
to §2026-08-24-ada-5's census, on the Go tier's shape.

**The first tenure came back RED on ONE guard, and it was the right guard
to lose.** Inch 2 pinned *`CallStmt` refuses at ARM 5.1 — 56,062 nodes, and
it is inch 3's*. Inch 3 made that false, so the guard failed:

    Expression
      refusedAtClause "5.1" [Node.node "CallStmt" sp0 #[ident "P"]]
    did not evaluate to `true`

> **A guard that pins a REFUSAL must go red the moment the frontier moves
> past it, or the tier keeps claiming not to model something it models.**

That is the whole value of writing refusals as guards rather than as prose:
the gate, not a reviewer, noticed that a claim had expired. The witness
moved to a kind still genuinely out of tier (`CaseStmt`, ARM 5.4, inch
7's) and a second guard records that `CallStmt` now refuses one step
further in, at ARM 6.4, when its child is not a call — so the arm stays
non-vacuous and only its clause moved. **52 of 53 guards passed on the
first compile**, including the whole mutual block, the frame machinery and
the order-dependence emission.

### THE STRUCTURE IS BORROWED, DELIBERATELY

`LeanModels/Go/Stmt.lean` is a `mutual` over `evalExpr`/`evalArgs`/
`evalCallValues`/`execStmt`, **fuel-indexed, with the function table as a
leading PARAMETER and no `termination_by`**. Inch 3 is the same five-function
shape — `evalExpr`, `callExpr`, `evalArgs`, `callSubp`, `execStmts` — for the
same reasons, and the absence of `termination_by` is load-bearing: it would
force well-founded recursion and take the gate's kernel reduction away, which
is the trap inch 2 recorded about `partial`. The C tier's `Expr.lean` measures
on AST size instead; this tier cannot afford to.

**The table is a PARAMETER, not `W`.** A subprogram body is program text, and
putting text in the world would make elaboration look like a side effect. Go
decided this first; Ada follows rather than re-deciding.

### WHAT A FRAME ABSORBS — the two-channel mapping at the call boundary

`inFrame` is the whole of it, and its three arms are three different laws:

* **`.ret` is CAUGHT.** That is what a frame is FOR (ARM 6.5) — and it needed
  **no new machinery**, because inch 1 already put `.ret` in `Abrupt`.
* **Any other exception PROPAGATES, and the frame is POPPED anyway.** ARM
  11.4: an exception leaving a subprogram still leaves it. Guarded both ways.
* **A refusal does not come back at all.** There is no world on `π` — it is
  the state-discarding channel — so there is nothing to pop. **A `π` arm that
  restored a world would be inventing one.**

### THE ORDER-DEPENDENCE GATE EMITS, exactly at the rung inch 2 predicted

Inch 2 recorded that its evaluation order was unobservable *because every form
in its vocabulary is side-effect-free, and the question becomes live exactly
when calls arrive*. It arrives:

> **Two or more arguments, and at least one contains a call → REFUSE with
> `RefusalCause.orderDependence` citing ARM 6.4.1.**

ARM 6.4.1 leaves the order unspecified and a call can have an effect, so the
model **refuses rather than picking an order and calling it the language**.
This is the first `orderDependence` emission in the tier, and it makes inch
1's `orderDependenceGate` — written expecting an empty bucket — non-vacuous
for the first time. Both directions are guarded: it fires on the ambiguous
shape and **does not** fire on one argument or on several with no call among
them, because a gate that refused those would be refusing the language rather
than the model's limit.

`containsCall` answers **`true` out of fuel**, because its only consumer
refuses on `true` and a refusal is the safe direction — a budget-exhausted
"no" would silently license the very order-dependence it exists to catch.

### THE CENSUS PAID FOR ITSELF TWICE

* **A parameterless call's argument list is a LEAF** (35 of 160). `P;` is the
  commonest call shape there is, and a walker matching only `.node "AssocList"`
  would have refused every one. Inch 2 paid to learn this encoding; inch 3
  handled it on the first try and guards it.
* **A `CallExpr` suffix is not always an argument list** — 20 of 124 are
  `BinOp`, a range or slice. Refused citing ARM 4.1.2 rather than read as
  arguments.

### THE SLICE, AND EVERY EXCLUSION CITES ITS CLAUSE

Positional associations only (**named refuses, 6.4.1**); `in` mode only
(**`out`/`in out` refuse, 6.2** — the subclause that also carries the Bounded
Errors category, so the next rung starts there); simple-name callees only
(`DottedName`/`AttributeRef` refuse, 6.4); no default expressions (an arity
mismatch refuses, 6.4.1).

The table BUILDER (`subpOf`, `collectSubps`) is guarded **apart from** the
call rules, so a red says which of the two is wrong — and one guard closes the
loop by driving the walker from a table the builder produced.

### THE NUMBER IS STILL ZERO

ACATS **0 / 4,188** and **0 / 3,996**. Inch 3 gives calls; the 1,374 v0 tests
call `Report`, which must be MODELLED (inch 5). The row moves at inch 6.

## 2026-08-24-ada-7 — INCH 4's CENSUS: the CHEAPEST rung so far, and it is the one that unlocks the first scorable set

Inch 4 is exceptions — raise, handlers, propagation (ARM 11.1-11.4, 11.4.1).
Census before build, per §L25. **The range is Ada 2012's**; a paragraph range
is edition-relative.

### COST AND VALUE ARE INVERTED HERE, and that is the scheduling finding

| rung | ARM paragraphs | corpus nodes | unlocks |
| --- | ---: | ---: | --- |
| inch 2 (5.1-5.3) | 58 | 120,563 (4.05%) | 0 tests |
| inch 3 (6.1-6.5) | 178 | 487,784 (16.39%) | 0 tests |
| **inch 4 (11.1-11.4.1)** | **77** | **38,497 (1.29%)** | **the 517-test v0 set becomes reachable** |

> **Inch 4 is the CHEAPEST rung by corpus share — 1.29%, a third of inch 2 and
> a thirteenth of inch 3 — and it is the one the first score depends on.**

`docs/ada-semantics-design.md` §2: v0 is *sequential Ada + exceptions + the
`Report` surface = 517 tests*. Inches 3 and 4 are both prerequisites; inch 3
cost 4x more nodes and 2.3x more paragraphs. **A ladder ordered by cost would
have put inch 4 first**, and the reason it is not is dependency, not size: a
handler needs a frame to unwind to.

**ARM 11.4 *Exception Handling* is EIGHT paragraphs and carries DYNAMIC
SEMANTICS ONLY** — no syntax, no legality, no static semantics. The
propagation rule this whole tier's `ρ` channel was designed around is eight
paragraphs of pure dynamic semantics, which is why inch 1 could commit to it
before anything could execute.

### THE TRAP, A THIRD TIME — and this one has a corpus-wide ZERO

| slot | measured |
| --- | --- |
| `HandledStmts` arity | **2 of 2**, uniform |
| `HandledStmts` slot[1] — THE HANDLERS | **`AdaNodeList`, 24 of 24** |
| `ExceptionHandlerList` corpus-wide | **0** |
| `AdaNodeList` | 65: **41 leaf-with-text (empty)**, 24 node |
| `ExceptionHandler` | 3 children: `(name‖null, AlternativesList, StmtList)` |

> **A walker written from the grammar would look for `ExceptionHandlerList`
> and find it ZERO times in 2,976,861 nodes.** The handlers live in a generic
> `AdaNodeList`, and when there are none that list is a LEAF with empty text —
> the same encoding that would have refused 30 of 31 `if`s (inch 2) and every
> parameterless call (inch 3).

Three rungs, three appearances, one encoding rule: **`extract.py` emits
`children` when a node has children and `text` otherwise, and libadalang's
list kinds are generic where the grammar's names are specific.** That pair is
now the tier's most reliable source of would-be semantics bugs, and it is
free to check before writing a rule.

### NO `RaiseStmt` WITNESS IN THE FIXTURES — labelled, not glossed

`RaiseStmt` is **1,440 corpus-wide and 0 in both fixtures**. So inch 4's
`raise` shape has **no local witness**: it must come from the corpus (the
re-acquire rung) or from a synthetic fixture that is LABELLED as synthetic.
Inch 3 could read every shape it needed off `report.json`; inch 4 cannot, and
saying so before building is the difference between a fixture and a guess.

### WHERE THE `undefined` CLASS ACTUALLY LIVES

**ARM 11.5 *Suppressing Checks* is 51 paragraphs and carries an ERRONEOUS
EXECUTION category** — the concentration the design doc predicted. It is
**outside** inch 4's range and should stay there: suppressing a check is how a
program opts into unbounded behaviour, and modelling it is a rung of its own.
Inch 3 already gave `undefined` its first *site* at 6.4.1; 11.5 is where its
*mass* is.

**ARM 11.4.2 *Pragmas Assert* carries BOUNDED (RUN-TIME) ERRORS** — a third
candidate instance for the `BoundedSite` machinery, after 5.1 and 6.2.

### WHAT INCH 4 ACTUALLY ADDS TO THE WALKER

Less than the numbers suggest, because inch 3 already walks `HandledStmts` —
it reads slot[0] and **ignores slot[1]**. Inch 4 is: read the handler list,
match an occurrence against `AlternativesList` (`OthersDesignator` is the
common case — both fixture handlers use it), and run the chosen handler's
`StmtList` with the frame intact. `RaiseStmt` re-raises on `ρ`, which is
already the channel `Constraint_Error` travels.

`inFrame`'s third arm is the one that changes: today an exception PROPAGATES
past a frame; with handlers, a frame may ABSORB it. That is a one-arm edit to
a function whose three arms were written knowing this rung was coming.

## 2026-08-25-ada-1 — INCH 4: a frame that ABSORBS, and the handler sees the world AS OF THE RAISE

`LeanModels/Ada/Ada2012/Stmt.lean` to 1286 lines and 70 guards. Built to
§2026-08-24-ada-7's census. **Not yet ticketed** — see the hold at the end.

### THE EDIT IS ONE ARM, AS THE CENSUS PREDICTED

Inch 3's `inFrame` had three arms and was written knowing this rung was
coming. Inch 4 replaces it with the same shape plus one decision:

* **`.ret` — CAUGHT.** ARM 6.5. Unchanged.
* **`.raised` — caught IFF a handler covers it** (ARM 11.2); otherwise it
  **propagates** (ARM 11.4). **Either way the frame is popped**: an exception
  leaving a subprogram still leaves it.
* **a refusal — does not come back at all.** There is no world on `π`, and an
  arm that restored one would be inventing it. Unchanged.

**THE STATE RULE IS THE PART WORTH GUARDING.** The handler runs on `w'` — the
world **as of the raise**, with the frame still pushed — not on the world the
call started in. ARM 11.4 hands a handler the state the raise happened in, and
that is precisely the property the adoption's state-RETAINING `ρ` channel was
chosen for at inch 1. The guard makes it visible rather than asserting it: the
body writes `X := 5` and then raises, the `others` handler does `X := X + 1`,
and **X ends at 6**. A handler that saw the entry world would leave 1.

### THE LIST-ENCODING TRAP, HANDLED ON FIRST CONTACT

Handlers are read from `HandledStmts` slot[1], which is a generic
**`AdaNodeList`** — 24 of 24 — and never an `ExceptionHandlerList`, a kind
that occurs **zero times in 2,976,861 corpus nodes**. An empty handler list is
a **LEAF** with empty text (41 of 65). Both are guarded. Inch 2 paid to learn
this encoding, inch 3 paid nothing, and inch 4 paid nothing.

### THE SYNTHETIC FIXTURE IS LABELLED IN THE SOURCE

`RaiseStmt` is **1,440 corpus-wide and 0 in both envelopes** — the first
construct this tier has modelled with **no witness in the tree**. Two
consequences, both taken:

1. The rule is written **not to depend on the arity**: child 0 is the
   exception name whatever else follows. A guessed arity is exactly what the
   three list-encoding traps punished.
2. The fixtures carry a **SYNTHETIC** label in the file, saying they pin the
   rule's behaviour and not the frontend's encoding, and that the label comes
   off when the re-acquire rung checks it against the corpus.

### THE SLICE

`others` and named choices (matched case-blind per ARM 2.3); a raise inside a
handler **propagates** and is not re-handled (ARM 11.4 — a handler is not its
own handler); a **bare `raise`** refuses at 11.3, because re-raising needs the
current occurrence in `W` and inch 4 has no occurrence type. Handlers on
BLOCKS (ARM 5.6) are out: blocks are not on the ladder yet.

### THE FIRST TENURE CAME BACK RED — TWO ROOT CAUSES, TEN ERROR LINES

The summary said *10 distinct error lines*; the full log says **two root
causes**, and three of the ten were cascade. Worth recording because the ratio
is the point: **an error COUNT is not a defect count**, which is why A14 says
the summary LOCATES and the full log COUNTS.

**1. A MULTI-LINE STRUCTURE UPDATE DOES NOT PARSE.** Three fixtures written as

    { caught with name := "caughtbyname",
      handlers := [...] }

each produced `unexpected identifier; expected '}'`, and the three `#guard`s
that used them then failed as **cascade** — `sorryAx` evaluating to the wrong
answer, not a semantics error. Diagnosed from evidence already in this file
rather than guessed: **one-line** updates compile here (`TrueOnly` in inch 2,
`outMode` in inch 3, both green), and a **multi-line plain instance** compiles
(`caught` itself is three lines and elaborates). Only the multi-line UPDATE
fails. The fixtures are spelled out in plain form, and the note lives in the
source next to them so the next author does not re-derive it.

**2. `Node` DOES NOT DERIVE `BEq`.** `s.handlers == []` asked for
`BEq (List Node)` and `LeanModels/Ada/Ast.lean` derives only
`Repr, Inhabited` on `Node`. Fixed with `List.isEmpty`, which needs no
instance. **Deliberately NOT fixed by deriving `BEq` on `Node`**: that file is
the version-neutral TRUNK, and a derived structural equality on a nested
inductive with `Array` children is a global instance bought for one guard —
the same trade inch 1 refused when it wrote `okIs` by hand rather than
declaring an orphan `BEq (Except Abrupt Val)`.

Neither root cause was in the semantics. **Every rule this rung added
elaborated**; what failed was two pieces of Lean surface syntax in the gate.

### HELD, NOT SHIPPED

Master fails `harness/divergence_register.py` — verified here, exit **1**, on
`docs/c-declared-divergences.json` row `c-div-2` (three guards where two
distinct named ones are required). That gate is in this lane's class floor, so
a ticket now would go red on another lane's rows. **Code written, enqueue held
until master is register-green.** ACATS stands at 0 / 4,188 and 0 / 3,996.
