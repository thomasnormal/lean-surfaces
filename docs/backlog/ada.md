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

## SPEC COVERAGE — the completion metric (standing; updated every landing)

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
| M2 Core adoption | *this landing* | **0 / 4,188 (0.0%)** | **0 / 3,996 (0.0%)** |

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

## INBOUND FROM THE SOFTFLOAT LANE — `2026-08-22-softfloat-5` (Ada lane's to triage)

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

### NEXT: INCH 2, CENSUS-FIRST

`W` + assignment + sequence + `if` (ARM 5.1-5.3). The census runs before the
rules, per this lane's standing practice, and the standing spec-coverage row
above is what it has to move.
