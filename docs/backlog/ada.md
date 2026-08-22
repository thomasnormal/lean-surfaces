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
