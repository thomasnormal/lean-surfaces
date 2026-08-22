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
