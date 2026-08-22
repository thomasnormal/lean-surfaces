# Backlog — MOVED

**This file is a redirect, and it is FROZEN. Do not append to it.**

`docs/family-architecture.md` §9.5 retired the single-file backlog:

* **your lane's entries go in `docs/backlog/<lane>.md`**, appended only by
  that lane, with ids `YYYY-MM-DD-<lane>-<n>` that need no reservation;
* the single view across every lane is
  [`docs/backlog/INDEX.md`](backlog/INDEX.md), **generated** by
  `tools/backlog-index.sh` and never hand-maintained (§5.5);
* everything written before the split is in
  [`docs/backlog-archive.md`](backlog-archive.md), frozen, where **every
  `§Lnn` reference still resolves at the heading it always had.**

This stub exists because **111 tracked files cite `docs/backlog.md`** —
including `.lean` files, whose edit would make a docs landing tier-class. A
big-bang sweep is exactly what §9.2 forbids; the old spelling is retired **by
touch**. Until then, a citation that lands here is one hop from its target.

`tools/backlog-index.sh --check` asserts the index is in sync, and
`tools/docs_check.py` reports it when it drifts.

### NEW LAW — count the PATTERN POSITION, never the IDENTIFIER (§5.4a's constructive half)

Minted by the completeness lane on its **third** hit, corroborated by the
rebuild's `DRAIN` collision the same day. Placed beside *"a grep that agrees with
your prior is the one to re-run"* as its **constructive half**: that rule says
**re-run**, this one says **what to count**.

> **A COUNT THAT PRICES A DECISION MUST COME FROM THE PATTERN POSITION, NEVER
> FROM THE IDENTIFIER.**

An identifier count answers *"how often is this name written?"* — mentions,
docstrings, other lemmas' statements, the doc you are reading. A decision is
priced by *"how many places must change?"*, and those are **pattern positions**:
match arms, clause slots, actual branch points.

| instance | what went wrong | direction |
| --- | --- | --- |
| §L49's `\.usub` grep | missed every `cases op with \| usub =>` arm **by one character** | UNDER |
| §L53's walker price | landed at **19** because **catch-all arms were load-bearing** | UNDER |
| today's VCGen price | **26 lemma NAMES** priced a **9-arm** change at **35**, nearly moving a date | OVER |
| the rebuild's `DRAIN` | generator drain vs the short-circuit trick — a collision that **agreed with the prior** | OVER |

**Both directions are live, which is why the rule names the POSITION rather than
saying "count carefully."** Identifiers over-count because names appear where no
work happens; pattern searches under-count when the syntax differs by a
character; and **catch-all arms defeat arm-counting entirely** — one `| _ =>` can
absorb a dozen cases, so even a correct arm count can be the wrong price.

Practical form: **price a change by enumerating the positions it must visit, and
check that enumeration against the thing that DISPATCHES** — the `match`, the
clause list, the table — never against the name index.

### THE `GenFrame` RULING — what a SHARED type may do while the legacy layer erodes

Erosion raises a question neither "freeze it" nor "maintain it" answers: a type
used by **both** layers, not itself retiring, which the **new** layer needs to
**grow** for a new capability.

> **A shared-not-retiring type MAY grow for new capability. The legacy
> interpreter's contract is exactly three things: it COMPILES, it REFUSES what it
> does not implement, and it GAINS NO CONSUMERS.**

The growth lands and the legacy layer absorbs it with **a one-line refuse arm —
the legacy layer's ONLY permitted growth.** Not a stub that half-works, not a
TODO, not an implementation. A refusal is loud, fuel-independent and correct
(cause 1), so the legacy layer stays **true** without being **maintained**.

**Both foreclosed failure modes are real.** Freezing the type blocks the new
layer's capability on a layer that is supposed to be dying — the dead hand of the
thing being retired. Implementing the arm gives the legacy layer a **new consumer
and a new reason to live**, which is the opposite of erosion. The one-line refuse
arm is the unique move that keeps it compiling without giving it a future.

### NEW LAW — a verdict vocabulary that cannot express a legitimate state fails BOTH ways

Third §5.4-family law minted this session (completeness lane, inch 3a). Placed
beside the grep/pattern-position pair: **those two are about COUNTING, this one
is about VERDICT VOCABULARIES growing honestly.**

> **A CHECK WHOSE VOCABULARY CANNOT EXPRESS A LEGITIMATE NEW STATE WILL EITHER
> BLOCK THE STATE OR BE SWITCHED OFF — both wrong. Extend the vocabulary, and
> make the new word EARN ITS VERDICT FROM THE ORACLE, NEVER FROM THE TABLE.**

**The failure has two exits and a check reaches for one automatically.**
BLOCKING: the state is legitimate, the gate says no, correct work cannot land.
SWITCHING OFF: the gate is loosened and nothing is checked. Neither is chosen on
purpose — both are what happens when a vocabulary runs out of words and nobody
notices that is what happened.

| instance | the missing word |
| --- | --- |
| `DIVERGE`/`DIVERGED` (§9.4) | a display name **drifting with its selector** |
| the census's `mono=` expectations | a **two-interpreter scoreboard needing a second column** |
| **`monadic_gate.py`** | non-zero on **ANY** non-frontier divergence — so a **RULED** divergence (trunk refuses, rebuild returns 1, **CPython AGREES with the rebuild**) **could not land green** |

**The fix and its guard**: `monadic_gate.py` gained **`OPENED`, counted only when
the rebuild matches CPython.** That qualifier is the whole rule —

> **The adjudicator is the ORACLE, never the TABLE.**

A new verdict word is not a place to record what you have decided is acceptable;
it records **what the oracle says**, under a name the old vocabulary could not
pronounce. Without that guard, "extend the vocabulary" is **whitelisting with
better manners** — which is why this is the standing ban on `"expect":
"unsupported"` rows that silence a mismatch, generalized from one harness to
every check.

**The wrong fix was NAMED AND REFUSED, not merely not taken**: switching the gate
off converts a vocabulary problem into a **coverage hole, and a coverage hole
reads green** — §5.4a's flattering direction, reached by a route that feels like
pragmatism.

**And §5.1's membership ruling was this law before it was named**: *the DIVERGE
test is not equality at every site* extended a vocabulary so it could express two
conforming implementations disagreeing — a legitimate state the old vocabulary
could only call DIVERGE. Recognized late and recorded as such.

### THE `GenFrame` RULING EXECUTED — first measured instance, and two laws paid off together

Inch 3a executed the erosion ruling **exactly**: the shared type grew, **the
trunk took exactly one refuse arm**, and the change landed at **9 arms — the
number the pattern-position law had just rescued from an identifier count of
35.**

A ruling and a counting law, both minted within a day, **paying off together in
the same inch**: the ruling said what the legacy layer was allowed to do, the
counting law said how much it would cost, and **neither the number nor the shape
moved on contact.** Recorded in the erosion clause as the ruling's first
measured instance rather than left as a claim.

### `#guard` IS NOT A KERNEL ORACLE — reproduced here, and it corrects this document

From the SoftFloat lane, **verified by this lane before propagating** (warm clone,
`nice -n 19`, rule 3 satisfied this time). Three propositions, all **`#guard`-PASS
and kernel-FAIL** on the pinned toolchain:

    #guard Nat.sqrt 49 == 7                -- PASSES
    example : Nat.sqrt 49 = 7 := by rfl    -- FAILS (unsolved goals)
    example : Nat.sqrt 49 = 7 := by decide -- FAILS
    #guard (2.75 : Float).toInt64 == 2     -- PASSES
    example : (2.75:Float).toInt64 = 2 := by rfl  -- FAILS

`#guard` runs unsafe `evalExpr`, honours `@[extern]`/`@[implemented_by]`/`opaque`,
and **passes identically whether a declaration reduces or has no body at all**.

**CONSEQUENCE 1 — "run, not admired" via `#guard` is RUNTIME attestation.** For
pure extern-free code the VALUE agrees with the kernel, but
**kernel-reducibility is certified only by `rfl`/`decide`** (or `#guard_expr`
with `=~`). **This document made the overstated claim** and it is corrected:
§3.4 said *"`#guard`/`#py_check` and every captured run are kernel `rfl`"*. They
are not. **The EStateM ruling itself stands** — its reason was that kernel
reduction is load-bearing, and its 1.4x figure was measured on kernel `rfl`;
what was wrong was the list of artifacts named as certifying it.

**CONSEQUENCE 2 — THE PAIR IS A DIFFERENTIAL**, and this is the constructive
half: `#guard` attests the **C runtime**, `rfl`/`decide` attest **core's model**,
so a float-touching row carries **both** and **disagreement is a FINDING** — two
oracles genuinely diverging, which is what a family of language models exists to
surface rather than average away.

**PLACEMENT vs the decide ladder**: the ladder's rungs are **KERNEL** tactics.
**`#guard` is BENEATH the ladder, not on it** — not a cheaper rung 2, but a
different kind of evidence, and the receipts rule applies: a row attested by
`#guard` says so.

**Re-attestation owed, cheaply**: the rebuild's *"9 `#guard`s decide real runs in
the kernel"* (one run per half with `decide`); the **~50 ES `#guard`s** under
`Examples/es`, FPU-attested today; and `harness/es/float_probe.lean`, which
**mis-describes `#guard` as kernel evaluation** (ES lane's fix).

**§5.4a gains a fifth instance**: a `#guard` batch quoted as kernel evidence —
and it reads CLEAN, which is the flattering direction again.

### SoftFloat LAYER 3 — TRANSFER, commissioned by core itself

Core's `UnpackedFloat` docstring disclaims the role outright: it is **not a goal
of that development** to be the basis of a general-purpose float library *"or to
have any direct lemmas written about it at all"*; users should **develop such a
library completely separately, prove the operations equivalent, and transfer
lemmas** to `Float`/`Float32`.

**So §3.5 has a third layer and it is commissioned, not optional.** This sharpens
"layer 1 is free": core supplies the *executable* model for free and **explicitly
declines to be a proof basis**. Layer 2 is the separate library core asks for;
**layer 3 is the equivalence-and-transfer bridge** — and without it a theorem
about our `Format`-parametric algebra says nothing about the `Float` an
interpreter observes, while a `#guard` on that `Float` attests only the runtime.
**Layer 3 is what joins the two oracles the differential pair names.**

**AND THE NaN PAYLOAD IS UNSATISFIABLE OVER CORE'S MODEL — open Thomas
decision.** §3.5.4 routes NaN payload/sign to ∀-resolution. Core states: *"There
is no payload attached to a NaN in this format."* **You cannot quantify over a
payload the type does not have.** The options — carry our own NaN representation
in layer 2, restrict claims to payload-independent facts, or accept core's
payload-free NaN as the family's answer — are **Thomas's**. Registered as open.

### `Core.SemM` LANDED — the §3.8 trigger fired, and the reconciliation INVERTS

`LeanModels/Core/Outcome.lean` is on master. **§3.8's single landing has
occurred** and the **rebuild lane was the first-arriving trigger** of the three
candidates. Verified in the file: `SemM W ρ := ExceptT ρ (StateT W Halt)` — the
ruled layer order — plus `refuse` as a **named primitive** (§3.4's never-a-bare-
throw law), `raiseIn` for the ρ channel, `exhausted` for timeout, and `SemPS`.
Registry and inventory rows updated: **Python's definition is the monadic
interpreter**, the deep interpreter is the legacy layer under §3.4(c)'s erosion
contract. `Run` stays with its proved iso (65 example files import its umbrella).
**Full triad is OWED under A14**, with the coverage statement in the merge commit.

**THE TWO SITES, NAMED — and the dispatch's framing inverts.** They are **C**
(`C23/Memory.lean:739`) and **ES** (`Es/Completion.lean:174`), each an
`inductive Halt α` rather than `Except Loud`. But there are **no literal
`Except Loud` sites** outside Core, and the real finding is different:

| site | its `Halt` | `unsupported` payload |
| --- | --- | --- |
| **Core** | `abbrev Halt := Except Loud` | **`msg : String`** |
| **C** | `inductive Halt α` | `(what : String) (snapshot : Option Mem)` |
| **ES** | `inductive Halt α` | `(cause : EsRefusal) (message : String)` |

**All three agree on the SHAPE** (`ok`/`timeout`/`unsupported`) — the covenant
holds. **The entire divergence is the `unsupported` PAYLOAD, and CORE'S IS THE
POOREST.**

**Both tiers implement rulings this document made.** C's `snapshot` is the `Halt`
ruling's structured payload **with the never-an-observable guard made
STRUCTURAL** — its `BEq` ignores the snapshot and `Outcome` drops it, which is
exactly the two constraints §3.4 imposed. ES's `cause` is the `RefusalCause`
ruling. **Core carries neither.**

> **Convergence-by-import would DELETE both payloads** — a regression, and *"the
> quiet way to lose facts"* arriving from the other direction: **not two tiers to
> fix, but a trunk too poor to absorb them.**

**DISPATCH ANSWER: the fix is in CORE, not in C or ES.** Parameterize
`Loud.unsupported`'s payload per the `Halt` ruling (cause + optional snapshot)
and the `RefusalCause` ruling (four classes, tier payload). **Until that lands,
the eleven mechanical sites converge by import and the two payload-bearing tiers
HOLD** — importing them now trades two implemented rulings for a `String`.
