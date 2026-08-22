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

### THE DUAL LAW — an obstruction that is only ENCOUNTERED is not measured either

Minted by the ES lane from **two of its own retracted claims**, and placed beside
the refusal-path law it duals. That law covers one direction — a path you never
walked is not evidence. This covers **negative claims**:

> **AN OBSTRUCTION THAT IS ONLY ENCOUNTERED IS NOT MEASURED EITHER.**

The two retractions, both generalized from a **single attempt**:

* *"`rfl` failed, so no kernel-reducible substitute exists"* — a failed attempt
  turned into a non-existence claim;
* *"`#guard` passed, so the kernel accepted it"* — a passing attempt turned into
  a claim about a **different oracle** (the §5.4 correction).

**Neither was measured against an ALTERNATIVE**, which is the whole defect. The
SoftFloat lane got both right by **replicating the function with core-only
imports and DIFFING THE TACTICS** — candidates side by side, rather than the
first outcome reported.

**Practical form**: before writing *"no X exists"* or *"X is unprovable"*, **try
the nearest alternative formulation and record the tactic diff.** A negative
needs a measurement too, and that measurement is a **comparison**, not an
attempt.

Recorded honestly in the doc: this lane's own `#guard` probe happens to have the
prescribed shape — `#guard`, `rfl` and `decide` on the **same** propositions —
which is the only reason it could support a claim about the difference between
them. **Had it run only the failing half, it would have produced exactly the
retracted claim.** Not a virtue this lane can claim credit for; a form worth
copying.

### THE HELD mvcgen DEFECT RESOLVES — the ceiling stands, and the tier routes around it

Recording defect and outcome together, as instructed when the edit was held.

**The defect stands**: per-arm `@[spec]` lemmas do **not** suffice for
**nested-match** arms, because the binding lemma cannot be *stated* — `mvcgen`
splits the inner match **without retaining the discriminant**, so unreachable
branches arrive as bare `⊢ False`. The grind-seam retry did not close it.

**The outcome**: the generator proof layer on the monadic interpreter is founded
as **judgments with discriminant premises — the trunk's method — NOT `mvcgen`
triples.** The nested-match ceiling decided it.

**And the reason the trunk's method transports is exact and worth carrying**: the
computed-shape law **never relied on a tactic retaining discriminant equations**
— the premise carries the discriminant explicitly, so nothing is lost when a
tactic declines to. **A method that depends on what a tactic happens to preserve
is fragile in precisely the way the harvest rule warns about; a method that
carries its own premises is not.**

So §3.4's *"mvcgen on the fuel-free fragment"* gains a measured boundary **inside**
the fragment: **arm-level `@[spec]` where the match is flat,
judgments-with-premises where it nests.**

### §9.5 GAINS THE INBOUND CONVENTION AND THE ROUTING LAW

**(a) INBOUND — filing into a lane that is not yours.** Per-lane files answer
*"where do I append?"* only while every entry has an obvious owner. One lane
filing into **another's** file needs a convention or it mints ids in a sequence
it does not own. So: headed **`INBOUND`**, carrying a **SENDER-namespace id**
(`YYYY-MM-DD-<sender>-<n>`, nothing minted in the owner's sequence), telling the
owner explicitly to **renumber or close** — the entry is a *proposal to* the
owner's record, not a fact already in it — and the **generated index renders
`INBOUND` as its own class** against each owning lane, so an owner sees what is
queued without reading their own file for surprises.

**THE MEASURED COST, and it is the part worth flagging: cross-lane appends
REINTRODUCE the tail race §9.5 just retired.** `es.md` conflicted on rebase
because the owner appended concurrently — the exact contention per-lane files
exist to remove, arriving through the one door they left open.

**Contingency, recorded as a WATCH ITEM rather than a change**: if the race
recurs, INBOUND entries move to **`docs/backlog/inbound/<owner>.md`** — a file
the owner drains but never appends to, restoring the single-writer property. Not
done now, because **one conflict is an incident and not yet a rate**, and §9.7's
light tick is where it would show up as one.

**(b) THE ROUTING LAW.**

> **CHECK WHAT THE OWNER ALREADY LANDED, AND FILE THE RESIDUE, NOT THE REPORT.**

Measured: an ES entry arrived **90% redundant** because the ES lane had already
**accepted, re-measured and sharpened** both findings before the report was
written. **The residue — the `ToInt32` clamp — was the only thing worth filing**,
and the report buried it under the nine-tenths the owner already had.

**This is the retrieval laws' third face.** *A grep that agrees with your prior
is the one to re-run* is about searching; *count the pattern position* is about
pricing; **this is about FILING — a report sent without checking what landed is a
duplicate its sender cannot see**, and it costs the owner the read. The practical
form is identical in all three: **look at the thing itself before reporting about
it.** For a cross-lane finding that means reading the owner's file first — which
also keeps the INBOUND entry short enough to be cheap to renumber.

### CORE'S `.except`-LAYER ALTERNATIVE IS CLOSED BY THE COVENANT (Go lane, third finding of the gap)

Core's header suggests that *"a tier that needs more than two causes does **not**
extend this type; it adds an `.except` layer of its own, which composes for
free."* Verified verbatim at `LeanModels/Core/Outcome.lean:87-88`. The Go lane —
**the third independent finding of this same gap** — named why it cannot be the
answer, and it is decisive on the family's own terms:

> **An extra `.except` layer is, BY CONSTRUCTION, a CATCHABLE channel.**

`ρ` is the program's channel **precisely because** `ExceptT` is where catch
constructs are instantiated (§3.4's speaker split). Putting refusal causes in
another `.except` layer puts **refusal in a catchable position** — the exact
thing the `Halt` ruling forbids, and it would be re-forbidden per language by the
N lemmas that ruling rejected. **Composing "for free" is free only if you do not
need uncatchability, and refusal is the one thing that does.**

So **the payload goes INTO `Loud`, not beside it**, and Core's alternative is now
closed **by the covenant rather than by preference** — which is the difference
between a ruling that holds and one that gets relitigated.

### BY-CONSTRUCTION GATES RECONCILE WITH "PRESENT AND GATED" — as the STRONGER form

The `RefusalCause` ruling said an expected-empty class is **present and gated,
never absent**. Go's `GoRefusal` has no `undefined` constructor at all. That is
**not** an exception to the rule; the two live at different levels:

* the tier's local refusal type **maps into Core's four-class cause**;
* **the gate is the THEOREM that the image excludes the class.**

**The scoreboard sees the constructor** — Core's vocabulary is complete, the
column exists, and *"this language has no UB"* stays distinguishable from *"this
tier did not model that column"*. **The tier cannot construct it**, provably,
rather than by a check that might not fire. A by-construction gate is therefore
**better** than a runtime one, for exactly the reason §3.4 prefers type-level
invariants to N lemmas: **nothing has to fire.**

Two instances, different mechanisms and the same shape — **ES's
`es_never_undefined`** (a theorem, beside `es_never_orderDependent`; ES's own
file already records both as *"PRESENT and GATED"*) and **Go's build-breaking
guard**. The class is **nameable by the family and unconstructible by the tier.**

### CORRECTION — `Run` is a RETRACT of `SemM`, not an isomorphism (and this doc claimed the iso twice)

The Core payload landing forces it. With `Loud.unsupported` carrying
`(cause, message, snapshot)` and `Run.unsupported` carrying **one field**, a round
trip through `Run` returns the only class `Run` can represent: **an
`orderDependence` refusal goes in and `unsupported` comes out.** The pilot's
isomorphism was true of the **poorer `Loud` it was proved against** — and the
payload ruling, which **this document argued for**, is exactly what broke it.
Corrected at all three sites (§3.4 headline, §3.4's re-spelling contrast, §3.8).

**The lane replaced the claim rather than weakening it, which is the right move.**
`toRun ∘ ofRun = id` still holds, so **`Run` embeds faithfully and no
trunk-shaped outcome is corrupted by lifting**. The residue is stated as
**theorems** rather than left as a caveat: `ofRun_toRun_normalises` says exactly
what is lost, `ofRun_toRun_of_plain` says exactly when the trip is the identity.
**A retract with its residue characterised is a stronger artifact than an
isomorphism that quietly stopped being one.**

> **`Run` is a faithfully-embedded VIEW. The stack is RICHER by the refusal
> payload. Theorems about `Run` transport ALONG THE EMBEDDING — never the other
> way.**

**Two conclusions survive, and it is worth saying why rather than asserting it.**
(1) *"`Run → SemM` owes no adequacy theorem"* holds, for the reason that always
mattered: **a retract is not a second semantics** — it is one semantics with a
poorer view, and `Run`'s theorems lift unchanged. (2) *"move `Run` to `Core`" and
"land `SemM`" are the same landing* holds; what changes is the **direction of
travel** — `Run`'s theorems lift into the stack, and the stack's facts do not
descend into `Run` without passing through the residue theorems.

### TWO FOLLOW-UPS RECORDED

**Default type args FAIL for monad-returning abbrevs.** `SemM W ρ Int` binds
**`Int` to `π`**, not to the value type — the abbrev returns a monad, so the next
argument lands on the defaulted slot. **The two-abbrev spelling (`SemMWith` /
`SemM`) is canon**, with `rfl`s pinning the `Unit` instantiation so the
specialised spelling is provably the general one at the default payload.
Recorded because the failure mode is a type error that **does not name its
cause**, and a tier will otherwise re-derive it.

**The runner's canonical JSON drops the refusal class**, so the scoreboard
**cannot bucket** — the one thing the shared vocabulary and the `RefusalCause`
ruling exist to make possible. **A cause type no consumer can read is a
well-typed private note.** Follow-up is an **OPT-IN field** on the
`--observations` model: off by default so canonical output stays byte-stable for
every existing `--compare` baseline, on when a scoreboard asks. Recorded as the
ruling's **delivery gap** rather than an implementation detail — until it lands,
the four classes are family law the scoreboard cannot see.
