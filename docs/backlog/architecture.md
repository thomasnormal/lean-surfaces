# The FAMILY-ARCHITECTURE lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the family-architecture lane.** Ids are `YYYY-MM-DD-architecture-<n>` and need
no reservation, because the lane name makes them unique.

This lane writes **no Lean and runs none** (A11); its subject is
`docs/family-architecture.md` — the charter every tier is built against — and
the amendment register in its §7, which is the build protocol's only durable
home. Entries below dated 2026-08-22 were **migrated** out of the frozen
`docs/backlog.md` redirect, where they had been appended while §9.5's migration
was landing concurrently; their content is unchanged and they were given ids in
landing order.

---

## 2026-08-22-architecture-1 — NEW LAW — count the PATTERN POSITION, never the IDENTIFIER (§5.4a's constructive half)

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

## 2026-08-22-architecture-2 — THE `GenFrame` RULING — what a SHARED type may do while the legacy layer erodes

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

## 2026-08-22-architecture-3 — NEW LAW — a verdict vocabulary that cannot express a legitimate state fails BOTH ways

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

## 2026-08-22-architecture-4 — THE `GenFrame` RULING EXECUTED — first measured instance, and two laws paid off together

Inch 3a executed the erosion ruling **exactly**: the shared type grew, **the
trunk took exactly one refuse arm**, and the change landed at **9 arms — the
number the pattern-position law had just rescued from an identifier count of
35.**

A ruling and a counting law, both minted within a day, **paying off together in
the same inch**: the ruling said what the legacy layer was allowed to do, the
counting law said how much it would cost, and **neither the number nor the shape
moved on contact.** Recorded in the erosion clause as the ruling's first
measured instance rather than left as a claim.

## 2026-08-22-architecture-5 — `#guard` IS NOT A KERNEL ORACLE — reproduced here, and it corrects this document

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

## 2026-08-22-architecture-6 — SoftFloat LAYER 3 — TRANSFER, commissioned by core itself

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

## 2026-08-22-architecture-7 — `Core.SemM` LANDED — the §3.8 trigger fired, and the reconciliation INVERTS

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

## 2026-08-22-architecture-8 — THE DUAL LAW — an obstruction that is only ENCOUNTERED is not measured either

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

## 2026-08-22-architecture-9 — THE HELD mvcgen DEFECT RESOLVES — the ceiling stands, and the tier routes around it

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

## 2026-08-22-architecture-10 — §9.5 GAINS THE INBOUND CONVENTION AND THE ROUTING LAW

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

## 2026-08-22-architecture-11 — CORE'S `.except`-LAYER ALTERNATIVE IS CLOSED BY THE COVENANT (Go lane, third finding of the gap)

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

## 2026-08-22-architecture-12 — BY-CONSTRUCTION GATES RECONCILE WITH "PRESENT AND GATED" — as the STRONGER form

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

## 2026-08-22-architecture-13 — CORRECTION — `Run` is a RETRACT of `SemM`, not an isomorphism (and this doc claimed the iso twice)

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

## 2026-08-22-architecture-14 — TWO FOLLOW-UPS RECORDED

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

## 2026-08-23-architecture-1 — AMENDMENT 17 (DRAFT): proof iteration is a different shape, and five conditions I would tighten

**The measured problem, from the C lane**: a 300-line proof at one compile per
tenure is **not a session's work** — roughly **80–88 minutes per compile** under
the queue. A11 made the lock cover all Lean execution and subsumed old rule 3's
exemption; that **fixed the starvation of BUILDS and, in the same move, priced
ITERATION out.** A17 re-licenses a narrow slice with the conditions rule 3 was
missing when it was abused.

A **single-file iteration loop** (`lake env lean <file>`, which writes no
oleans) is ticket-free under **all** of: **(a)** load < 10 AND swap < 50%,
checked immediately before each run (A8's discipline, per iteration); **(b)** at
most ONE such process per lane, `nice -n 19`, `LEAN_NUM_THREADS=2`; **(c)** the
file's imports' oleans are **WARM**, else it silently becomes a dependency build
— §7.1's cold-clone trap; **(d)** it **YIELDS**, pausing while any build tenure
is in its build phase, and swap > 50% = stop. `check.sh --iterate` implements
(a)–(c) so the conditions are **checked, not guessed**, which is the whole
difference from the exemption it replaces.

**FIVE TIGHTENINGS FLAGGED FOR RULING**, in the order I would apply them:

1. **THE PER-LANE CAP DOES NOT COMPOSE — the load-bearing one.** (b) caps one
   process *per lane*; N lanes each obeying it is N unticketed Lean processes,
   which is the hazard the lock exists for. The check should count **ALL**
   iteration processes machine-wide. Same class of error as measuring RSS over
   the box instead of your own chain, with the scope inverted.
2. **NO RSS CEILING.** (b) bounds count and niceness but not memory, and A16
   exists because one honest worker measured **3 251 MB**. An unticketed,
   unsupervised process needs an explicit line — set **below** A16's 5 GB
   precisely because nothing is watching it, and make exceeding it a **kill**,
   not a pause.
3. **(d) SHOULD MIRROR (a) ON BOTH CONDITIONS.** (a) starts on load AND swap;
   (d) stops only on swap, so a loop starting at load 9 keeps running as load
   climbs. Pause on `load ≥ 10` **OR** `swap ≥ 50%`.
4. **A11's THOMAS-PRIORITY CLAUSE IS UNTOUCHED, and should be said.** A training
   run outranks every tenure, therefore outranks an iteration loop — which stops
   for it, not merely for swap.
5. **THE CHECK IS PER-ITERATION AND THE YIELD IS BEST-EFFORT.** There is a window
   between passing (a) and a tenure starting, so A17 is a **courtesy protocol,
   not a guarantee** — which is the strongest argument for tightening 2: the RSS
   ceiling is the backstop that does not depend on anyone observing anything in
   time.

**A SECOND DATA POINT ON THE A15 → A16 CHAIN FIGURE.** The C lane's **stale
watchdog killed a HEALTHY build at 6 171 MB against the superseded 6 144 MB
line** — A15's retired number still enforcing, and doing active harm. It
confirms both halves of A16 (the raise was right; canon's **10 GB** chain line
is correct) and is **A16.2 in miniature**: *an amendment takes effect when the
last script predating it is dead*, and this watchdog was not.

## 2026-08-23-architecture-2 — BACKLOG V2 migration: this lane's entries were stranded in the frozen redirect

Recording the cleanup because it is a §9.5 incident and the convention is new.
While §9.5's per-lane migration was landing, this lane kept appending to
`docs/backlog.md` — which had become a **frozen redirect** (*"Do not append to
it"*). **Fourteen entries** were stranded there, in a file nobody reads.

Fixed: `docs/backlog/architecture.md` created for this lane; the fourteen
migrated with content unchanged and ids assigned **in landing order**
(`2026-08-22-architecture-1..14`); `docs/backlog.md` truncated back to its
redirect; `INDEX.md` regenerated with `tools/backlog-index.sh`.

**The transferable bit**: the migration's own append-only design assumes lanes
notice it happened. This lane did not, because `docs_check` was green until the
index existed to go stale — **the migration was invisible to the gate that would
have caught it** until the last step landed. §9.7's light tick is where a lane
should look for "did the record's shape change under me?", and this is the first
instance of that question having a real answer.

## 2026-08-23-architecture-3 — CAPABILITY-PARITY AUDIT: two refusals are not agreement, and diff_test is structurally blind

From the completeness lane's **RED 2, a master defect**. Erosion has a second
direction nobody had ruled on: not the legacy layer growing, but the **TRUNK**
growing after the branch cut. Rung 3b's **seven draining-consumer arms** landed
on the trunk and were **merged without the capability crossing the presentation
boundary** — so the rebuild **refuses what the trunk runs, on 25 rows**.

**`diff_test` is STRUCTURALLY BLIND to this class, and the blindness is not a
bug.** A differential harness measures **agreement between the two sides**; when
both refuse, **parity holds while both are wrong**. The instrument that sees it
is the **refusal census's expectation column**, because that column is written
from **CPython's measured behaviour** — the oracle — not from the model's.

> **Agreement between two models is not evidence. Agreement with the ORACLE is.**

**This is §5.3 one level up, and §5.3 now says so.** That rule forbids a run
which executed nothing from scoring as agreement; this forbids **two refusals**
from scoring as agreement. Same shape — a check finding sameness where there was
no content — and the same fix: **anchor the expectation outside the pair.**

**THE RULE, landed in the erosion clause:**

> **Every merge across a presentation boundary owes a CAPABILITY-PARITY AUDIT**
> — the census, run against **both** targets — and **trunk-landed capabilities
> must RE-PRESENT in the rebuild before the trunk arm may retire.**

Without it erosion **silently loses capability**: the trunk arm retires because
the rebuild "agrees", and the agreement was two refusals.

**THE COROLLARY — the maximal-trunk design paying off measurably: the fix cost
ONE LINE.** The rebuild's single `iterValues` dispatch serves **six** consumers
that the trunk pays **seven arms** for. The defect was expensive to FIND and
trivial to FIX, and that ratio is the argument: a design concentrating dispatch
converts a seven-arm capability gap into a one-line one.

**Also recorded**: the rebuild lane's transcript was lost (its work is safe on
its branch) and a successor lane is spawned inheriting its ledger. The ledger
surviving the transcript is the point — §7.1a's durability lesson holding up
under its own test case.

## 2026-08-23-architecture-4 — QUALIFICATION: diff_test's blindness is in the AIMING, not the instrument; and the Core-payload hold releases conditionally

**(1) A qualification to this lane's own framing.** Entry `-3` said `diff_test`'s
blindness to mutual refusal *"is not a defect in `diff_test`: it is what a
differential harness IS."* **Too strong**, and the rebuild successor measured
why: the blindness belongs to **pointing a differential at TWO MODELS**, not to
the instrument. On the branch with `--monadic` removed the harness's other side
is **CPython**, and the **same unmodified `diff_test` CONVICTED** the 25 rows —
*predicted 25, came back 25.*

**So the law is a procedure, not a limitation**: *agreement with the ORACLE is
the evidence* is made **operational by REMOVING THE SECOND MODEL**. With one
model and one oracle the ordinary harness already covers this class.

**And the capability-parity audit gains an END CONDITION**, which is what makes
it scaffolding rather than a standing tax: **it is the rule for the WINDOW in
which two models coexist.** When the presentation boundary closes and the other
side is the oracle again, the ordinary differential resumes covering the class
and the audit retires with the window. Corrected at both sites (§3.4's erosion
clause and §5.3).

**(2) THE CORE-PAYLOAD HOLD RELEASES ON LANDING — written as a CONDITION.** A
queued merge's `Loud.unsupported (cause : RefusalCause π) (message)
(snapshot : Option σ)` **subsumes both tiers** — C at `σ := Mem` with its guards
lifted, ES at `π := EsRefusal`. On that landing **both HOLDs release**, the two
payload-bearing tiers converge by import like the other eleven sites, and entry
`-?`'s *"Core carries neither"* **goes false at that moment.**

**MASTER TRUTH AS WRITTEN: NOT YET MERGED — checked, not assumed.**
`LeanModels/Core/Outcome.lean` still reads `| unsupported (msg : String)` and
contains **zero** occurrences of `RefusalCause`. So the doc states a **condition
on a landing**, never a fact; the merge lands on green.

**And the discharge is pinned by a docs_check-checked block against
`Core/Outcome.lean` rather than prose** — this document's §9 thesis applied to
itself: **a claim that a type now carries a field should be checked against the
type, not asserted beside it.** When the block goes green the conditional
paragraph is retired **by the gate**, not by an editor remembering to.

## 2026-08-23-architecture-5 — Re-founding needs a differ-on-purpose word; names asserting verdicts expire

Three laws from py-complete inch 3a.

**(1) THE RE-FOUNDING COROLLARY to the vocabulary law, and it is the FOURTH
instrument this lane has had to teach a legitimate new state:**

> **During a re-founding, every two-sided check needs a vocabulary for "these
> differ ON PURPOSE" — and the default vocabulary never has one.**

The four: `DIVERGE`/`DIVERGED`, the census's grammar column, the gate's
`OPENED`, now `MONO_OPENED`. **Four is no longer a run of bad luck; it is a
property of re-founding.** Any check built when there was one model will need
this word the moment there are two, and will not have it.

**THE HONESTY SPLIT that stops this becoming whitelisting:** *the census RECORDS
intent and never adjudicates; the gate ADJUDICATES.* A census may say "these
differ on purpose" — a claim about **intent**, and recording it is what makes
the difference visible. Only the gate decides whether it is acceptable, and it
decides **from the oracle**: `OPENED` counts only when the rebuild matches
CPython. Without the split, "extend the vocabulary" degrades into "record that
we meant it" — precisely the failure *the adjudicator is the oracle, never the
table* names.

**AND IT IS WINDOW SCAFFOLDING — it retires with the window.** The two-model
window creates the need for a differ-on-purpose word; when the window closes the
word has nothing to name. **Resolution ruled DELETE, not deprecate** — the
successor's landing deletes `monadic_gate.py`. A vocabulary kept past its window
is a standing invitation to record intent instead of measuring agreement.

**(2) THE NAMING LAW**, landed in §5.4's instrument contract where rows are
governed:

> **A name asserting a VERDICT has a shelf life. One asserting a CONSTRUCT does
> not.**

Measured: `keys_for_is_still_loud` **expired the moment 3a landed** — the
construct stopped being loud, and **both instruments convicted the NAME** rather
than the behaviour. Renamed `keys_for_live_cursor`, which names what the row
*exercises* and stays true as the tier grows. **A verdict-named row is prose
embedded in an identifier**, and it goes stale the way §9's prose does — except
nothing greps it, so it goes stale **silently** and then convicts the wrong
thing.

**(3) A SECOND MEASURED INSTANCE of two-model blindness, smaller and therefore
worse.** `for` has **three** entry paths — `execGen`, `SKont`, `Kont` — and the
**third was missed**. `diff_test` could never catch it: the trunk refuses the
same rows, so parity held while both were wrong. The 25-row instance was a whole
capability going missing; this is **a single dispatch arm**, invisible by exactly
the same mechanism. **The class does not announce itself by size** — which is
the argument for the capability-parity audit being routine rather than reserved
for large merges.

## 2026-08-23-architecture-6 — Three tiers re-derived one payload; DELETE has a precondition; and a correction to my own A14 guidance

**(1) THE MEASURED COST OF A TRUNK POORER THAN ITS SIBLINGS — three independent
re-derivations.** Go is the **third** tier found re-deriving §5.2 locally: its
own four-class `RefusalCause` whose tag is **byte-identical to Core's
`className`**, flattened with the clause into **a prose prefix for a scoreboard
to parse back out.** After C's snapshot and ES's cause, that is three lanes, none
talking to each other, each rebuilding the same missing payload **in string form
plus a parser to recover it.**

**Three is the family's own evidence bar** (§9.3 ratified the span field names on
exactly this standard) — and what it convicts is **not the tiers, it is the
trunk.** Go's is the sharpest: it re-derives a name **Core already has**, then
**encodes structure into a string so a consumer can decode it** — a round trip
existing only because the typed field does not.

> **A thin sibling is cheap. A trunk too poor for its siblings is not — it is
> paid for N times, in string-building and re-parsing, by lanes that never see
> each other's version.**

Landed beside the thin-siblings strategy as the direct cost of the §3.4 gap, and
the reason the fix belongs in `Core` rather than any adopter.

**(2) DELETE HAS A PRECONDITION, and missing it inverts the ruling.**
`MONO_OPENED` could not simply be deleted: its own comment recorded why the table
was safe — it *"cannot become a silencer BECAUSE `monadic_gate` adjudicated its
rows against the oracle."* **Delete the adjudicator and keep the table and you
have built the silencer.**

> **When a window's ADJUDICATOR retires, every row it adjudicated must be
> RE-ANCHORED to the surviving oracle — never left merely recorded.**

Done by moving the rows `expect:unsupported → match`, so **`diff_test`
adjudicates them against CPython**: the adjudicator changed, the adjudication did
not lapse. **And dropping them would have been worse than keeping them** — four
census rows carried `mono=MATCH` against `expect=REFUSE`, where the `REFUSE` was
**the retired trunk's answer**. Dropping checks the rebuild against a retired
interpreter's expectation; keeping un-adjudicated checks it against nothing.
**Only re-anchoring is a check at all** — §5.3's *agreement with the ORACLE*
arriving at the moment a window CLOSES rather than while it is open.

**(3) A CORRECTION TO MY OWN A14 GUIDANCE.** I wrote that a red full build falls
back to scoped `--build-target` builds carrying a coverage statement. **That is
wrong, and the reason is structural: a scoped coverage statement needs a GREEN to
scope a DELTA against.** A coverage statement says what this green covers
*relative to a known-good baseline*; **a red full build leaves nothing to
scope**, because the untouched part's status is unknown rather than good. So
after a red, **the next build is FULL again**. Scoped builds are how you **extend
a green**, never how you **recover from a red** — and my guidance would have had
lanes reporting scoped greens over an unknown tree.

## 2026-08-23-architecture-7 — The blast radius is bounded by DESTRUCTURING sites; and the triad summary locates rather than counts

Two findings from the successor's triad #3.

**(1) THE PATTERN-POSITION LAW MEASURED AGAINST ITSELF — and it caught a THIRD
wrong unit: IMPORTS.** A bound on breakage from a payload change was taken as the
count of **direct importers** of `Core.Outcome` — **2 files**. That is neither
the identifier nor the pattern position; it is a unit that **cannot see the thing
at all**, because a consumer reaches a constructor's shape without naming its
module. The convicting case: `guards.lean`'s `refusalOf` matches
`.error (.unsupported m)` and **names no Core symbol whatsoever**.

Five units on one change: direct importers **2** (not a bound at all);
transitive reachers **128** (true, useless); **sites that DESTRUCTURE the
constructor — 11 lines / 3 files (the right unit)**; actually broken **1**;
build-reported **6** (five `#guard`s downstream of ONE cause).

> **The blast radius of a constructor change is bounded by the sites that
> DESTRUCTURE it. Grep the PATTERN POSITION — `.error (.unsupported` — not
> imports, and not the API's identifiers.**

**The last two rows are the practical point.** The destructure count (11)
**over**-estimates real breakage (1) — an upper bound, which is what planning
wants. The build report (6) **over**-states *sites* by amplification, five of six
being `#guard`s downstream of one cause. **Neither the plan nor the build log is
a count of causes**: the destructure grep bounds the work, the log locates it.

**And the grep must DISCRIMINATE**: two correct exclusions were
`.unsupportedDevice`, a constructor of a **different type** sharing a name
prefix. Matching the constructor name alone re-imports the identifier law's
failure; matching the **position** is what excludes them.

**(2) THE TRIAD SUMMARY IS NOT A COUNT — measured on the wrapper itself.**
`tools/triad.sh`'s "first failures" block is `grep -E '^error|✖' | sort -u |
head -8` — **deduplicated and truncated at eight** — and **`lake` stops at the
first failing module**, so the log it summarises is already partial. A "one error
in 839 targets" line reported from a red triad came from exactly this block. A
failure count taken from it is a **LOWER BOUND on sites, never a count.**

> **The triad summary LOCATES; the full log COUNTS.**

**And a red build means THE GATES NEVER RAN.** Build exit 1 short-circuits the
tenure, so a red triad yields **a build-error list and nothing else** — no
`docs_check`, no `diff_test`, no census. A red triad is not a triad *result* with
one part failing; it is an **aborted triad**, and reporting it as "triad: 1
failure" claims two gates that never executed. §5.4a on the instrument that
reports the other instruments: **the number carries the state it was taken in,
and "red" is a state in which most of the numbers do not exist.**

## 2026-08-23-architecture-8 — The Core payload LANDED: holds released, and the gate retired the conditional

**MASTER TRUTH, verified rather than accepted** (`eeeb1fd`):
`LeanModels/Core/Outcome.lean` now declares `inductive RefusalCause (π : Type)`
with `| unsupported (detail : π)`, and `Loud π σ` carries
`(cause : RefusalCause π) (message : String) (snapshot : Option σ)`. **The
condition on the conditional paragraph is TRUE**, so the prose is now the fact.

**Both HOLDs release.** The payload **subsumes both tiers** — C at `σ := Mem`
with its guards lifted, ES at `π := EsRefusal` — so **all thirteen sites may
converge by import**, the eleven mechanical and the two payload-bearing. The hold
existed to stop a convergence that would have traded two implemented rulings for
a `String`; **it has served its purpose and is discharged.** C and ES are told;
Go has the adaptation on master and **the structural-cause decision is Go's**.

**AND THE MECHANISM WORKED — recorded because it was a proposal one landing
ago.** The discharge was pinned by a **`docs_check`-checked block against
`Core/Outcome.lean`**, and **the gate retired the conditional paragraph**, not an
editor remembering to. The block matches the landed `Loud`, the `BEq` instance
that **ignores the snapshot**, and `observable`, which **drops it** — so the two
constraints of the original `Halt` ruling (*optional*, *never an observable*) are
now **checked against the type** rather than asserted beside it. `docs_check`
reads **87/87** on the merged tree.

That is this document's §9 thesis with an instance attached: **a claim that a
type carries a field is checked against the type, and it cannot rot silently.**
This doc has twice carried a claim that went stale under it — the `ofRun`/`toRun`
iso, and *"Core carries neither"* — and this is the first one retired **by a
gate** instead of by a correction.

## 2026-08-23-architecture-9 — NEVER `git stash` MID-MERGE: it silently destroys MERGE_HEAD

From the Core-payload merge itself, into §7. A `stash` / `stash pop` inside an
active merge leaves the **content correct and the SECOND PARENT gone** — the
resulting commit is an ordinary commit wearing a merge's tree.

**The failure is delayed and unexplainable.** The lane caught it only because its
commit **fell through as a no-op**; had it landed, **master would not have been
an ancestor**, the push would have been rejected, and **nothing in the tree would
explain why** — every file would be right.

> **Never stash mid-merge. Take comparisons from `git show <ref>:<path>`, which
> touches no state.**

**And verify before declaring a merge ready: `git log -1 --format=%p` must show
TWO parents.** That is the check this failure mode demands, because **every other
signal — the diff, the build, the gates — looks correct.** It is §5.4a's shape in
git metadata: **the artifact reads clean while the thing that makes it a merge is
missing**, and only a check aimed at the metadata can see it.

## 2026-08-23-architecture-10 — The pattern-position grep mis-counts BOTH ways; helpers shrink the blast radius; and four tiers converged on the classes

Five findings from ES, C and SV, landed together because three of them calibrate
the same law.

**(1) THE PATTERN-POSITION LAW MIS-COUNTS IN BOTH DIRECTIONS — it warned about
one.** Calibrated by the C tier, which had already moved `unsupported` out of `ρ`
into `Halt`: **`.error (.unsupported` returns ZERO there** — the pattern was
written for tiers where refusal rides the error channel, so a tier that moved it
is invisible to the grep meant to bound it, and it reads as *"no work to do."*
Meanwhile a naive `.unsupported` grep **OVER-counts by 4** (`Ast.lean`'s
`Expr`/`Stmt`/`Decl.unsupported`, three unrelated types sharing a name).

> **The pattern position is the CONSTRUCTOR OF THE TYPE BEING CHANGED, WHEREVER
> THAT TYPE RIDES. Name the type first, then grep its constructor's pattern.**

A grep hard-coded to one channel has a tier's design baked into it.

**(2) THE COMPLEMENTARY DESIGN LAW — shrink the blast radius before measuring
it.** ES: **198** "guards" as first framed → **5 destructure + 2 construct**,
because the guards route through four factored helpers and only `refuses*`
matches `Halt` at all — an over-estimate of roughly **40×**. C: **53 of 64 touch
points INSULATED at zero cost**, because every refusal routes through a **named
primitive**.

> **Concentrate outcome-shape knowledge in helpers. A substrate change is then
> priced by the HELPERS, not by their callers.**

**C's 53-of-64 is §3.4's routing law paying for itself at adoption** — a rule
adopted for uncatchability and `@[spec]` registration turning out to make
substrate changes cheap. And **one arithmetic note, because the law applies to
its own evidence**: ES's raw grep returned **8**, three were collisions, and the
honest total is **7** — not 5 — because the two **construction** sites match a
*different* pattern. **No single grep produced the number.**

**(3) `σ := Unit` IS THE FAMILY DEFAULT.** *Adding a snapshot without a consumer
is designing against nothing.* A tier takes a non-trivial `σ` only with **both** a
consumer **and** the never-an-observable guard. ES takes `Unit`; C takes `Mem`
because it has both.

**(4) THE STATEMENT-SITE LAW PAYING OFF WITH A ZERO.** `es_never_undefined` and
`es_never_orderDependent` transferred across the Core payload landing with **ZERO
edits**, because they are stated about **the tier's own cause constructor**, not
about `Halt`. **A theorem survives a change to the thing it does not name.**

**(5) A GREEN BUILD IS NOT A TERMINATION ARGUMENT** — landed as founding-checklist
step 10. C's inch 5 killed termination inference by passing `evalExpr ctx` as a
closure through an opaque `ctx.call`, which **exposed a latent defect inch 3 had
built green on**: `evalExpr`'s aggregate cases **reconstruct** the node, which is
not a syntactic subterm. The defect was **two inches old and passing**.

> **When recursion goes through a RECONSTRUCTED node or an OPAQUE callee, state
> the measure — `termination_by` on the whole mutual block. Take the PARTS; never
> rebuild the node.**

A §5.4a instance rather than a Lean tip: **the green was never evidence of
termination — it was evidence that inference had found some other route.**

## 2026-08-23-architecture-11 — Four tiers converged on the CLASSES while three re-derived the PAYLOAD; and a value is never a refusal

**(1) THE EXACT COUNTERPOINT to the three re-derivations.** SV's §2.4 taxonomy
predicted it would need a class for scheduling nondeterminism and found
**`RefusalCause.orderDependence` already in `Core`** — arrived from ES, Go and
Python **without SV asking**. So the **classes** were reached independently from
**four directions** and agreed, while the **payload** was re-derived **three
times** into three different string encodings.

**Convergence validated the taxonomy at the same time re-derivation convicted the
type.** Worth holding as a pair: §5.2's four classes were right while `Core`'s
`Loud` was wrong, and a lane reading only the three re-derivations might have
concluded the whole design needed revisiting. **It did not — one field did.**

**(2) A TIER INVARIANT ON MEMBERSHIP SITES, guarding an invisible mistake.** In
SV, **X-propagation must NEVER become `orderDependence` or any refusal**: unknown
(`x`) is a **VALUE of the 4-state semantics**, and misfiling it silently converts
**4-state into 2-state-plus-errors** — a different language wearing the same
name, with nothing failing to announce it.

> **A value the spec defines as a VALUE is never a refusal — however much it
> looks like "we don't know."**

**Stated as a QUESTION, not a family fact.** Two candidate siblings, neither
ruled here: **Python's `NaN`** (already a value in IEEE 754, so the question is
only whether a tier is tempted to refuse it) and **C's indeterminate-but-NOT-UB
reads** — genuinely open, because the C tier currently arms *indeterminate read*
as one of its eleven UB classes, and whether the not-UB subset is a value or a
refusal is **the C lane's to answer**. If two tiers answer the same way
independently, the convergence standard promotes the invariant from tier to
family.

## 2026-08-23-architecture-12 — A definition that COMPILED was unsound; Go's retirement resolves the re-derivations; Ada dates a predicted consumer

**(1) THE SHARPER SIBLING TO "a green build is not a termination argument."** The
Lean tier's first definition required the structure's sort to be
**`IsAlwaysZero`** — **unsound**: `instL` turns `Type u` into `Prop` at `u := 0`,
so a **projected data field yields `False`** (the arena's proj-of-imax-prop
family, which **the official kernel itself failed at v4.28.0**). The kernel's own
test is **`!isNeverZero`** — *maybe* zero, not *always*.

**What caught it was the validation lemma**: `TrProjP.instL` was **unprovable**
against the wrong definition.

> **A definition that merely compiled would have shipped the unsoundness. The
> proof is what refused it.**

Landed beside step 10 as §0.1's trust boundary in the form of a **work order**:
**write the validation lemma before declaring a definition done.** A definition
is a claim, and compiling is not how a claim is checked — the same relation step
10 draws between a green build and a termination argument, one level more
dangerous because the artifact was not merely unproven but **wrong**.

**The polarity rule, carried for anywhere universe levels are modelled**:
`MaybeZero` **REFLECTS** along instantiation (discharges hypotheses),
`IsAlwaysZero` **TRANSPORTS** forward (supplies conclusions), `ProjSound` goes
**∀ → ∃**. Getting the polarity backwards is exactly how a hypothesis-shaped
condition ends up asserted as a conclusion, which is what happened.

**(2) THE THREE-RE-DERIVATIONS ENTRY IS RESOLVED.** With Core's payload landed,
**Go retired its local `RefusalCause`** (ticketed); its gate is now
`(r.toCore π).isUndefined = false` by `cases r <;> rfl` against **`Core.isUndefined`,
a predicate lifted from ES.**

> **The lane contributes the NARROWER TYPE; the PREDICATE is everyone's.**

And the payoff is concrete rather than aesthetic: **two guard shapes a string
could not express** — a **cited clause that is checkable**, and **`isUndefined`
per refusal**. So the entry closes as a **result**, not just a diagnosis: the
string encodings were not merely inelegant duplication, they were **LOSSY**, and
the loss is recoverable only by carrying the cause as data.

**(3) HOW TO HOLD A FUTURE `σ`, from Ada.** Ada accepted `σ := Unit` while
naming a **predicted** consumer — a partial trace on a mid-test refusal — and
**dating it to inch 5**.

> **Predicting a consumer is not having one.**

The anticipated need is **named, dated to an inch, and not built**, which keeps
the default honest (no field nobody reads) without losing the design intent (the
inch that will need it knows it is coming). **A prediction held this way is a
scheduled decision; a prediction held in the type is speculative generality
wearing a plan's clothes.**

## 2026-08-23-architecture-13 — The triage rule for what the parity audit finds; and the two-model window has closed on the closed-function surface

**(1) A TRIAGE RULE, from the R-track lane correcting its OWN ledger.** It had
recorded the 25 dict-keys rows as a **tier-boundary disagreement needing a
ruling**. The ruling was **"defect — rung 3b never crossed the presentation
boundary."** The capability-parity audit *surfaces* divergences; it did not say
how to **read** them, and this closes that gap:

> **When two interpreters of the SAME tier differ, the null hypothesis is an
> UNPORTED FIX — never a boundary dispute.**

**A cost argument as much as a frequency one**: disputes are **rare and cost a
ruling**; unported fixes are **common and cost a line**. A prior that reaches for
the expensive rare explanation is wrong most of the time and expensively wrong
each time.

**The recorded reasoning error is the transferable part**, because it is a
mistake anyone reading a refusal is tempted into:

> *"I read a deliberate refusal MESSAGE as evidence of a deliberate STATE — a
> refusal message is written at the DEFINITION SITE and says nothing about
> whether reaching it HERE was intended."*

A carefully-worded refusal proves someone thought about **refusing**; it proves
nothing about whether **this path should have arrived**. The two are authored at
different places and different times.

**And the tell was already in the lane's own log**: the **trunk answered**,
**CPython agreed**, **only one presentation refused** — an unported fix's
signature, not a dispute's. A dispute would have the two sides disagreeing about
what the *language* does; here they agreed and one side had simply not been told.

**(2) MASTER TRUTH — the two-model window has CLOSED on the closed-function
surface.** Verified in the tree: `Main.lean:14` imports
`LeanModels.Python.Monadic`, and line 543 reads `let run := Monadic.callInMono m
fuel` under a comment naming it **THE INTERPRETER**. So `diff_test`'s
**1427 / 0 / 116 / 1311** validates **the rebuild against CPython directly**, not
one model against another.

**The second model is gone from that surface, and with it the blindness** — which
is the *remove the second model* procedure **executed rather than described**.
The capability-parity audit remains the rule for whatever windows remain open;
where the window has closed, the ordinary differential covers the class again, as
the end condition said it would.
