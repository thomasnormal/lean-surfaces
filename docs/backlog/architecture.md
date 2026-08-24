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

## 2026-08-23-architecture-14 — Flattering errors have a cause; the layer order makes fuelMono mechanical; three Lean tooling hazards

**(1) THE MOTIVATED-ERROR RULE.** SoftFloat's consumer census ran **319 → 170 →
13 candidates → 0 qualified crossings** — wrong twice before right, the identifier
trap in its purest form (**bare member names are English words and other types'
members**; `.exp`/`.log` were **Mathlib's `Real.exp`/`Real.log`**).

**What makes it more than a third instance is the DIRECTION**: a bigger consumer
list is **a bigger mandate for the lane doing the counting**. The error was not
random with respect to the measurer's interest.

> **When an instrument's error would ENLARGE ITS OWNER'S MANDATE, treat the
> number as FLATTERING until a recall-preserving narrowing reproduces it.**

That is §5.4a's asymmetry **with a cause attached** — the provenance law says
misleading numbers tend to read clean; this says **where to expect it**.

**And the fix is the instructive part: not a cleverer regex.** A sharper pattern
is one more guess. What worked was a **narrowing that CANNOT LOSE RECALL** — *a
file with no `Float` token in code cannot contain a `Float` crossing* — justified
by an argument about the domain, so it is **safe by construction rather than by
being careful**. Leftovers were handled by **not counting them**: dotted rows
kept as **CANDIDATES, never merged into the count**, resolved by **reading**.
**13 candidates → 0 crossings** is a number that only exists because the
ambiguous rows were held apart instead of folded in with a plausible assumption.

**Plus the one-second-build rule**: `exit 0` with **no `Build completed` line is
not evidence** — a build that did nothing and one that did everything exit the
same way. The evidence is **the olean mtime landing in the build's second**: from
*"do not infer success from the absence of errors"* to *"name the artifact whose
existence success would have produced."*

**(2) THE LAYER ORDER PAYS OFF A SECOND TIME — `fuelMono` becomes MECHANICAL.**
Measured **in scratch** (kernel-checked there; **not yet landed**). The ∃F
collapse's one missing lemma is provable **without touching the `Kont` knot and
without weakening anything**, and the reason is §3.4's covenant: the **only**
`catch` in the fuel-free half is `tryCatch` on `ExceptT PyErr` — **the program's
channel** — and **nothing observes the `Halt` layer**, so **no arm can branch on
a timeout**. Every arm is therefore a bind/ite/tryCatch composition, and
`tryCatch_apply` (Loud passes straight through; the handler is reached only from
ρ) makes the induction mechanical.

> **The layer order chosen for STATE-RETENTION ON RAISE is what makes FUEL
> MONOTONICITY mechanical.**

Same shape as C's routing law paying for itself at adoption: **a decision taken
for one reason buying a second.** The **speaker split** is doing the work — no
program construct observes `Halt`, so monotonicity has no case where a timeout is
inspected. Recorded as the family's **monotonicity recipe for ρ-bearing tiers**,
with its boundary marker: **`le_tryCatch` is the one lemma SV's `fuelMono` never
needed**, because SV has **no ρ**.

**(3) THREE LEAN TOOLING HAZARDS**, each of which cost a red and none of which
announces itself. **Through a `def`-alias, dot notation picks the TARGET's
lemma**: `HasType.instN` and `IsDefEq.instN` take arguments in **different
orders**, and `HasType` unfolds to `IsDefEq`, so dot notation **mis-slots
silently** — it worked for `instL` only because those orders *coincide*, which
taught the wrong lesson before producing a red. **Name the lemma you mean.**
**Nested inductives refuse `induction`** — use `<f>.induct`, whose arms arrive
**unfolded**, so **`apply` it**; `induction … using` fails. **A plain `def`
delta-unfolds past the motive** — prove the `_iff`, then `attribute
[irreducible]`.

## 2026-08-23-architecture-15 — A6 covered half the hazard; and the gate line has THREE states

**(1) A6 AMENDED — the missing half is the ORDINARY one.** A6 forbade *rebasing*
under a running build, and a corollary extended it to a queued ticket. Both true,
both too narrow, because of a fact about **when the tree is read**:

> **A queued tenure reads the source at BUILD time, not at ENQUEUE time.**

So an **ordinary EDIT** to a file while its ticket sits in the queue **silently
changes what the verdict is about**. Nothing is torn, nothing fails, the tenure
is not interrupted — it simply builds a different tree than the one enqueued. The
measured near-miss: a lane would have reported **"`instN` green"** for a run that
actually built **`instN` + `weak'`** — a true statement about a tree nobody asked
about.

> **Never CHANGE THE TREE a ticket will build — no rebase, no edit, no stage —
> between ENQUEUE and RELEASE. Batch BEFORE enqueue, or after the verdict.**

The window is **enqueue → release**, not build-start → build-end, and the
forbidden act is **any** change, not just a history rewrite. §5.4a's shape in its
most ordinary clothing: **the number reads clean and is about the wrong state**,
produced here by the most routine thing a lane does between tickets.

**(2) THE GATE LINE HAS THREE STATES, not two** — drawn independently by two
lanes the same morning, which is the family's convergence standard. Reading a
missing gate line requires knowing **why** it is missing, and only one of the two
absences is a verdict:

| gate line | lock | meaning |
| --- | --- | --- |
| **PRESENT** | acquired | **the gates RAN** — a verdict |
| **ABSENT** | **ACQUIRED** | **RED — aborted triad**; the build failed and the gates never ran |
| **ABSENT** | **not acquired** | **NEVER STARTED — not a verdict at all** |

**The third row was the missing one**, and it is what **SV's killed ticket** and
**the Lean tier's pending one** both were. Collapsing it into the second reports
a red for work never attempted; collapsing it into the first is worse. **The
discriminator is whether the LOCK was acquired** — which is why the lock line,
not the gate line, is what a reader checks first.

## 2026-08-23-architecture-16 — A generated model's relations are its own; the order lifts but the congruences don't

Six items across two rounds (Wasm, then the successor's fuelMono work).

**(1) CONSUMING A GENERATED/EXTRACTED MODEL — checklist step 11.** Wasm's
spec-extracted model defines its own **`Forall₂` as ZIP-BASED**
(`∀ t ∈ xs₁.zip xs₂, P t.1 t.2`), while **Mathlib's `List.Forall₂` is INDUCTIVE
and a different constant**. **Zip truncates**, so the zip-based relation **does
not imply equal lengths**, and the entire Mathlib `forall₂_*` route cannot apply.

> **A generated model's relations are ITS OWN constants — check the definition
> before importing a library's lemmas about a same-named relation.**

**The generator's extra premises are the tell**: it emits `Resulttype_sub` with a
**separate explicit length premise**, which is the generator writing down that
its relation does *not* carry length equality. **A generated model's extra
premises tell you what its relation does NOT carry** — the premise list is a
specification of the gaps, not boilerplate. And what transfers is the
**FACTORING, not the lemmas**: Aaron Lee's Isabelle `list_all2` is inductive so
his closer has no counterpart, but his factoring (refl, both split orientations,
trans) does. **The proof architecture ports; the proofs do not.**

**(2) TWO SOURCES AGREEING IS NOT VERIFICATION**, landed beside *agreement
between two models is not evidence*:

> **Reading two sources that agree with each other is not verification when both
> are about a THIRD THING the model does not use.**

Two documents concurring tells you they concur; if the model's own constant is
not the one they are about, their agreement is as unanchored as two interpreters
both refusing. **The referent, not the concurrence, is what makes reading into
evidence** — so the check is *read the model's definition*, not *read more
sources*.

**(3) THE LANE'S OWN CORRECTION, filed**: *"Mathlib: no cost"* was **right about
DEPENDENCY and wrong about APPLICABILITY** — two separate claims. Importing costs
nothing new (this doc's own §3.2 note is about that, and is true); whether its
lemmas govern **your constants** is a claim about **your definitions** and
nothing about the build supports it. Added to §3.2 so that note cannot be read as
licensing the second.

**(4) `FlatLe` RULED — conditional on landing.**
`FlatLe (bot : α) (x y : α) : Prop := x = bot ∨ x = y` with `refl`/`bot_le`/
`eq_of_ne_bot` **lifts to Core** as the flat order **every tier's `Res.le` /
`PyLe` is an instance of**. But `Sv.Res` and `Python.Res` are **DIFFERENT TYPES**
(Python's has the `.exn` raise arm), so the `Res` lemmas are not liftable and the
**bind/ite congruences stay per-tier** — each is about a **different monad's
`bind`**.

> **The ORDER lifts; the CONGRUENCES don't.**

§2.4's trunk/sibling split arriving in the proof layer: a congruence lifted here
would be the thick-trunk mistake, one lemma pretending to be about two monads.
**What travels instead is the NAMING**, mirrored across tiers (`Res.le`,
`le_refl`, `timeout_le`, `le_eq`, `le_bind`, `le_ite`, `<worker>FuelMono`) —
**convention where a definition cannot go**. Rides the successor's `fuelMono`
ticket and owes a **full build** (A14, `Core` touched); **not landed today**.

**(5) TACTIC MACROS ARE HYGIENIC — pass the IHs in.** Measured on
`heapEqFuelMono` (14 arms, axioms `[propext]`): a **top-level tactic cannot see
induction hypotheses bound inside a proof**, and **`assumption` cannot
instantiate a ∀-quantified IH**. Passing the IH names as **`ident` arguments** is
what turns fourteen hand-written arms into `split <;> auto ihE ihL`. Hygiene is
not the obstacle — it is the reason the macro must be *told* what a human reader
infers from the goal.

**(6) DOCSTRING DRIFT, into §5.4's contract.** `Kont.fuel`'s docstring read
*"used by `heapEq`, `setDedup`"*; the **measured** set is **`heapEq` +
`valContains`**. Nothing failed — a docstring naming the wrong consumers compiles
exactly as well as one naming the right ones, and a lane reading it to decide a
blast radius would have grepped for the wrong thing. **A reachable set is
measurable, therefore checkable**, and a docstring asserting one is in the same
category as a clause citation: **checked data, or prose that goes stale
silently.**

## 2026-08-23-architecture-17 — Census-first applies to the LEMMA; and the retract framing earns a judgment

**§9.7's duplication instance for this tick**, owned by the successor lane in its
own words. It proved `heapEqFuelMono` (14 arms, clean axioms) and half of
`evalCompareOpH` before finding that `LeanModels/Python/Obs.lean` **already
carried all of it**: `Res.le` and its congruences — **identical, same namespace,
a hard name clash waiting** — plus `heapEqMono`, `evalCompareOpH_mono`,
`valContains_mono`, and **the trunk's full `fuelMono` with ~15 corollaries.**

> *"I applied census-first to the proof OBLIGATION and never ran the one grep
> that would have found existing monotonicity work."*

**The blind spot is structural rather than careless.** Censusing the *obligation*
asks *"what must be true?"* — the discipline this doc has prescribed since §1. It
does not ask *"has someone already made it true?"*, and a lane that has correctly
censused its obligation **feels finished with census-work** exactly when the
second question is still unasked.

> **Before proving `X_mono`, grep the tier AND `Core` for `_mono|Mono|\.le\b`.
> The grep that would find your own work already done is the one most worth
> running.**

Landed as §9.0a, and noted as **the retrieval laws' fourth face**: *the search
that agrees with your prior* is about believing a hit, *count the pattern
position* about pricing, *file the residue* about reporting — **this one is about
STARTING**, the grep skipped because you already know what you are about to
build.

**WHAT SURVIVES THE DISCARD, recorded so the tenure is not a total loss:**

* the **hygienic-macro / `ident`-argument technique** — now **confirmed twice**;
* the **`FlatLe` lift STRENGTHENED to THREE in-tree instances** — `Sv.Res.le`,
  `Python.Res.le`, `PyLe`. The ruling was made on two; a third independent
  instance of the same two-constructor order is §9.3's convergence standard
  applied to a **definition** rather than a name;
* **a judgment that falls out of the RETRACT: `PyLe` must NOT be defined through
  `toRun`.** `toRun` is the **lossy projection** — it **erases `RefusalCause` and
  the snapshot** — so an order mediated by it would **equate refusals with
  different causes**. That is not a convenience but a **weakening of the
  definition**, which §0.1's first principle forbids. **Define the order on the
  type that carries the information; do not route it through the view that drops
  it.**

**The last one is the retract framing paying off where it was not written for**:
knowing *precisely* what `toRun` loses is what makes "do not define through it" a
**derivation rather than a preference**. Had the iso claim stood uncorrected,
this judgment would have had no basis — the projection would have looked
information-preserving.

**Also corrected**: `Kont.fuel`'s docstring priced `setDedup` as reachable;
**measured 0 hits**. The §5.4 docstring-drift note now carries it.

## 2026-08-23-architecture-18 — Price the TYPE not one constructor; a docstring that argues is a claim; cancelling a ticket is the right move

Three from ES inch 5.

**(1) THE ES PRICE WAS RIGHT AND INCOMPLETE.** Its **7 destructure sites were
exactly right** — and the same adoption carried **22 CONSTRUCTION sites across
five modules**, which a grep for `.unsupported` alone never sees. The type's
price was **not 7**; 7 was the price of *one half of one direction*.

> **A price grepped for ONE CONSTRUCTOR is not a price for the TYPE. Price
> CONSTRUCTION and DESTRUCTURING separately, and SUM.**

The ladder has now shown this failure **four ways** — imports, identifiers,
one-channel patterns, and now **one direction of use** — and this is the most
seductive, because **the destructure number was correct**. *A right answer to
half the question reads exactly like a right answer.*

**(2) A DOCSTRING THAT ARGUES A CASE AWAY IS A CLAIM.** Sharper than the drift
note it now sits above, because prose reasoning reads as **justification** rather
than assertion. `Completion.lean` argued **in prose** that `Abrupt.brk`/`cont`
never need a `[[Value]]`; **§14.2.2 step 3 refutes it** — `while (true) { 5;
break; }` completed **empty** where the language says **5**. Same shape a second
time: **`V` starts at `undefined`, not empty**, so `1; while (false);` answered
**1**. Both are the **test262 `-cptn` family**, and both were found only by
**re-reading the pinned spec against the docstring** *after* the inch was green
and queued.

> **The missing GUARDS were the real defect.** The docstring stood where a guard
> belonged, and **prose cannot fail**.

A docstring arguing a case away is doing exactly what §5.5's manifest does —
pairing a claim with the clause that settles it — **but without the check**,
which is the whole of the difference.

**(3) CANCELLING ITS OWN QUEUED TICKET WAS THE RIGHT MOVE**, recorded under A14.
The lane dropped the ticket on discovering the wrong answers rather than spend a
tenure validating a tree it already knew was wrong. **A tenure is the scarce
resource** — A9's queue exists because it is — and a green over a known-wrong
tree is **a number about the wrong state**: §5.4a applied to **scheduling**
rather than to reporting. **Re-ticket after the fix; the queue position is
cheaper than the tenure.**

## 2026-08-23-architecture-19 — Probes must refuse on absence; the congruence set has five shapes; and row 1 fired on its author

Seven items across two rounds (ES, then the successor's fuelMono work).

**(1) EVERY PROBE THAT READS A CORPUS MUST REFUSE WHEN THE CORPUS IS NOT THE
RECORDED STATE — not only the revision probe.** ES's census stored
`{ignore_entries: null, ignore_file_present: false, workflows: []}` — **a
measurement of an ABSENT REPO**, since a bare fetched `spec.html` has no
`.esmeta_ignore` and no `.github/workflows`. The truth at the pin is **11 ignore
entries and 3 CI workflows**. `rev()` had been hardened to refuse exactly this
and **did**; **`esmeta` was the quiet half nobody had hardened.**

> **A `null`/`false`/`[]` measured on ABSENCE is the flattering direction with
> the volume off.**

A wrong revision is loud — it names another commit. An empty list is silent and
**reads as a finding**. **Absence and zero are different, and most encodings
conflate them**, so the refusal belongs in the probe rather than in the reader;
hardening one probe and not its siblings leaves the quiet ones as the whole
remaining exposure.

**(2) RE-PINNING IS RECOVERY, NOT DERIVATION.** The `ecma262` pin was recovered
by taking annotated tag `es2026-errata` → `d89c03f2` and confirming its
`spec.html` **sha256 is byte-identical to the recorded `spec_sha256`**. **The
hash is the anchor**; a tag, date or changelog is a *hint toward* the commit,
never the pin. **Reconstructing a pin from provenance metadata is a guess that
looks like a citation.**

**(3) §9.0a's OWN GREP HAS A FALSE POSITIVE, in the tier it was written for.** In
the monadic Python tier **`Mono` means MONADIC** (`callInMono`, `runScriptMono`).
**A grep's hits are CANDIDATES TO READ, never findings** — the same discipline
SoftFloat reached by another route, and a prescribed grep is not exempt from the
law that prescribed it.

**(4) THE CONGRUENCE SET HAS FIVE SHAPES, two of them CORE's**: `bind`, `ite`,
`tryCatch` (the monad) **plus `zoomIn`, `zoomOut`** (the **state-zoom seam**,
verified at `Core/Outcome.lean`). Every tier instantiating `SemMWith` **inherits
the same two obligations** — and their discharge, once Core carries the lemmas.
Python's `inFrame`/`inWorld` are instances at **two lines each**.

> **Missing one is not a missing ARM; it is a hole in the SET — and it shows up
> as a goal no amount of arm-work can close.**

The practically useful part: a missing *arm* looks like more of the same work; a
missing *shape* looks like an **impossible goal**, and a lane will grind arms
against it indefinitely. The tell: `iterValues_mono` **closed the moment the seam
lemmas existed**, with no arm changed. **When a monotonicity goal resists work
that is succeeding elsewhere, check the SET before checking the proof.**

**(4a) AMENDED AT THE LANDING — SIX shapes: monad (3) + state-zoom seam (2) +
PURE-WORKER seam (1).** The sixth is **`liftRes`**, the door a tier's REUSED
pure workers come through. `PyLe.liftRes : Res.le x y → liftRes x ⊑ₚ liftRes y`
is four lines and is the ONLY place the tier's fuel BOUND is consumed — both
`K.fuel` sites in the monadic Python tier reach `Obs.lean`'s `_mono` lemmas
through it. **A tier that REUSES another's pure workers owes a congruence for
the DOOR they come through, not just for the operations it writes itself.**

**(5) A CONGRUENCE WALKER'S COMPLEXITY IS SET BY ITS DISPATCH.** `mono_with`'s
backtracking `first` at each node is **LINEAR on bind spines, EXPONENTIAL on
`ite` chains** — **~22 nested `ite`s timed out at 200 000 heartbeats.**

> **Raising heartbeats trades a WRONG answer for a SLOW one.**

The fix is **syntax-directed dispatch on the goal head**, not budget: a
backtracking `first` is a **search where a case analysis was available**, and the
exponent is the price of not looking.

**(5a) AMENDED AT THE LANDING — the exponent was real, and the fix is smaller
than the prediction.** No goal-head dispatcher was written; the walker closes
all 61 arms plus the 19-deep chain at the **default 200 000 heartbeats**. Two
mechanisms, only one of which had been named: the backtracking `first` re-plans
a SUBTREE per leaf failure (cure: **`repeat'`** — one step per goal, KEPT), and
**`apply` unifies at DEFAULT transparency**, so it whnf-unfolds a tier constant
to find an `ite` underneath and descends *through* the very lemma it should stop
at (cures: **run the leaf closer FIRST guarded by `done`**, and make the
reflexivity probe **`with_reducible`**). **"Syntax-directed" is bought with
TRANSPARENCY CONTROL and a non-backtracking driver, not with a dispatcher — a
tactic that unfolds is a tactic that has left the syntax.**

**(6) A ~210-LINE `if fname == …` CHAIN DEFEATS EQUATION-THEOREM GENERATION**
("failed to generate equational theorem"), so **`unfold` is the only door** —
`simp only` and `rw` cannot open it, both needing equations that were never
generated. The definition still works; it becomes **unreachable by the tactics
that rewrite with it.**

**(6a) THE ARM COUNT, CORRECTED BY READING THE SOURCE.** The chain is **19**
`if fname == …` arms, each branch a small nested `match vs with`. A tool
reported 45 by counting the nested match arms as top-level ones and missing the
`if ==` form entirely. **A tool's arm count is a candidate, not a finding** —
same law as (3), one level up.

**(7) §5.4a's ROW 1 FIRED ON ITS OWN AUTHOR, live.**
`applyBuiltin_mono does not depend on any axioms` printed **beside a
heartbeat-timeout error in the same run**. The law is not hard to believe; it is
hard to **remember at the moment the line scrolls past** — which is why it needs
a machine. The guard now exists, so the rule upgrades:

> **Quote `tools/check.sh --axioms`'s VERDICT LINE. A bare `#print axioms` is not
> evidence.**

That moves the check from a discipline a reader must apply to **an artifact a
lane must produce** — §9's thesis applied to the law most likely to be violated
by the person who wrote it.

## 2026-08-23-architecture-20 — Six congruence shapes; the walker's real cause was transparency; and a correction inherited its error's scope

Three from the fuelMono lane (31/31 `evalOpen` arms, certified). Two of them
correct entries this lane recorded.

**(1) THE CONGRUENCE SET IS SIX SHAPES, three of them Core's** — `bind`, `ite`,
`tryCatch` (monad), `zoomIn`, `zoomOut` (state-zoom seam), and **`liftRes`** (the
**PURE-WORKER seam**: `Res.le x y → liftRes x ⊑ liftRes y`). Corrects the "five"
recorded last round.

> **`liftRes` is the single door the maximal trunk comes through — so it is the
> ONLY place fuel-argument monotonicity is consumed, on either side.**

It earns a shape structurally rather than as a list item: every pure worker's
monotonicity enters the monadic world **there and nowhere else**, so a missing
lemma is not a gap but a **severed connection between the two halves of the
proof** — the trunk's `_mono` results exist and cannot be spent.

**(2) THE WALKER'S EXPONENTIAL TIMEOUT: the real cause was TRANSPARENCY, not
dispatch shape.** Last round's recorded diagnosis (*"a search where a case
analysis was available"*) was the **plausible** one, not the measured one. Two
causes, found by looking: **`apply` at DEFAULT TRANSPARENCY whnf-unfolded tier
constants** hunting for an `ite` underneath, descending *through* `applyBuiltin`
— **the actual timeout was the whnf reconciliation of two 200-line bodies** —
plus **recursive backtracking re-planning a subtree per leaf failure**.

Three fixes, each aimed at one cause and none a budget: **`repeat'`** (one step
per goal, kept, so a leaf failure is an **open leaf** and never a parent
re-plan — that is what makes it **linear**); **the leaf closer FIRST, guarded by
`done`** (stops the transparency descent into named lemmas' definitions before it
starts); and **the early `refl` under `with_reducible`** (succeeds on syntactic
equality and **FAILS FAST** rather than attempting the 200-line whnf).

> **When a tactic is exponential, ask what it is UNFOLDING, not only what it is
> TRYING.** A backtracking search is visible in the tactic text; a transparency
> setting is not, and it was the expensive half.

Also: **`<f>.mutual_induct` exists** and concludes the **whole mutual conjunction
at once** — with the trap that **conjunct order is NOT source order**.

**(3) THE `Kont.fuel` CORRECTION WAS ITSELF WRONG — and the way it was wrong is
the sharper law.** `setDedup` **IS** reachable (via `applyBuiltin`'s set arm,
`Eval.lean:392`, two `K.fuel` sites; verified here — `setDedup_mono` is consumed
in `Obs.lean` through `le_liftRes`). The correcting grep had measured **"0 hits
FROM `evalCompareOpH`"**, **inheriting the frame of the very docstring it was
correcting** — re-answering the old question accurately instead of asking the
right one.

> **A measurement that CORRECTS a claim must not take its SCOPE from the claim it
> corrects. Sweep the whole surface, not the cited path.**

**This is the retrieval family's worst case**, because a correction carries
**more** authority than the claim it replaces: it arrives with a measurement
attached. Inheriting the scope makes the second number as wrong as the first
**and harder to doubt.** The fuelMono lane fixes the docstring in its landing
ticket, carrying that sentence in it.

## 2026-08-23-architecture-21 — The versioning exemplar is REALIZED; a falling split is correct; and deferrals need a double guard

Three from Go inch 2.

**(1) THE FAMILY-VERSIONING EXEMPLAR IS REALIZED, NOT PLANNED — the charter's
acceptance test is DISCHARGED.** One walker, **one world field different**:
`runUnder go1.21 loopVarProbe = some 1`, `go1.22 = some 3`, with the observable
being **POINTER IDENTITY** — **the same number the real toolchain gave** (1
distinct address under go1.21, 3 under go1.22). The model reproduces the
measurement rather than a story about it.

**This is the whole family-versioning thesis in one artifact**: the edition is a
**datum in the world**, not a directory; the walker is **shared**, not copied;
the delta is **one field**. §2.4's thin-siblings ruling and clause (4)'s
edition-as-data discharge together.

**AND THE NON-VACUITY PAIR IS NOW THE STANDARD.** Gated in **both directions** —
**go1.21 claiming 3 fails**, and **the counting loop breaking under 1.22 fails**
— because of a named trap: **freshening without copy-back passes every closure
test and corrupts ordinary loops.** A wrong implementation satisfying the
*interesting* half is exactly what a one-directional gate certifies.

> **Every version-delta claim carries a non-vacuity PAIR — the old behaviour must
> FAIL under the new edition, and the new behaviour must FAIL under the old.**

And the loop-variable set is **read off the init's locals, not hand-listed** —
the census discipline applied inside the semantics, since a hand-written list is
a second source of truth that drifts from the construct it describes.

**(2) A FALLING SPLIT IS CORRECT — the metric must not become a target.** Go's
math/interpreter split moved **63% → 58.6%**, and that is right: **fuel theorems
do not transport.**

> **A rung that adds fuel-bearing constructs moves the split DOWN. Holding it
> flat would mean fuel facts were written into spec-shaped statements.**

Goodhart with a specific mechanism: the ratio is a **diagnostic of where
statements live**, not a score. A lane optimising for a flat 65% would achieve it
by **smuggling interpreter facts into mathematical statements** — the exact
interleaving step 9 forbids, with the metric applauding. **Read a falling split
as evidence the discipline is holding** under a rung that genuinely added
interpreter surface.

**(3) DEFERRAL HYGIENE — the rule for every deferred construct.** A deferral is
cause 1 and must **stay** cause 1; the failure is that it **quietly becomes a UB
claim** (cause 2, which never retires). Go's `fallthrough` is the pattern: the
**census figure travels IN the refusal message** (4.0% corpus share, so the cost
is visible **at the point of refusal**), and it is **guarded TWICE — on the CLASS
and on `isUndefined`** — *so the deferral cannot quietly become a UB claim.*

**The double guard is the load-bearing half**: one guard proves the construct is
refused, the second proves **which kind of refusal it is** — the property that
would otherwise erode silently as a tier grows. **A deferral indistinguishable
from undefined behaviour has given up the one distinction §5.2 exists to keep.**

## 2026-08-23-architecture-22 — A transcribed expectation is a third implementation; and a census that could have overturned the plan

Three from Go inch 3, plus two riders.

**(1) EXPECTATION PROVENANCE — the sneakiest form of "agreement is not
evidence".** A differential table's expected column was **typed by hand, and it
PASSED.** The defect is invisible when committed and matures later:

> *"The whole claim is that two independent implementations agree, and a
> hand-copied expectation makes the Lean side the source of BOTH columns the
> moment someone 'fixes' a row."*

**A transcription is a third implementation nobody declared** — a human's reading
of the oracle, which degrades into the model's own output the first time a row is
adjusted to make a test pass. **Nothing fails; the differential simply stops
being one.**

> **A differential expectation must be GENERATED by the ORACLE side, never
> transcribed. It would have shipped looking identical and meaning less.**

The fix is the shape to copy: rows **`printf`'d from the compiled Go binary** and
**mechanically rewritten into `#guard` syntax** — the same provenance the refusal
census's expectation column already has (**written from CPython's measured
behaviour**). The two together make it general rather than a Python habit: **the
oracle writes its own column, in every tier.**

**(2) A PRICING CLIFF IN `--classify`, measured.** Adding **one new `Examples/`
subdirectory** widened classification from **four Go modules to the WHOLE
`Examples` library**: **91 s → 37 minutes, 25×.** It is a **cliff, not a slope**,
so a lane paying 91 s gets no warning before it pays 37 minutes. Recorded so it
is budgeted: **a new `Examples/` subdirectory is a scoping event**, and **the
cheap classify budgeted from yesterday's tenure is not the one you get today.**

**(3) A SEQUENCING DECISION EARNS A CENSUS THAT COULD HAVE OVERTURNED IT.** Go's
charter deferred concurrency; the walker census then found concurrency constructs
in **<1% of rung-1-reachable files** — agreeing with the decision **after the
fact**.

The agreement counts **because it was a real test**: run after the decision, over
the corpus, and it **could have come back the other way.** That is what separates
it from §5.4a's retrieval failures — *a grep that agrees with your prior* is
worthless when it could only ever have agreed; **a census that could have
overturned the plan and did not is evidence.**

**RIDERS.** The exemplar was found **by SEARCH over the corpus**
(`bigmod.bitLen`, chosen on FIPS provenance), so **the exemplar chose the
operators** — scope from the corpus, theorem from the exemplar, in that order,
which is *suites drive scope* actually followed rather than asserted. And the
**bitwise family was deliberately NOT declared**: **declaring an operator the
walker refuses would be a vocabulary claim the tier cannot honour** — deferral
hygiene applied to vocabulary, keeping the tier's **stated** surface equal to its
**actual** one, since a declared-but-refusing operator reads as coverage in every
table that counts declarations.

## 2026-08-23-architecture-23 — Data may carry the decision, not the scrutinee; and an audit has a third site

From pyc 3c-i-b's red — a **design wall, correctly reverted**.

**(1) THE DEFUNCTIONALIZATION LAW GAINS ITS MIRROR**, stated as one rule where
the law lives. The existing half says a continuation **may** become data. The
mirror says what that data may **not** be:

> **A pure plan may decide WHAT to do — but it must never supply a term the
> definition then RECURSES ON.**

The reason is the measure, and it differs by half: **in the FUELED half the plan
is free**, because **fuel is the measure** and the recursion decreases whatever
term it is handed; **in the FUEL-FREE half the measure IS THE SYNTAX**, and **a
plan-supplied term erases it** — a computed scrutinee is not a syntactic subterm
of anything.

> **Data may carry the DECISION; it may not carry the SCRUTINEE.**

That is **step 10's reconstructed node generalized**: a rebuilt node is merely
the most obvious way to compute a term the recursion then eats, and **any plan
producing one has the same effect on the measure.**

**(2) RIDER — THE PAYOFF CASE FOR WRITING *WHY* AT THE SITE.** The file's own
comment sat **three lines above the attempted edit**: *"the free-scrutinee
discipline is load-bearing twice over — it is also what keeps this block
structurally recursive."*

**This is the positive counterpart to §5.4's two docstring laws**, and the
distinction now sits in the doc so they are not read as *"do not write prose"*:

* a docstring asserting a **FACT about the world** (a reachable set, a case that
  cannot arise) is **a claim and needs a check**;
* a comment recording **WHY a constraint exists**, at the site it constrains, is
  **guidance** — it **cannot be wrong about the world because it makes no claim
  about the world**, and it is read **exactly when someone is about to violate
  it**.

**Write the second freely; gate the first.**

**(3) RIDER — THE CAPABILITY AUDIT HAS A THIRD SITE: INGESTION.** The corrected
design fuses at ingestion (`list(d.keys())` → `list(dictkeys(d))`, on the
`ListComp` precedent), so the capability lives in **the ingestion rewrite**, not
in either walker.

**An audit comparing only the two interpreters cannot see it** — both walkers are
innocent and the behaviour is decided before either runs. So the parity audit now
sweeps **trunk, presentation, AND ingestion rewrites**, and a capability found
missing on one side should prompt *"is this implemented as a rewrite over
there?"* **before** it is filed as an unported fix.

## 2026-08-23-architecture-24 — This lane's three audit findings, fixed; and the laws predicted where the defects are

The cross-tree audit (`docs/quality-audit-2026-08-23.md`, `00fe2dc`) filed three
rows against `family-architecture.md`. **All three verified here before fixing**
— the audit's own second register entry demands exactly that — and **one was
worse than reported.**

**F1 (`:418`) — UNDERSTATED, corrected.** The row named **one** private-path
violation. The one-grep answer finds **FIVE live ones**:
`docs/sv-construct-census.json:5` (a **committed machine-readable `corpus_path`
provenance field** — the worst, because a provenance field is *read by tools and
copied forward* where prose is only read by people), `docs/sv-charter.md:189`,
`docs/sv-corpus-coverage.md:5`, `docs/litreview/area-c-isa-models.md:9,213`, and
`docs/howto/add-a-spec-to-existing-code.md:159`. **Reporting the instance that
was noticed as the population is the §5.4a error**, committed by the section that
states it. A repo-wide grep belongs in `tools/check.sh`.

**F2 (`:346`) — the provenance law, violated by this document.** *"Settled at
98"* was true at `8f4fd65` (8 166 lines, 93+5) and false at `00fe2dc` (**8 562
lines, 96+10 = 106**). Row re-measured **and stamped with the revision**. The
fix is the **stamp**, not the refresh: **a stamped stale number is readable; an
unstamped current one rots silently.** Counts owed to a `--check` mode so the
registry drifts loudly.

**F3 (`:3631`) — my convicting example was invalidated by a landing I
documented.** `refusalOf` now reads `.error (.unsupported c _ _)` — **three
fields** — and returns `Option (RefusalCause SpecRef)`, **naming Core outright**.
The **Core payload landing** did it. Re-quoted as a **docs_check-gated block** so
it cannot drift again, and **the point restated so a signature change cannot
refute it**: a consumer reaches a constructor's shape **by destructuring it**,
and a module-import census cannot see that *whether or not* the consumer also
names the type. The row's count is corrected too: **11 lines across FIVE files**,
not three.

**REGISTER ENTRY 1 — §9.7's FIRST FULL INSTANCE, with the audit as its
artifact.** Of the 11 HIGH findings: **3 provenance, 4
identifier-in-instruments, 1 absence, 1 vacuous-guard, 2 docdrift.** **Not one
landed outside a family this document had already minted.**

> **The laws predicted where the defects are.**

That is the strongest available evidence the minting has been **measurement, not
taxonomy** — a family invented to describe one incident would not go on to locate
eleven more across seven lanes. Cadence parameter recorded: **the LENS LIST for
the next audit = the law families minted since the last one**; and **a family
that finds nothing on a sweep is itself a result** (either the discipline took,
or the lens is wrong).

**REGISTER ENTRY 2 — the verifier layer earned its cost, measurably.** **8 of 64
findings REFUTED**, and many confirmed **with corrections** — **severities moved
in both directions**, consequences replaced.

> **A finding un-re-read is a claim, not a finding.**

Both halves matter: publishing the 8 would have sent lanes to fix non-defects;
publishing the corrected ones uncorrected would have sent them to fix real
defects **for the wrong reason**, which is worse because **it survives the fix**.
And severities moving **both** ways is the tell the verifier was working rather
than rubber-stamping — **a layer that only ever downgrades is a filter, not a
check.**

## 2026-08-23-architecture-25 — The audit-response norm: the remedy for a provenance gap is provenance, never reconstruction

Rider from SV's dispositions, landed verbatim beside "a finding un-re-read is a
claim, not a finding" (§5.4a). It closes an **incentive loophole the audit
creates by existing**: an audit that demands provenance applies pressure to
**manufacture** provenance, because a dangling citation is embarrassing and a
plausible reconstructed table makes the embarrassment go away.

SV had two citations resolving to nothing and the backing Xcelium host
unreachable. They corrected the citations to **unreproducible-pending-access**
rather than rebuilding the table:

> **Fabricating rows to satisfy a provenance audit would be that audit's own
> defect, one level up. A dangling pointer replaced by an honest 'lost, and here
> is what would restore it' is a real fix; a fabricated table is not.**

> **The remedy for a provenance gap is PROVENANCE, never RECONSTRUCTION.**

**The reconstructed table is strictly worse than the dangling pointer it
replaces, and the audit is what makes it so.** A dangling pointer **announces
its own failure**; a fabricated one **passes every future check** and is
indistinguishable from a measurement until someone tries to act on it. The
honest disposition keeps the gap **visible and closeable** — it names the access
that would reopen it. **Closing a finding is not the goal: the finding is closed
when the claim is true**, and *"we cannot currently reproduce this"* is a true
claim.

## 2026-08-23-architecture-26 — A transcription is a copy with a timestamp; and every gate was green while the file lied

Two landings from the SoftFloat lane's audit response (`046d9dc`, branch
`softfloat-m1`; audit row `docs/quality-audit-2026-08-23.md` "## softfloat",
HIGH). Incident and dispositions: `docs/backlog/softfloat.md`
`2026-08-23-softfloat-11`.

**(1) THE TRANSCRIPTION LAW — §5.4, a new bullet beside the two docstring
laws.** `harness/softfloat/probe_es_unblock.lean` transcribed ES's
`numberToString` under the label *"as landed"*; ES committed the routing
**six minutes thirty later** (`f255c03` `23:47:56` → `9dab312` `23:54:26`,
both verified here against the log), and the probe went on presenting the
**pre-unblock** body as the landed one with its expected-FAIL rows under the
heading *"The landed version"*. Anyone running it concluded the unblock was
UNLANDED — the opposite of what the lane had just measured, in the file whose
purpose was to demonstrate it.

> **A cross-lane transcription must carry a TRIPWIRE in the gate set, or it is
> a lie with a fuse.**

The half-life is the argument: **six minutes is short enough that "be careful"
is not a control**, because no amount of care makes a copy notice a commit. The
lane's `--check-transcriptions` gate is the shape to copy, its own failure path
exercised in the self-test.

**FOUR CONVERGENCES, and the first is the one worth the landing.** §5.3 already
carried a transcription law — *a transcription is a third implementation nobody
declared* — aimed at hand-copied **oracle expectations**. This one is aimed at
another **lane's source**. Stating the pair gives the general rule and the
reason the remedies differ: **an expectation is a VALUE and can be GENERATED; a
source line is TEXT, cannot be, and must be GATED.** A forward pointer now sits
in §5.3 so a lane meeting either meets the other. The other three: *a check that
has never failed is a design, not a control* is §7.1a's amendment line
re-derived about gates; the lane's `numberStringPreUnblock` rename is §5.4's
**construct-not-verdict** identifier law (*"as landed"* is a status, and a
status has a shelf life; a **vintage** does not).

**AND ONE SHARPENING THE DISPATCH DID NOT CARRY: STAMP THE COPY FIRST.** *"As
landed"* is a present-tense claim about a file you do not own; *"as landed at
`f255c03`"* stays true forever. **A stamped copy goes OUT OF DATE; an unstamped
one goes WRONG.** So the control has two parts doing different jobs — **the
stamp makes a stale copy READABLE, the tripwire makes it LOUD** — and only the
second is a gate. That is `2026-08-23-architecture-24`'s *the fix is the stamp,
not the refresh* arriving at a copy instead of at a count, and it is MEAS-10
owed by this document.

**This landing's own transcription is gated**, which is the law applied to
itself: the ES half is quoted as two `docs_check`-marked blocks (the routed
`numberToString`, and the `%` arm — **WITHDRAWN**, a fact no line-number
citation could have carried). **State stamp:** the SoftFloat gate is on
`softfloat-m1` and **not on master**, so it is described and not quoted; master
still carries the rotted probe text as of this landing.

**(2) GATE TOPOLOGY — new §5.4b.** The second half of the same incident, and
the more general one. The lane had **four** gates, all green throughout:

> **Every gate was green while the file said the opposite of the truth, because
> none of them was pointed at the claim that had rotted.**

`probe_es_unblock.lean` was **expected to error** and did; its sibling was
expected clean and was; `docs_check` gates **marked blocks in `.md`** and this
was a comment in a `.lean`; the census gated **call sites**, not **citations**.
Four gates, four elsewheres.

> **ENUMERATE WHAT EACH GATE IS POINTED AT. A claim no gate points at is
> UNGATED, however green the neighbourhood.**

Two things added to the dispatch. First, **a dense gate set is worse than a
sparse one here** — the more gates surround a claim, the more gated it looks,
and the inference runs neighbourhood → claim without touching a pointer; so
**a gate set is audited by ENUMERATION, never by execution**, because
re-running only re-answers the questions already asked. Second, the
expected-error corollary is stated with its limit: pinning the COUNT is
**necessary and not sufficient** — two errors a probe was built to have and two
it acquired are the same number, so the count **bounds** the drift and does not
**identify** it, and an expected-error file carrying a transcription still owes
the tripwire. The §5.4b enumeration table is the practical form, and it takes
each gate's scope **from the gate's own words** where it states them
(`tools/docs_check.py`'s docstring, quoted as a checked block).

**RIDER — THE ANNOTATION NORM, landed with it.** The lane annotated its dated
entry `2026-08-22-softfloat-1` rather than rewriting it:

> **The measurement was right as taken; only its tense was wrong.**

Recorded because rewriting would have destroyed the evidence for the very law
being minted: **that the text was TRUE WHEN WRITTEN is the entire finding**, and
a rewritten entry reads as a lane that simply erred — a different and weaker
story. **Present-tense prose is FIXED; a dated record of a past measurement is
ANNOTATED.** Same instinct as §7.1a's register carrying two rows marked **LOST**
instead of two plausible reconstructions.

**Index:** MEAS-64 … MEAS-69 in `docs/law-index.md`.

## 2026-08-23-architecture-27 — A published number is a second artifact; a check that cannot fire; and an instrument that selected itself

Three from the QoL lane's audit closeout (`12386db`, `ec48c98`, `9162c6b`,
`a9f7867`), plus the `leanlex` consolidation. Every claim below re-checked
against the tree here before landing, and **two of them came out different from
the dispatch.**

**(1) THE PUBLISHED NUMBER — §5.4a, fifth row of the identifier table.**
`substrate.sh`'s `REF_LOCAL` counted `| unsupported` **match arms inside
proofs** as declarations: **Python 82 → 4** (~20×), **Sv 17 → 11**, **C 2/6 →
1/7**, `REF_CORE` **6 → 5**. Two things landed, not one.

The **sharpening** of the pattern-position law, because the position here was
the right *kind* and the wrong *scope* — a constructor and a match arm are the
same characters:

> **A pattern position is a position IN A DECLARATION, never a shape in a file.
> The same characters in a different scope are a different fact.**

And the part the other four instances do not have — **the count had been
published**, in `docs/backlog/qol.md` `2026-08-23-qol-21`'s live table
(*"6/82"*):

> **A number a gate PUBLISHED is a SECOND ARTIFACT. Correcting the instrument
> corrects the next run; the published figure is corrected where it was
> published, or it stands.**

That is `2026-08-23-architecture-24`'s *the fix is the stamp, not the refresh*
extended from a hand-written number to a **tool's output**, and the correction
is made under `2026-08-23-architecture-26`'s annotation norm — annotate the
published row with the re-measured number and the sha, never silently refresh
it. **The lane published the correction against itself** (*"the correction is
large and it is mine to own"*), which is why this is a norm and not a reprimand.
**The residue — `qol-21`'s table still reads `6/82` — is filed back as INBOUND
`2026-08-23-architecture-27` in `docs/backlog/qol.md`** (§9.5a, §9.5b: file the
residue, not the report).

**(2) A CHECK THAT CANNOT FIRE — §9.7, the no-code closure.** QoL closed two
audit rows with no diff: `triad.sh:497` **verified already fixed** by `4c710e3`
(earned by re-running the row's own example, not by reading the diff), and the
`a6-guard` wiring **declined** because `triad.sh` never rewrites the tree.

> **A check that cannot fire is the audit's own VACUOUS category.**

§5.3's ruling aimed at gates instead of verdicts — and **this document had
already made the move once without naming it**: §2.4's STMT-61 is reported as a
column (`7/0`) rather than built as a comparison that cannot fire. Wiring the
guard raises the gate COUNT without raising COVERAGE, which is MEAS-9 and, in
§5.4b's vocabulary, a gate with no claim at the far end of its pointer.

**The condition is the whole norm, and it is the half a lane will skip:**

> **A no-code closure is CLOSED when the AUDIT FILE carries the reason.
> Anywhere else it is a lane's private opinion of a public row.**

A row closed only in the lane's ledger is invisible to the next sweep, which
re-files it — costing an investigation and, worse, the credibility of every
other row beside it.

**(3) THE INSTRUMENT THAT SELECTED ITSELF — §5.4, with a near-miss note under
§7.1a A11.** `ci.sh`'s new self-test step selected tools with
`grep -q -- '--self-test'` and matched **`ci.sh` itself** — the function doing
the matching names the flag in its own text — so CI re-entered CI and started an
**unticketed `lake` build**. *"It hung, which is the only reason I looked."*

> **Any content pattern you can select on, you will eventually WRITE DOWN in
> the selecting file — so the file matches it. Only IDENTITY excludes.**

**The repair is the proof**: narrowed to match a *handler*, the lane's own
explanatory **comment** then contained the handler string and the pattern
re-matched, so an explicit `ci.sh` belt is load-bearing. **The narrowing failed
the same way twice**, which is what makes it structural rather than a sloppy
regex. And the detection channel is the alarming part — **no error, only a
hang**: a self-selecting instrument fails by recursion, and recursion is silent
until it is expensive.

Filed under §7.1a **as an observed near-miss, NOT as a new amendment**, because
the amendment that governs it already exists: A11 covers all Lean execution, and
the gap is that **a tool that can start Lean is a lane that never queued** —
A9's queue disciplines lanes, and tools do not take tickets. The cheap fix is
the one taken: a per-tool timeout, so a hang cannot become a tenure.

**(4) `tools/leanlex.sh` — MEAS-28's first consolidation, AND THE DISPATCH'S
NUMBER CORRECTED.** *Four private copies retired* is not what happened, and
landing it would have put a wrong number in the gate's own ledger — the trap
minted three paragraphs earlier, one level up. Measured here:

* **two copies were never grown** — `substrate.sh` needed a third and fourth and
  sourced the shared file instead. That is the consolidation.
* **two copies are still live** — `sites.sh:160` `code_hits` and
  `triad.sh:518` `code_mentions`, the latter's own comment calling itself
  *"third copy of the comment walker in this tree"*. They retire **BY TOUCH**
  (§9.2), which is this document's rule and not a shortfall.

**Two avoided, two owed.** Only `substrate.sh` sources `leanlex.sh` today
(`grep -rln leanlex tools/`).

**Index:** MEAS-70 … MEAS-75.

## 2026-08-23-architecture-28 — The guard was never in those processes; and a correct refusal is not a mitigation

The CI re-entrancy incident's laws, from QoL's closure (`docs/backlog/qol.md`
`2026-08-23-qol-36`). Four dispatched, four landed, plus two findings this lane
made while landing them.

**(1) §7.1a 16.2's SECOND INSTANCE — it convicted its own author.** The lane
that carries 16.2 diagnosed the first near-miss, added a belt, verified it
green, and **left its own hung pre-belt process running**; that process had the
old code in memory and spawned **26 `ci.sh`**, each an unticketed `lake build`,
load ~30 for twenty minutes.

> **The guard never failed, because the guard was never in those processes.**

Rider added to the amendment:

> **The rule applies to YOUR OWN runners FIRST — the author's surviving process
> is the likeliest in the tree to predate the amendment.**

It was started before the fix existed, by the person who then stopped thinking
about it. The **incremental-read hazard** fired in the same window (the lane
edited `ci.sh` under 26 live executors) and its admission is recorded verbatim
rather than resolved: *"I cannot cleanly separate 'ran the old code' from 'read
a shifted file'."* **An incident with two indistinguishable causes has two
causes** — picking one after the fact would be a reconstruction (§5.4a).

**(2) THE INTERFACE LAW — §5.4, a new bullet.**

> **Ignoring an unknown flag is how a self-test request became a full build.**

An entry point that executes its **default** on an unrecognized argument
converts every typo into its **most expensive path**. `ci.sh` now refuses all
arguments at lines 31/51/58, ahead of the first step at 129 — because a refusal
that runs after the work has started is a report. Stated with the
over-correction blocked: **the allowlist is not the defect** (`--verify-guards`
is fine); the defect is the **fallthrough branch**, which has exactly one safe
value and it is an error. This is *every refusal path RUN, not admired* moved
one step earlier: **the argument parser is a refusal path, and the first one
every caller touches.**

**(3) THE A13 COROLLARY, and the sharper half is mine to state.** The clone was
a plain `git clone`, never seeded, so the accident built Mathlib **from zero**
— 3.2 GB, *not an invalidated cache but a cache that never existed*.

> **An unseeded clone is permanently ONE ACCIDENT away from a full Mathlib
> build.**

And the part worth more than the corollary: **`check.sh --iterate` had been
refusing that clone as COLD all along, correctly, every time — and the hazard
sat behind the refusal untouched.**

> **A correct refusal is not a mitigation. Refusing to operate on a hazardous
> state leaves the hazard for whoever does not check.**

A distinct failure shape from the families minted so far: the usual defect is a
guard that **fails to fire**; this one **fired perfectly and bought nothing**,
because it protected the caller rather than the machine. A refusal is a control
on **one path**; the state it refuses is reachable from every other.

**(4) THE RULING, landed in §7.1a and in §7's tools table.** `ci.sh`'s
`lake-build` step is **host-gated**: builds under `GITHUB_ACTIONS`, locally
**skips loudly to `tools/triad.sh`**, no local override reaching a bare `lake`.

> **A step that can start Lean names the HOST it is allowed to start it on. Off
> that host it does not degrade quietly to a smaller build; it REFUSES and
> names the ticketed path.**

The three-layer fix generalizes too, and the middle layer is the transferable
one: **a guard against RE-ENTRY must live in something INHERITED, not something
PASSED** — depth and argv are what the recursion controls; the environment is
what it cannot rewrite. `tools/ci.sh` is now IN the lane-tools table, because
its absence made the table's *"every tool below runs no Lean"* read as coverage:
**a documented exception is an exception; a tool left out of the table is an
undocumented one** (§5.4b).

**(5) FINDING — MY OWN A11 NOTE WAS OVERTAKEN THE SAME DAY.** Yesterday's
landing called this *"A11's first near-miss"*. Hours later it ran 26 deep. The
law was right and **its severity was understated**; recorded next to what it
became rather than edited away, which is the charter-prose half of
`2026-08-23-architecture-26`'s split (present-tense prose is fixed — but a
wrong estimate of *how bad* something is, is worth leaving visible).

**(6) FINDING — §9.5a's WATCH ITEM HAS FIRED, AND MASTER SHIPPED CONFLICT
MARKERS.** My INBOUND append to `docs/backlog/qol.md` raced the owner's
`qol-36`. The first occurrence (`es.md`) was a rebase conflict — loud,
blocking, resolved. This one was **resolved wrongly and committed**: `47544f1`
shipped `docs/backlog/qol.md` containing `<<<<<<< HEAD`, `=======` and
`>>>>>>> cc3d9ec`. **Fixed here**, keeping both halves in order (`qol-36`, then
the INBOUND block).

> **A race that conflicts is a nuisance. A race that MERGES WRONG AND COMMITS
> is a defect, and the second is what a rate buys you.**

**And every gate was green over a file full of conflict markers** — §5.4b on
this repository's own documents: `docs_check` gates marked code blocks,
`backlog-index.sh` gates the index's freshness, and **nothing is pointed at
"is this markdown structurally intact"**. Residue filed to QoL: a `^<<<<<<<` /
`^=======$` / `^>>>>>>> ` grep over `docs/**` in `tools/ci.sh`.

**THE CONTINGENCY IS NOT SIMPLY TRIGGERED, THOUGH — it has an unstated
precondition, and landing the move blind would be a silent-absence defect.**
`tools/backlog-index.sh` globs `docs/backlog/*.md` **one level deep**, so
INBOUND entries moved to `docs/backlog/inbound/<owner>.md` would **vanish from
the generated index** — defeating the property the convention exists for. The
move is therefore **conditional on the generator learning the subdirectory**.
Until then the convention stands, with one free tightening that would have
prevented this instance: **an INBOUND append is a separate commit, made
immediately, never batched behind other work** — the window is the hazard, and
it is the only part a filer controls.

**LANDED ON A MOVING TREE, and the second race is recorded too.** While this
entry was being written the QoL lane pushed `a1bb01e` — the ruling
**implemented** (`qol-37`) and `lean-qol` **A13-seeded at last**. Two
consequences: both charter paragraphs are **stamped with that sha** so neither
asserts a stale present tense (MEAS-10), and the rebase **conflicted on
`qol.md` a second time in one day**. `a1bb01e` had appended `qol-37` *around*
the unresolved markers rather than resolving them, so master carried them from
`47544f1` until this landing. Resolved keeping **all three** blocks in order:
`qol-36`, `qol-37`, INBOUND.

**That is the watch item firing twice within the same hour**, and it is the
argument for the free tightening above rather than for the file move: the move
is blocked on the generator's glob, while *"file the INBOUND in its own
immediate commit"* is available today and shrinks the only window a filer owns.

**Index:** MEAS-76, MEAS-77, OPS-65 … OPS-68.

## 2026-08-23-architecture-29 — An instrument optimization is proved by output equality; and §5.4b's first two catches

Four from the QoL lane (`7a4876f`, `8fb27db`, `f5b35a0`), plus the residue this
lane filed yesterday coming back closed (`bf329ad`).

**(1) §5.4a — THE PROVENANCE LAW REACHES THE INSTRUMENT'S OWN COST.**
`laws.sh` timed at **54 s, 1m23, 1m55, then past two minutes** on an input that
had barely changed: **spawn-bound**, ~8 000 spawns at four to six per law, and
spawn latency scales with machine load.

> **The instrument's cost was a measurement of somebody else's work.**

New row in the instance table. Two things about the response were worth more
than the fix. **It was profiled first, and the profile refuted the author's
guess** — three slices came back uniform at ~1.15 s, so no subset of laws was
pathological and a fix aimed at the guess would have optimized the fast part.
And the optimization was accepted on **output equality**: 231/118/1
**byte-identical**, runtime 62 s.

> **An instrument optimization is proved by OUTPUT EQUALITY, never by speed.**

**And the sharpening, which is the part I would not want a lane to miss:** the
faster algorithm was also the **simpler** one. `index()` would have been faster
still and would have **dropped the whole-token rule** — *exactly how `§9` came
to match `§9.5`* and mis-credited a law to seven tools (§9.7). So: **the
optimization that is also a simplification is the dangerous one, because it
deletes a distinction the previous version was paying for.** The anti-regression
is a self-test row (`§9` counts 0 where a ledger says `§9.5` twice; `§9.5`
counts 2), not a comment — a comment would not survive the next rewrite.

**(2) §5.4b — THE HONESTY RIDER, from `--gate-set`'s own first line.**

> **A guessed pointer is worse than a missing one, because it makes a claim
> look COVERED.**

`UNRESOLVED` is the only honest value for a runtime-computed gate target (16
declared, 2 UNRESOLVED, both shell functions whose targets really are computed).
It is *the remedy for a provenance gap is provenance* arriving at a gate set.

**And §5.4b's "gate's own words" clause is now MEASURED rather than
recommended**: reading only the declaration left `.md` looking orphaned while
`docs_check` was pointed squarely at it; reading the script's header too took
the orphan list **from five kinds to one**. Four of five orphans were the
enumerator's blind spot, not the tree's. Also recorded: `gate_rows` emitted five
tab-separated fields with two empty placeholders, and a tab is whitespace, so
bash collapsed them — **an empty field in a whitespace-separated record is not a
field** — and the reason it was caught is its **direction**: it erred toward
alarm. The same collapse silently *attributing* gates would have read as
coverage and survived.

**(3) §5.4b's FIRST TWO CATCHES, one mechanical and one by hand.**
`harness/sv_round_trip.py` appears in `ci.sh` **zero times against 18 `.sv`
files** — a whole KIND with no gate, found by the instrument built from the
section **one day after it was written**.

> **ANNOTATION (2026-08-23, `ea6f667`; entry NOT rewritten, per
> `2026-08-23-architecture-26`).** This paragraph's headline was **half an
> instrument artifact**. `gate_rows` anchored at column 0, so all **28 indented
> (host-gated) gates were invisible** — **16 enumerated, 44 after the fix**,
> `lake-build` among them. The counterfactual was **run**: the new `laws.sh`
> against the **old** `ci.sh` gives **43 gates and no orphan kinds**, so
> *".sv has no gate"* was the **enumerator's blind spot, not the tree's gap**.
> **What survives is narrower and real**: both `.sv` rows are simulator-gated
> and SKIP on a stock runner, so **on CI `.sv` had no gate that RUNS**, and the
> wiring was right for that reason. `sv_round_trip.py` genuinely was absent
> from `ci.sh` and is now wired. **The measurement was right as taken; the
> claim built on it was too wide** — corrected in §5.4b and carried forward in
> `2026-08-23-architecture-32`. And the Wasm lane ran the enumeration
by hand on its own four gates (`886ede9`): its headline *"5 live obligations"*
was pointed at by one text scanner **that cannot see whether the file
elaborates**, and was ungated **in exactly the dimension that later refuted
it**. Three censuses green, deterministic, refusal paths executed — the
dense-neighbourhood trap, literally. **Neither catch needed a new failure; both
needed someone to write the pointer list down.**

**(4) §5.4a + §7's tools table — TWO TOOLS THAT DISAGREED ABOUT ONE FILE.**
`check.sh` read `lakefile.toml` and called a repo-root `.lean` scratch;
`triad.sh` hard-coded the globs and warned about the same file. It warned rather
than refused, **but two protocol tools disagreeing about one file eventually
gets trusted in the wrong direction.**

> **When two tools disagree about a fact, neither is the authority. Find the
> artifact that DEFINES the fact, and let exactly one reader parse it.**

`tools/lakeinfo.sh` is that reader, sourced by both (MEAS-28). **The
transferable half is that the fix went deeper than the classifier**:
`lean_glob_offenders`'s predicate asked *"is this not-docs?"* while its message
named a lake glob — so **a guard must ask the question its MESSAGE claims to be
answering.** *"The warning names a lake glob, so the LAKEFILE decides it."*

**(5) §9.7 — A FIXTURE IS NOT ENFORCEMENT**, minted within an hour of its cause:
a self-test row naming A15 made `laws.sh` credit **itself** as A15's gate. The
self-test region is stripped before attribution now. That is §5.4's
self-selection law in the attribution direction — **a tool that searches for
text will find the text it contains, and the copy it most likely contains is the
one it was built to recognize.** Landed with `--budget`'s honest partial: past
the budget every count is a **FLOOR**, and the verdict is written to a **file**,
because a subshell's variable does not survive the subshell.

**RESIDUE CLOSED.** `2026-08-23-architecture-28`'s INBOUND — the conflict-marker
gate — landed in `bf329ad`: one `git grep` over the tracked tree, failing on any
hit, **verified in both directions**, with its single possible false positive (a
setext underline of exactly seven `=`) **named rather than discovered**. Filed
Saturday, gated the same day; recorded because *fixes live in gates* is worth a
data point when it works.

**Index:** MEAS-78 … MEAS-85.

## 2026-08-23-architecture-30 — Heartbeats over wall time; one execution, two projections; and a shared name is worth an import

Four from the fuelMono lane, **staged on ticket 40057**. Every one is landed
**conditional on that landing** and says so at the site

> **ANNOTATION (`6b91a8d`): the ticket LANDED, and all four conditional stamps
> in the charter are discharged** — `bind_apply` in `Substrate.lean`, the
> `callInRaw`/`ofHalt` projection pair, the heartbeats measurement, and the
> `Order.lean`-not-`Outcome.lean` placement. Recorded rather than deleted,
> because a stamp that is removed silently leaves no evidence that the claim was
> ever conditional.

 — a law citing a tree
that has not landed is a claim about a branch, and §5.4a's state stamp is the
difference between recording that and pretending otherwise.

**(1) §5.4a — THE MEASUREMENT'S UNIT.** The instance landed an hour earlier
(`laws.sh` spawn-bound, `2026-08-23-architecture-29`) diagnosed the disease:
an instrument's runtime is partly a reading of the machine. This one prescribes
the cure.

> **Heartbeats are a DETERMINISTIC step count; wall time is not. On a shared
> box, report the deterministic half and SAY WHY the other half was dropped.**

Measured: **both arms time out at 1M heartbeats against the REAL tree** — a
number that does not move when another lane starts a build. It **replaces the
spike's `VOID` headline**, and the judgments-not-`mvcgen` method decision now
rests on a **tree-level** number rather than a spike's. The clause I added:
**dropping wall time is not hiding it, but an unexplained omission is** — a
reader cannot tell a dropped measurement from one never taken, so MEAS-10
applies to the *absent* half as much as the quoted one.

**RIDER — a probe that errors prints `sorryAx`, so a probe cannot certify its
own definitions.** The certification comes from **the tree's green build
ledger**. MEAS-11 with the artifact named, which is §7.1a's one-second-build
move: name the artifact whose existence success would have produced.

**(2) §5.2 — ONE EXECUTION, TWO PROJECTIONS.** A model reporting a refusal
*class* beside its outcome has two answers about one event, which is the shape
that drifts. `callInRaw` projected two ways with `callInMono_eq_ofHalt` tying
them: **the two answers cannot drift**, because the class is not extra data
about the run — it is a **view** of it.

And `refusalClass_isSome_iff` makes the field's **presence a theorem**:
**absence means the run did not refuse, never "refused, unclassified."** Worth
the theorem because the convention fails in the direction §5.2 exists to
prevent — an unclassified refusal is invisible to every per-cause count while
the run *was* a refusal, and the scoreboard reads *"no refusals of that kind"*.
Silent absence inside the verdict system.

**And the census's `WHITELIST_CLASS` is now cross-checked by the interpreter
itself**, which is the half that generalizes:

> **A table asserting how the interpreter classifies is an UNFALSIFIABLE CLAIM
> ABOUT the interpreter — until the interpreter is asked to confirm it.**

§5.4's docstring laws in table form: a claim about the world is checked data or
prose that goes stale silently, and the fix is to let the thing being described
answer the question.

**(3) §2.4 — A NEW CLAUSE (1a), the companion to census-gated placement.**
Clause (1) prices **separating** two things; nothing priced **joining** them.

> **A SHARED NAME IS WORTH AN IMPORT; IT IS NOT WORTH RELOCATING THE TRUNK'S
> ELABORATION COST. Check whose CLOSURE a file sits in before deciding two
> things belong side by side.**

Measured: instances landed in `Outcome` §8 rather than beside `FlatLe`, because
the tidier placement **dragged `Std.Do` into 65 `Examples` closures**. Nothing
would have failed — that is the hazard. **A placement decision made on naming
grounds pays in elaboration time across every downstream file, and the bill
arrives on lanes that never made the decision.** Practical form is a grep, not
a judgment call: list who imports the destination first. MEAS-1 applied to a
decision that does not look like it has a price.

**(4) COOKBOOK ENTRY 22 — opening the monad stack.** *Once, in the module where
the stack is DEFINED* — not zero times (something must connect abstraction to
representation) and not twice (two openings are two definitions kept in step by
hand). **The tell that it is being violated is a proof that unfolds
`Functor.map`**: a proof reasoning about the stack's plumbing in a module with
no business knowing the plumbing exists. Written as the per-module form of
§3.4's *one monad, one `vcgen`*, and the entry says to treat the unfold as a
signal to add a lemma where the stack is defined rather than as a step to keep.

The cookbook's table gains row 22. `2026-08-22-qol-2`'s title still says *"21
claim shapes"* and is **left alone**: it is a dated record and it was right as
taken (`2026-08-23-architecture-26`).

**Index:** MEAS-86 … MEAS-89, STMT-101, STMT-102, PROOF-56.

## 2026-08-23-architecture-31 — A false blanket claim hides the real gap; and cite by name, not by offset

Two from the pyc lane's audit triage (**staged on its queued ticket**; landed
conditional on that landing and stated so at each site), plus the state
statement they asked to have somewhere a newcomer reads.

**(1) §5.4 — THE SECOND MEASURED INSTANCE OF *a docstring that argues a case
away is a claim*, and it carries the worse half.**
`Examples/python/bench_bisect/spec.lean` asserted the live CPython oracle
**could not take** its cases. It could — since the batch protocol — and the
truth was a gap **far smaller than the claim**: nine rows added, **exactly ONE
genuinely unreachable**, now whitelisted **with its reason** (2026-08-23 audit,
`## python`, HIGH).

> **A false blanket claim hides the real gap — the gap was far smaller than the
> claim, and THE CLAIM IS WHY NOBODY LOOKED.**

**The self-preserving property is what I added and what makes it worse than an
ordinary wrong docstring**: a gap with a stated cause **is not re-measured**. An
unexplained gap nags; an explained one is closed business. The false
explanation does not merely misinform — it removes the incentive to look, and
goes on doing so for as long as it stands.

**And the second addition ties it to the transcription law**: the claim was
about **another component's capability**, so it rotted with nobody touching it
— true when written, false once the harness gained the batch protocol. **A
capability claim about a component you do not own is a transcription with a
timestamp**, on the same schedule, for the same reason, with the same remedy:
check it against the component. The nine rows that now run against the oracle
*are* that check.

**(2) §5.4 + §9.7 — CITE BY NAME, and the third kind of legitimate no-code
closure.** An audit row asked for stale line-number citations to be re-numbered
and was **declined, correctly**:

> **Fixing offsets buys ONE LANDING of accuracy. The durable fix is lemma
> NAMES.**

Line numbers rot on every insertion above them, by anyone, forever. This also
explains a decision made two landings ago that I had only justified locally:
the `%` row had to be **re-stated** rather than re-numbered, because *"the arm
is WITHDRAWN"* is a fact **no line number can carry at any offset**.

So §9.7's no-code closures gain a third kind beside VERIFIED-ALREADY-FIXED and
WOULD-BE-VACUOUS: **THE REQUESTED FIX IS NOT THE DURABLE ONE.**

> **A row is closed when the CLAIM is true, not when the requested edit has
> been made. An audit prescribes a remedy; the owner may substitute a better
> one, and must SAY WHICH.**

The must-say is the safeguard — an unnamed substitution reads, one audit later,
exactly like a row nobody acted on. And the three kinds do not all point the
same way: the vacuous closure refuses to do something **useless**, this one
refuses to do something **temporary**, and both are available only to an owner
who verified the row first.

**(3) §3.4 — THE PYTHON TIER'S STATE, one sentence, at the top of the section a
newcomer opens first.**

> **Executable behaviour is the REBUILD's; proved behaviour is still the
> TRUNK's; the two are held together by the PURE WORKERS they share — which is
> why a capability opening reaches the harnesses instantly and the proof layer
> not at all.**

Landed with the reading that makes it usable rather than merely true: **the
asymmetry is the design working, not a gap** — and it is why *"the rebuild can
do it"* is never an argument that the trunk can. Cross-referenced to
`2026-08-23-architecture-23`'s third audit site, since the same asymmetry is why
a capability audit must sweep the **ingestion rewrites** and not only the two
walkers.

**Index:** MEAS-90 … MEAS-92.

## 2026-08-23-architecture-32 — The enumeration's first finding was about the enumerator

A correction to this lane's own `f587ec2`, from QoL's `ea6f667`. The dated entry
`2026-08-23-architecture-29` is **annotated, not rewritten**; §5.4b's
present-tense prose is **corrected**, with the correction stated as a
correction. That split is `2026-08-23-architecture-26`'s, applied to itself for
the first time.

**WHAT WAS WRONG.** `f587ec2` recorded `sv_round_trip.py` as §5.4b's *first
mechanical catch* under the headline *".sv has no gate"*. `gate_rows` anchored
its match at **column 0**, so every **host-gated** gate — declared inside a
function or an `if`, therefore indented — was invisible: **16 enumerated, 44
after the fix**, including **`lake-build` itself**. An auditor reading the
16-row list would have concluded CI does not gate the build.

**THE COUNTERFACTUAL WAS RUN, NOT ASSUMED**: new `laws.sh` against the **old**
`ci.sh` → **43 gates, NO orphan kinds**. `sv-harness`/`sv2-harness` had pointed
at `.sv` all along and the anchor hid them.

> **A new instrument's FIRST finding is the one to re-run against the old
> input.**

**AND THE FLATTERING DIRECTION IS NOT THE USUAL ONE — it flatters the
INSTRUMENT, not the tree.** A day-old tool reporting a dramatic gap in somebody
else's work is the one output its author will not doubt: the tool justifying its
own existence. That is *a finding un-re-read is a claim, not a finding* (§5.4a)
aimed at the enumerator, and the counterfactual is the scope-inheritance rule
from the same section implemented — *a measurement that corrects a claim must
not take its scope from the claim it corrects*. **Running the new tool on the
old input is output-equality (MEAS-78) in the correction direction: the only way
to separate what the FIX changed from what the TREE changed.**

**WHAT SURVIVES, and the disposition was right either way.** Both `.sv` rows are
**simulator-gated and SKIP on a stock runner**, so **on CI `.sv` had no gate
that RUNS**; `sv_round_trip.py` genuinely appeared in `ci.sh` zero times against
21 committed envelopes and is now wired. **The disposition was correct and its
published justification was not** — which is its own small law, and the reason
the correction is worth a landing rather than a footnote: *a right action taken
for a wrong stated reason survives the fix, and the next lane inherits the
reason.*

**THE COUSIN LAW, and it is what makes §5.4b's pointer list honest: A
DECLARATION IS NOT A CALL.** A gate declared inside a never-called function
enumerates perfectly. With the `.sv` narrowing beside it, the list has **four
states, and "green" reports only the last**: **DECLARED → CALLED → RUN ON THIS
HOST → POINTED AT THE CLAIM**, each step losing members. Enumeration establishes
only the first; the call site is pinned separately (a `--verify-guards` row,
meanwhile), and the host question is answered by the skip discriminator.

> **A gate set audited only by ENUMERATION over-reports; one audited only by
> EXECUTION under-reports.**

That is a genuine amendment to §5.4b as I first wrote it — the section said *a
gate set is audited by enumeration, never by execution*, which is right about
**coverage** and silent about **liveness**. Both sentences now stand, with the
ladder between them.

**AND *A FIXTURE IS NOT ENFORCEMENT* (MEAS-84) REACHED A SECOND SITE**: the
`--verify-guards` region is cut inside `gate_rows`, deliberately **not** inside
the citation counter, whose numbers were not that inch's to move. A law arriving
at a second site with its blast radius bounded on purpose is the by-touch
discipline (§9.2) working.

**ONE MORE NUMBER CORRECTED WHILE HERE.** §5.4b's *"16 gates declared, 2
UNRESOLVED"* — landed by me in `f587ec2` — was the pre-fix count. Now **44, 2
UNRESOLVED**, and **stamped with the sha**, because a number that has already
moved once is exactly the number that needs its state carried (MEAS-10). The
`UNRESOLVED` pair is unchanged, which is its own small confirmation: the anchor
defect lost *declarations*, not *targets*.

**Index:** MEAS-93 … MEAS-96.

## 2026-08-23-architecture-33 — A stepper RECOVERS its walker; and arming a gate arms the pins it does not have

Two from the SV lane's green (`b499afa`, on master).

**(1) §3.6 (1a) — THE SUBSUMPTION OBLIGATION, and it is the pattern every tier
that defunctionalizes will owe.** Defunctionalizing a suspending language
produces a **second interpreter shape**: the resumable stepper beside the walker
already there. SV discharged the obligation rather than living with it —

> **`execSStmts` is RECOVERED as the NON-SUSPENDING CASE of `stepSStmts`, not
> superseded — proved, so the two cannot drift into a second interpreter.**

— and the old definition becomes a **theorem-backed special case**. **The
discipline is cheap only at the moment the stepper is introduced**, while the
stepper was built to generalize the walker and nothing has diverged yet.

**The contrast that prices it is in this repository**, and it is what I added:
the Python **trunk/rebuild** window kept **both sides executable**, and that
single fact is why that tier needed the **whole capability-parity apparatus** —
the three-site audit of `2026-08-23-architecture-23`, a census of what each side
can do, and a standing question of which side a finding is about.

> **Two EXECUTABLE implementations of one semantics cost a parity APPARATUS.
> One executable plus one theorem-backed SPECIAL CASE costs a THEOREM.**

Both are legitimate — the Python window was a deliberate migration with the
apparatus priced in — but **the choice is made when the second implementation
appears, and only then is the cheap option available.** A tier shipping a
stepper without the agreement theorem has silently taken the expensive road and
will not learn it until the two answers differ.

**(2) §5.4b — ARMING A GATE IS A PINNING DECISION, made retroactively.**

> **An unconditional byte-comparing gate inherits every unpinned input of the
> artifact it compares. Arming the gate arms the pins it does not have.**

A byte comparison has **no tolerance**, so it promotes every input of the
compared artifact into a **pin requirement**. Measured: all **21 SV envelopes
stamp pyslang's POINT version**, `ci.yml` installed it **unpinned**, and the
newly-unconditional `sv_round_trip` would **turn every PR red at pyslang's next
release, for a reason unrelated to anyone's change**. **Green today only because
the resolver happens to match** — *a green that holds because nobody has
released yet is evidence about the world, not about the pin.*

**This is MEAS-9's dual, which is the framing I think earns its place:** a
permanent SKIP is *a check pretending*; a gate red for reasons unrelated to the
change is *a check being ignored* — it trains a team to re-run rather than read,
and it spends the credibility of every honest red beside it. **Same defect — the
gate is not about the change — pointed in opposite directions**, and arming an
under-pinned gate moves a tree from the first to the second in one commit.

**THE COMPOUND, and it is what changes the cadence.** The half-applied family
stamp was **already flagged** in the lane's own dormancy note — *"DONE for the
census; the envelope still stamps 11.0.0"* — honest, correctly filed, entirely
dormant. Dormant **only while nothing compared those bytes unconditionally**.

> **A flagged wart plus a new gate is an armed bomb.**

So §9.7 gains a **trigger** rather than a tick: **on every gate that goes
unconditional, re-read the owning lane's dormancy records** — arming a gate
re-prices every deferral the artifact carries. Disposition recorded so the
interim is not mistaken for the fix: the **temporary pin** (`pyslang==11.0.0`,
marked as such) is dispatched to the tools lane; the **durable fix** — family
stamp plus regeneration, **validated by the same gate** — rides SV's Landing A.
*A pin is a schedule, not a design.*

**AND A CONVERGENCE WORTH TWO SENTENCES.** SV kept its new lemmas **out of the
`LeanModels` glob** because an unverified `rfl` would have turned `lake build`
red, *"and a red build means the gates never run — which would have cost the
proof evidence as well as the build."* The Wasm lane reported the same shape
from the other side (`886ede9`: its fork build, *"when red hides every gate
behind it"*). Two tiers, independently: **a red build is not one failure, it is
an OUTAGE of every gate behind it** — which makes build-red a **gate-set** event
and makes staging an unproven definition outside the glob a **gate-preserving**
move rather than timidity.

**THREE RIDERS, arriving from QoL (`582529d`, `2026-08-23-qol-43`) while this
entry was being written.**

**(a) The obligation is RELOCATED, and that is the sharpest part.** The unpinned
input was **harmless for as long as the gate sat unwired** — nobody edited it,
nothing about it changed; what changed is that something started **comparing**
it.

> **Wiring a comparison changes the blast radius of inputs NOBODY EDITED — so
> the PIN AUDIT belongs to the ARMING COMMIT, not to the gate's author.**

The gate's author is the person least able to see it: they wrote a correct
comparison, and the defect lives in a `ci.yml` line they never touched. **The
arming commit is the only commit where both facts are visible.** Checkable form
for `--gate-set`: for each unconditional comparing gate, does its compared
artifact embed a version string, and is that version pinned at **every** install
site — **both arms of any `||` fallback**, since the second arm was unpinned
here too. The `||` clause was discovered, not designed: **a fallback install
path runs only when the first one failed, which is exactly when nobody is
watching**, so a pin audit that reads the happy path audits the arm that was
already fine.

**(b) A message is a surface.** The SKIP branch politely told the reader how to
enable the gate — with the **unpinned** command, in a line twenty minutes old.

> **A hint is an INSTRUCTION, and an instruction that reproduces the defect IS
> the defect.**

Error and skip messages that tell a user what to run are **part of the gate's
surface and audited with it**. For the reader who follows it, the message *is*
the tool — §5.4's argument-parser rule pointed at the other end of the
interface.

**(c) One note left standing by name.** `docs/sv-charter.md:138`'s dated venv
measurement will quietly stop being true. **Named in §5.4b and flagged to SV,
not edited** — a dated measurement in another lane's document is named, never
corrected in passing, because correcting it silently turns a record of their
moment into a record of mine (§9.5a, and `2026-08-23-architecture-26`'s
annotation norm seen from the outside).

**Index:** MEAS-97 … MEAS-102, STMT-103, STMT-104.

## 2026-08-23-architecture-34 — Ask what the run type IS before pricing the seam; and a named blocker is a next step

Three from the Go lane's seam landing (`6a73111`, on master).

**(1) COOKBOOK 22 IS NOW CONDITIONAL — minted by CENSUS, not by analogy.**
*"Open the stack once"* presumes there is a stack. Go's census found the fork,
and it decides the seam's whole shape:

* **a DATATYPE run** (Python's `Run`) — `bind` **reduces by cases**, so there is
  **no opener and none is needed**; that tier's wall was the
  **approximation-order congruences**;

  > **ANNOTATION (`6b91a8d`; entry NOT rewritten).** This bullet says *Python*
  > where it should say *Python's TRUNK*. The census measured one of that
  > language's **two** tiers and named the language: the **monadic** tier is a
  > transformer stack and **does** have an opener — `bind_apply`, in
  > `LeanModels/Python/Monadic/Substrate.lean` with the `toRun` corollaries.
  > Corrected per-tier in cookbook §22, with the meta-law recorded there and in
  > `2026-08-23-architecture-35`.

* **a TRANSFORMER STACK** (Go's `GoM`) — nothing reduces by cases, so **the
  opener is exactly what was missing**, and it is **one lemma wide**.

> **Ask what the run type IS before pricing the seam. A datatype's cost is its
> CONGRUENCES; a stack's cost is its OPENER.**

**And the guard is the transferable half, because the number was REAL.**
`Python/Obs.lean` is 158 KB and 79 theorems — a true measurement — and the
lane's own words are the law: *"quoting Python's 79 theorems as my price would
have been the wrong read of a real number."* Not a wrong number: **a right
number about a different structure.**

> **A number from another tier measures THEIR structure. It prices yours only
> if the structures match — establish that first, or the census you skipped is
> the one that mattered.**

MEAS-1 with its failure mode named: **pricing by ANALOGY feels like pricing by
MEASUREMENT, because there is a measured number in it.** That is the same
family as §5.4a's scope inheritance, arriving through a tier boundary instead
of through a correction.

**(2) §3.4 — TWO RIDERS, and the second is the one I would keep.**

**(a) The ruling held by being DECLINED.** Go needed congruences and did not
lift Python's, because `Python.Res` carries an **`.exn` arm the Go stack does
not have** — lifting it would have been the thick-trunk mistake. Core supplied
the **order**, the lane wrote its **own** congruences. Recorded because **a
ruling whose first out-of-tier use is a lane declining to reuse something is
better evidence than one whose first use is reuse**: the ruling's content is
*where the line falls*, and only the refusing case tests the line.

**(b) `run_bind` is the covenant made mechanical.** One lemma opens the stack
and its arms *are* the layer order restated as rewriting rules — **loud
discards state, panic RETAINS it, only a value continues.** Nothing there was
decided at the seam; it is `ExceptT ρ (StateT W Halt)` read off arm by arm, in
the one place a proof needs it.

> **The covenant made mechanical: the layer order paying for itself in a form a
> proof can rewrite with.**

**This is the SECOND tier in which the speaker split bought a theorem it was not
designed for.** The split was chosen for **fidelity** — so a model-level refusal
could not be caught by modelled code — and it keeps returning **proof**
dividends: fuel monotonicity became mechanical from the state-retention order,
and now a stack-opening lemma is three arms long because each speaker has
exactly one behaviour on `bind`. **A distinction drawn for the right reason
keeps paying in currencies it was not drawn in** — the strongest argument
available for drawing them on principle rather than on convenience.

**(3) §9.7 — §G8 → §G9 AS THE WORKED INSTANCE OF THE BLOCKER-NAMING NORM.**

> **ANNOTATION (`cd14591`; entry NOT rewritten).** The clearing entry is
> **§G10**, not §G9 — the lane's own ladder table names it. Corrected in the
> charter, and the arc is now complete there: §G8 → §G10 → §G11 → §G12.

§G8 recorded three lemmas as unprovable **and named the cause exactly**:
`lookupLocal name w` is not definitionally the match on `w.locals.find?`. One
seam later each is **four lines** (`propext` alone).

> **A NAMED BLOCKER IS A NEXT STEP; AN UNNAMED ONE IS A WALL.** *"Unprovable"*
> retires a line of work; *"unprovable BECAUSE these two terms are not
> definitionally equal"* is a specification of the lemma that fixes it.

Landed beside §9.7's *an obstruction that is only encountered is not measured
either*, which is the same law stated negatively. **And the honest half is the
model for how to LEAVE a blocker**: the seam does not settle the induction, the
lane says so, and it names the difference that makes it progress — **the debt is
smaller and its next step is MECHANICAL rather than OPEN-ENDED.** *The same size
of debt, differently shaped, is progress and should be reported as such.*

**Index:** MEAS-103, MEAS-104, STMT-105, PROOF-57.

## 2026-08-23-architecture-35 — A census that names a language when it measured one of its tiers; and a gate that caught its author

A correction to the previous landing plus two from `6b91a8d`. The dated entries
`-30` and `-34` are **annotated**; the charter's and cookbook's present-tense
prose is **corrected**.

**(1) THE CORRECTION: PER-TIER, NOT PER-LANGUAGE.** Go's census reported *"Python
has no opener, because it never needed one"*. **Python has two tiers.** The
**trunk**'s `Run` is a datatype — true, no opener, and the wall was the order
congruences. The **monadic** tier is a **transformer stack** and **does** have an
opener: `bind_apply`, `LeanModels/Python/Monadic/Substrate.lean`, with the
`toRun` corollaries beside it.

> **A census that names a LANGUAGE when it measured one of its TIERS is the
> right measurement under the wrong quantifier.** Name the artifact you ran it
> over.

**This is the files-vs-sites family at TIER granularity** — the same defect as
counting identifiers where pattern positions were meant (§5.4a), one level up:
the number is real, the **unit** is wrong, and the wrong unit is the more
plausible one. Worth noting **what did not break**: the datatype-vs-stack fork
itself is unaffected, and Go's own price — one lemma — was right. **A wrong
quantifier over a right measurement damages the GENERALIZATION, not the
decision that was made from it**, which is exactly why it survives review: the
lane that made it got the right answer.

**AND THE STAMPS ARE DISCHARGED.** All four `-30` landings carried *"staged on
ticket 40057; conditional on that landing"*. It landed. The charter now says
**LANDED `6b91a8d`** at each site, and the discharge is **recorded rather than
quietly deleted** — a stamp removed silently leaves no evidence the claim was
ever conditional, which is the annotation norm applied to a stamp's retirement.

**(2) §5.4b — A GATE THAT CAUGHT ITS OWN AUTHOR ON ITS FIRST RUN.** A new census
gate produced **109 confident `DRIFT` lines**, every one the same conflation:
`WHITELIST_CLASS` names **which GAP** a row is, the model's class names **what
KIND** of refusal it made. **Two fields with the same name are not the same
field.** Seven more flagged boundary-freeze refusals for lacking a class the
same commit's documentation says they must not have — *a gate contradicting its
own specification.*

> **The tell is the UNIFORMITY, not the count. A check that suddenly convicts
> most of a corpus is far likelier to be reading the wrong column than to have
> found a systemic bug.**

**My addition is why uniformity is the signal**: a systemic bug in a mature
corpus is **ragged** — it hits the rows sharing a cause and misses the rest.
Uniform, confident and everywhere is the signature of a **misread**. The
instinct it should trigger is *"which column am I comparing?"* before *"how did
this get so bad?"* Landed beside:

> **An unexercised gate is not a gate; it is a claim.**

— the same rule as *a check that has never failed is a design, not a control*,
with the best instance available: **its first real run convicted its author, and
both defects were in the gate.** A gate whose first execution is on somebody
else's landing has been tested by nobody.

**(3) §5.2 — THE COUNTING RULE FOR THE EXPECTED-EMPTY CLASS.**

> **A zero for a class the tier CAN emit is a fact about the CORPUS. A zero for
> a class the tier's API CANNOT BUILD is a fact about the TIER.**

`environment=0` and `order-dependence=0` are **coverage**; `undefined=0` is a
**property of the model**. **Conflating them is how a coverage hole reads as a
soundness result** — *"no undefined behaviour observed"* is a sentence both
zeroes support and only one earns. The distinction is **structural** (can the
API build it?), so it is decidable **once per class** rather than argued per
report, and the census now gates the strong half from the outside on the real
corpus: 116 rows, 45 gap classes, 7 boundary-freeze refusals with no class by
design, 0 drifts.

**Index:** MEAS-105 … MEAS-108.

## 2026-08-23-architecture-36 — Never touch the scrutinee; the blocker ladder is complete; and a boundary drawn after a proof is drawn by the proof

Three from Go's closed loop induction (`cd14591`, on master).

**(1) COOKBOOK 23 — REWRITING PAST A DEPENDENT MATCH.**

> **Never touch the scrutinee — rewrite the WHOLE BIND from a proved equation
> about its head.**

`run_bind_ok (h : x w = .ok (.ok a, w')) : (x >>= f) w = f a w'`, **one lemma
per outcome of the stack** — three, because the stack has three, which is the
covenant again — placed **beside the seam** rather than in the exemplar that
needed them first, since they are reusable at every loop and every `do` block
the tier will prove about.

**The entry is written around the two wrong moves**, because both look
obvious: a **congruence over the match** still leaves a match (the Lean fact
*simp will not rewrite inside a dependent match discriminant* is the blocker
itself, not an obstacle en route), and **let-binding the interpreter's
scrutinee** edits the definition to suit the proof — §0.1's forbidden move. The
head-equation form clears it **with no congruence over the match at all**, and
the definition stays untouched.

**Two riders, both discovered rather than designed**: `dsimp only` is needed for
the **iota** step, because `simp only` will not reduce a match on a **literal
constructor**; and the head's **associativity must be read, not assumed** —
`execLoop`'s head is `evalExpr >>= fun v => asBool v >>= …`, and a `show` built
on the other shape fails **without naming the difference.** *Assume the shape
and the error teaches you nothing; read the goal.*

Cross-referenced from cookbook §10 (the destructuring route, unavailable here)
and tied to §3.4's **nested-match ceiling**: same Lean fact from the tactic
side. **The ceiling stands; this is the route around it for a tier that owns its
own lemmas.**

**(2) §9.7 — THE BLOCKER LADDER IS COMPLETE, and it converts the norm from
anecdote to test.** §G8 *a lemma SET* → §G10 *cleared, 10 rows* → §G11 *ONE
congruence* → §G12 *cleared, 3 rows on `propext` alone*, ending in a proved
loop. Read the cost column downward and the shape is the finding:

> **A well-named blocker NARROWS each time it is re-stated. If the next
> statement is no smaller than the last, the naming was wrong — the lane has
> re-described the wall rather than located it.**

That is the norm's **test**, checkable without waiting for the proof: not *"did
we progress?"* but *"is the blocker's next form narrower than its last?"* A
blocker arriving repeatedly at the same width is a symptom being renamed. **And
the arc argues for the norm itself**: nothing in it was a breakthrough — each
rung was ordinary work made possible by the previous rung stating exactly what
was missing.

**Citation corrected**: `2026-08-23-architecture-34` cited the clearing entry as
**§G9**; it is **§G10**, per the lane's own table. Charter fixed, dated entry
annotated.

**(3) §5.4a — THE STANDARD FOR A PARTIAL THEOREM CLAIM.**

> **The LOOP is correct, PROVED. The FUNCTION is correct, CHECKED** — 35 inputs,
> two independent standards.

Neither half hedged, neither inflated. **The mechanism is what makes it
repeatable**, and it is the law:

> **Write the proved/checked boundary BEFORE you can close either half. A
> boundary drawn after a proof lands is drawn BY the proof.**

§G6 wrote the distinction while **both** halves were open, so closing one **did
not move the other half's words.** A boundary written afterwards is written by
someone who already knows which side won, and **it drifts in one direction
only** — the proved side annexes what sits next to it, because at that moment
the annexation feels like precision.

Landed as §0.1 II(a)'s receipts rule at the granularity of a **claim** rather
than a tactic: *"checked on 35 inputs against two independent standards"* is a
strictly better sentence than either *"correct"* or an apologetic silence. **A
checked half is a result; it is only a weakness when it is described in the
vocabulary of the proved half.**

**Index:** MEAS-109, STMT-106, PROOF-58, PROOF-59.

## 2026-08-23-architecture-37 — The first vendored function-level theorem outside Python; and a proof demotes only the rows about the relation it proved

Three from Go's completed exemplar (`4bda5af`, on master).

**(1) §5.6 — THE MILESTONE, landed where the section that asked for it lives.**

> **`bitLen_correct`: `callFunction … "bitLen" [v]` returns `bitLenSpec v` for
> every `v < 2⁶⁴`** — the family's **first full function-level theorem about a
> real vendored program** outside Python. 22 theorems, `propext` /
> `Quot.sound` / `Classical.choice` at worst, no `sorry`, no `native_decide`.

> **ANNOTATION (Thomas's completion directive, 2026-08-23; entry NOT
> rewritten).** This is a **WAYPOINT**. It describes an **exemplar**, never the
> **tier** — Go's completion is measured by its stdlib reach instrument, and
> that number is elsewhere and much smaller. §9.0 now carries the framing, and
> §5.6 says it at the milestone itself. Nothing in the entry was wrong; what
> needed fixing was **what a reader would infer next**.

Read against §5.6's own rule it is the whole shape: a **suite** set the scope,
**one exemplar** drove the proof library, and the exemplar was **chosen for its
theorem**. **The property that makes it a milestone rather than a demonstration
is that the subject is vendored** — the tier did not write it and cannot edit
it, so nothing in the result can be arranged by choosing a friendlier program
afterwards.

**AND THE COMPOSITION FORCED A GENERALIZATION — the benign direction of the
quantifier family.** `body_step`, `cond_eval` and `loop_computes` were stated
with `[]` as the program table because the loop calls nothing; `callFunction`
passes the real one, so they now range over an arbitrary `P : FuncTable`. *The
loop genuinely does not care, and now says so.*

> **GENERALIZATION BY COMPOSITION: when a consumer forces a lemma's quantifier
> wider and the proof does not change, the narrow statement was an accident of
> its first use.**

Named explicitly because **the quantifier family's other members are
failures** — a count under the wrong unit, a census naming a language where it
measured a tier (`2026-08-23-architecture-35`). This is the same mechanism with
the sign reversed, and a lane should read it as a **result, not churn**: a lemma
widened by its consumer and re-proved with no new work has been **measured** to
be more general, which is better evidence than being written general by an
author who guessed.

**(2) §5.4a — THE DEMOTION STANDARD, beside the proved/checked boundary.** With
`bitLen_correct` proved, the 35 **SPEC** rows are demoted to corroboration —
instances of `bitLen_eq_spec`. The 35 **ORACLE** rows are **not**:

> **`bitLen_correct` proves the model computes `bitLenSpec`; it cannot prove
> `gc` does.**

> **A proof demotes the rows about the RELATION IT PROVED, and no others.**

**My addition is why this is a trap and not a bookkeeping note.** A landed
theorem creates pressure to retire the tests it "covers", and the covering feels
**total** — it quantifies over all `v < 2⁶⁴` where the rows are 35 points. But
**strength along one relation is not coverage of another**, and the two row sets
are **indistinguishable in the table**: same inputs, same expected values, and
**only their ADJUDICATOR differs** — precisely what a row's data does not show.
So the decision is made by asking which relation each row adjudicates, never by
comparing values. That makes it *the adjudicator is the ORACLE, never the TABLE*
in its **second direction**: an adjudicator's retirement re-anchors its rows; a
**theorem's arrival** may demote only the rows whose adjudicator it replaces.

**(3) §9 — WHY CORPUS-DRIVEN SELECTION WORKS, recorded because it reads as
luck.** `bigmod.bitLen` hand-rolls its loop **to avoid the lookup table**
`bits.Len` uses — its own comment says so — and lookup tables need exactly the
array types and indexing the tier lacks. **The census picked the one function in
the neighbourhood that does not need the construct the tier lacks, without
knowing that was why.**

> **Corpus-driven selection finds the frontier's traversable point BY
> CONSTRUCTION: a ranking over what the tier can EXECUTE is already filtering
> for what the tier can PROVE about.**

The constraint was satisfied **silently** — nobody identified it and searched
for a program obeying it. That is the argument for ranking by **executability**
rather than by interest: **a selection rule defined over the tier's own
capability cannot pick an unreachable subject**, and a human choosing *"the
interesting function"* routinely does. **And the honest limit is in the same
census**, which is what makes it a strategy: the next inch (`math/bits`, 49
exported, 26 plain-integer) is blocked on **exactly the eight table-driven
ones**. Corpus selection finds the traversable point **and names the wall — in
constructs rather than in effort.**

**Index:** MEAS-110 … MEAS-112.

## 2026-08-23-architecture-38 — A mis-bucketed refusal is mis-scheduled; a parser's kinds are the parser's; and the census that refutes a published plan

Three from Go's census landing (`69ea58a`, on master).

**(1) §5.2 — THE CLASSES ARE A WORK ASSIGNMENT, NOT A LABEL.** `int(x)` parses
as a **`CallExpr` on an `Ident`**, indistinguishable at the AST from calling an
undefined function, so the walker refused **every type conversion** as
`environment`: **51 255 of the stdlib's plain-identifier calls — 26.3%** — all
in the wrong bucket. Verified by **running the walker before and after**, not by
reading the patch.

> **A mis-bucketed refusal is not mislabelled — it is MIS-SCHEDULED. The class
> determines WHO OWES THE WORK.**

`environment` retires by **widening the modelled slice**, `unsupported` by
**climbing a rung**: different work, different owners, different schedules. So a
mis-bucketed row **queues the wrong lane**, and the downstream damage was
exactly that — the tier's ranked worklist was a worklist of *environment*
refusals, and **a quarter of it was never an environment problem at all.** This
is MEAS-18 (*never pool the four causes*) with the cost finally measured: the
pooling defect is not a reporting blemish, it is misdirected labour.

**And the fix shape is the reusable part — a PAIRED guard**, one conversion and
one genuinely-undefined function, so a regression **in either direction** shows.
My addition, because the reason generalizes past this incident:

> **When a fix moves a boundary, guard BOTH SIDES of it. A one-sided guard
> ratifies today's error in the other direction.**

Re-classification defects move both ways by construction — the same edit that
stops over-claiming `environment` can start under-claiming it — and a
single-sided guard pins only the half that happened to be wrong the day it was
written.

**(2) §5.4a — A FOURTH WRONG UNIT, and this one was handed to the lane by the
parser.** `[N]T` and `[]T` are **one `go/ast` kind**, separated only by a `Len`
field, so a census over AST kinds reported **`ArrayType` 48.0%** — two semantic
objects summed. Split: **slices 46 188 (85.4%), fixed arrays 7 923 (14.6%)**,
slices outnumbering fixed **6 : 1**.

> **The files-vs-sites family INSIDE THE AST: an upstream representation's unit
> is not your unit.**

**The direction is what earns the paragraph.** The sizing question was whether
the tier could **skip slice semantics** because the tables are fixed-size, and
the working assumption ran the **opposite way** from the truth — a conflated
figure could never have corrected it, because **both objects sat inside the one
number that looked like an answer.** General form, cheap to apply: **a parser's
kinds are a convenience of the parser**; before pricing by them, ask **which
distinctions the upstream representation declined to make**. Those are exactly
the ones your census cannot see, and they are invisible precisely because the
tool that produced them had no reason to care.

**(3) §9.0a — CENSUS-FIRST'S STRONGEST FORM.** The rung was scoped as *"the
table functions need array types and indexing"*. They do not: all four tables
are **untyped STRING constants**, `Len8` is `int(len8tab[x])`, and the
acceptance case is **string indexing plus a type conversion**.

> **A census is worth running even when the plan is already written. Especially
> then: the plan is the hypothesis, and the census is the only thing that can
> refute it before it is paid for.**

**Two things make it the strongest instance.** It is the **second** time the
corpus corrected a rung's definition before a line was written — and the **first
time it corrected an entry this lane had already published.** A published entry
is the hardest premise to re-examine: it has survived review and been cited. The
census had no way of knowing that, and refuted it anyway.

**The rule that falls out** — and it is a change to how the norm is read:
*census-first* is **not a phase that ends when planning ends**. **Re-run the
census at the moment the plan becomes expensive**, the inch before the *work*
and not only the inch before the *design*, because that is the last point at
which a refutation is still free.

**Index:** MEAS-113, MEAS-114, STMT-107, STMT-108.

## 2026-08-23-architecture-39 — Take the acceptance case that can fail; a performance symptom is a modelling question; and a proved spec adjudicates its siblings

Three from Go's rung 4 (`a991f22`, on master).

**(1) §5.6 — THE DISCRIMINATING ACCEPTANCE CASE, and take it NOW.** `Len8`
would have passed under **any** string representation; `rev8tab` holds **128
bytes ≥ `0x80`** of its 256, and a Lean `Char` at code point 200 is **two bytes
in UTF-8** — so that table, and only that table, could tell a wrong value model
from a right one. It did: `stringV (s : String)` was refuted **by the spec's own
words** (a Go string value is a sequence of bytes; `s[i]` yields a byte) and
became `stringV (bytes : List UInt8)`. Blast radius **7 sites, checked before
the change**.

> **Choose the acceptance case that can FAIL under the wrong model, and take it
> NOW rather than defer it. The alternative is rebuilding the model after the
> rung has been built on it.**

**The trap I named is that the non-discriminating case is the attractive one**:
`Len8` is simpler, lands sooner, and passes. A rung accepted on it would have
been **green on a wrong value model**, with every later inch adding weight to
the thing that had to be replaced. **An acceptance case that cannot fail is a
demonstration; one that can is a measurement** — §5.3's distinction moved from
the row to the choice of subject.

**(2) §5.4a — A PERFORMANCE SYMPTOM IS A MODELLING QUESTION**, landed as the
**diagnosis half** of §8's *raising heartbeats trades a wrong answer for a slow
one*. That line says what not to do with a timeout; this says where to look, and
**three times in one rung the faithful shape was also the cheap one**: run-time
panics carry a `runtime.Error` and not a string (`runtimeErrorV`), and a
conversion **is a different construct that Go's grammar merely spells like a
call** (`Expr.convert`, emitted by the frontend — 0 timeouts without the
in-`evalExpr` branch, 4 with it, and moving it to the `none` path recovered
nothing). **No heartbeat bump was needed.**

> **When the faithful shape keeps turning out to be the cheap one, the cost was
> reporting a CONFLATION, not a budget.**

**My addition is the mechanism, because it makes the law usable rather than
anecdotal**: a model that conflates two things must **decide between them at run
time**, on every visit, and the kernel pays for that decision every reduction.
**Un-conflating moves the decision to the frontend, where it happens once.** So
a cost spike is evidence about **where a distinction lives**. And it is the
parser-unit law from `-38` seen from the other side: `go/ast` merges `[N]T` with
`[]T` **and** a conversion with a call — **the census reads those merges as a
measurement hazard; the interpreter feels them as a cost.** Same fact, and that
lane's charter already rules the second: anything type-dependent is the
frontend's.

*(Routing note: the coordinator offered "cookbook or §5.4a". It went to §5.4a
alone — the cookbook is one page per CLAIM SHAPE, and this is a diagnosis rule,
not a way to word a theorem.)*

**(3) §5.6 — PROVED-SPEC-AS-ORACLE, a THIRD adjudicator kind.** `Len8` was
checked **exhaustively over all 256 inputs** against `bitLenSpec`, **§G13's
proved spec**, and `Reverse8` against **what `gc` printed**.

> **The theorem proved for the crypto lane's hand-rolled loop now predicts the
> standard library's table-driven function, and they agree on every input.**

> **Once a spec is PROVED for one implementation, it serves as an INDEPENDENT
> STANDARD for sibling implementations.**

So a tier has **three** adjudicator kinds — compiled oracle, hand-derivation,
spec-theorem — and the demotion rule (`-37`) applies to the third **per
relation, exactly as before**: a spec-theorem row adjudicates *"this
implementation computes the spec"*, **not** *"the compiled artifact does"*.
Which is why `Reverse8` still needed `gc`, and why `Len8`'s oracle rows are not
retired by its spec rows.

**What makes it new evidence rather than a second proof**: it is **one proved
relation used twice**, and its value comes from the implementations being
**structurally unrelated** — a hand-rolled loop and a table lookup, no shared
code, written years apart to do the same arithmetic.

**AND THE SMALL GUARD SHAPE:** three named high-byte rows beside the exhaustive
sweep, **so a representation that lost the high bit fails BY NAME, not only in
bulk.** An exhaustive sweep is the stronger check and the **worse diagnostic** —
it reports *"some input disagrees"* and leaves the reader to bisect. A handful
of rows chosen **at the boundary the model is most likely to get wrong** costs
nothing and turns a bulk failure into a sentence. Non-vacuity run on both, which
is what keeps the named rows from being decoration.

**Index:** MEAS-115 … MEAS-117, STMT-109.

## 2026-08-23-architecture-40 — The census partially orders the rungs; the conjunctive law is now family law

Three from Go's re-rank (`4618380`, on master). **Headline, stamped:** the
walker steps **1 289 of 3 084 rung-1-reachable stdlib files — 41.8%**, up from
**633**. Rungs 3 and 4 **doubled** it, and the number moved **by construction
rather than by drift**, which is why it is quoted with the commit that produced
it (MEAS-10).

**(1) §9.0b — NEW SUBSECTION: a reach census does not just RANK, it PARTIALLY
ORDERS.**

> **ANNOTATION (`5b3602f`; entry NOT rewritten).** The `+0` law below was
> **RETRACTED by the next measurement**: `RangeStmt` measures `+0` alone and is
> worth `+9` inside the family it shipped in. **A construct's delta is a
> function of the current vocabulary, not a property of the construct.** The
> headline figures here are withdrawn too — *41.8% → 74.8%* counted
> `SelectorExpr` as steppable, which the walker refuses; the reproducible
> figure is **512 → 604 of 3 803**. Carried forward in
> `2026-08-23-architecture-42`; the conjunctive law is untouched and was in
> fact confirmed by the same evidence.


> **`+0` in a reach census means NO REACHABLE FILE IS BLOCKED ONLY BY THAT
> CONSTRUCT. It cannot be a next rung AT ANY PRICE; it is strictly DOWNSTREAM
> of whatever co-occurs with it.**

`MapType +0` and interfaces `+0`, both behind slices. **My addition is the
misreading it prevents**: a lane reading `+0` as *"cheap, do it when
convenient"* will build a rung that unblocks nothing — **and will not find out
until after paying, because the construct itself will work perfectly.** So the
two readings of a small number are opposite: **`+56` is a small rung; `+0` is
not a rung at all.** A rank says what is worth most; a partial order says what
is even **available**, and this census answers both with one number.

**(2) §9.0b — THE CONJUNCTIVE LAW, PROMOTED to family law on its third
independent reproduction.** It was nowhere in the charter or the law index —
checked before promoting — so it had been a lane observation through all three.

> **Some constructs have value only as a FAMILY. Ship any one and almost
> nothing moves; ship the family and the reach steps.**

`ArrayType` **+528**, `SliceExpr` **+27**, `RangeStmt` **+29** — parts **584**,
whole **+1 019**, **1.7×**, reach **41.8% → 74.8%**. §G1's bundles and §G4's
switch family were the first two; **this is the first where the parts are
individually near-worthless in single digits**, which makes the failure mode
concrete: **a lane pricing these three separately would have rejected all
three.** Three reproductions is this document's own evidence bar (§9.3), so:
**price a candidate rung against the family it belongs to and report both
numbers** — a per-construct table with no joint column **systematically
under-prices exactly the rungs worth taking.**

**And the counterpart that stops the law licensing bundles**: the family is what
the **census** says co-occurs, not what a lane finds tidy. **Fixed arrays are
14.6% of `ArrayType` and are NOT in it** — declare only what executes (§5.2's
deferral hygiene).

**(3) §5.4a — VALUE OR REFERENCE, a diagnostic for two adjacent-looking
blockers.** The `strings` package did not start paying after the value model was
fixed, because `strings.Index(…)` is a **selector call** — 52.4% of call sites,
ruled `go/types` work.

> **§G15 changed what a string IS; it did not change what `pkg.F` MEANS.**

They fail on the same line of source, and **a lane that has just fixed the first
will reach for it again when the second bites.** So: **decide whether a blocker
lives in the VALUE or in the REFERENCE before pricing it** — the value model was
this lane's, the selector resolution is the extractor's. Landed as §5.2's
mis-scheduling law **in a second dimension**: the refusal class says which lane
owes a *construct*; this says which lane owes a *blocker*, and both go wrong the
same way when a plausible adjacency substitutes for a measurement.

**Index:** MEAS-118 … MEAS-120.

## 2026-08-23-architecture-41 — The discriminator lives in the call; and the row a wrong model cannot state

Two from Go's slice census (`e2af807`, on master), both refining
`2026-08-23-architecture-39`'s acceptance-case rider one rung after it landed.

**(1) §5.6 — THE UNIT IS `(FUNCTION, ARGUMENT)`.** The rung went looking for a
discriminating function and **could not find one** — which is the finding, not a
setback. **60 candidates** used a slice expression plus a write through an
index; tightened to require a **MIDDLE slice `a[i:j]`** — *the only place `cap`
and `len` come apart, since a tail slice has `cap == len`* — it collapsed to
**8**, every one needing interfaces, `clear`, `append`, or
range-over-struct-slice.

> **A discriminating acceptance case does not have to be a discriminating
> FUNCTION. The case that can fail under a wrong model is `(FUNCTION,
> ARGUMENT)` — not the function alone.**

`runtime.itoa` (57 nodes, no external calls) **called on a middle slice**
discriminates both, measured against `gc`. **The tightening is what proves the
unit**: a tail slice cannot discriminate `cap` from `len` **at all**, so the
argument's *shape* is part of the discriminator — a search over functions was
searching the wrong space and returned the honest answer for that space, none.

**And the pet-program line, which is the part I was careful about**, since §5.6
exists partly to refuse commissioned subjects: the subject here is still
vendored and unedited, and what the lane chose is **the call**. *A chosen call
site is not a commissioned program — it is how a caller would use the function.*
Stated as the boundary: **choosing an ARGUMENT is selection; writing a SUBJECT
is commissioning.** The first is what a suite does every time it picks an input.

**(2) §5.6 — THE ACCEPTANCE-ROW HIERARCHY, and the top tier is qualitatively
different.** Against a naive list-copy slice model the four rows sort: the
return value **PASSES**, the two aliasing rows **FAIL**, and `out[:cap(out)]`
reaching past the value's own length **CANNOT BE STATED**.

> **Rows the wrong model PASSES < rows it FAILS < rows it CANNOT STATE.**

**Two reasons the top tier is stronger, which I separated because they are
independent.** It fails at **design time rather than run time** — you find it
while *writing the row*, before anything is built on the model. And it **cannot
be argued away as a bug**: inexpressibility is a property of the
**representation**, not of the code, so no patch answers it. *A value reaching
beyond its own length into a longer array has no representation in a copy*
settled the value model **up front** — backing array + offset + len + cap.

**And the procedure runs the opposite way from how the hierarchy reads**: you do
not know the right model and then find the row; you **try to write the row under
the candidate model and fail**, and the failure is the finding — §9.7's
blocker-naming norm in a new place. **An acceptance row you cannot write is a
specification of what the model is missing.**

**Index:** MEAS-121, MEAS-122.

## 2026-08-23-architecture-42 — My own +0 law, retracted by measurement; and a missing lemma is a missing import

Five landings, and the first is a correction to this lane's `-40`.

**(1) §9.0b — THE `+0` LAW IS RETRACTED, IN PLACE.** I promoted it to family law
yesterday; `5b3602f` refuted it the next inch. **`RangeStmt` measures `+0` alone
and is worth `+9` inside the family it shipped in.**

> **A construct's delta is a function of the CURRENT VOCABULARY, not a property
> of the construct.**

Maps (`+8/+14`) and interfaces (`+4/+7`) are **not disqualified — only still
small**. The section keeps the retracted text and says what killed it, because
a law deleted silently teaches nobody.

**WHY IT WAS WRONG IS WORTH MORE THAN THE LAW WAS, and it is my error to own:
I generalized a DELTA into a PROPERTY.** A `+0` is defined relative to a
baseline, and the whole content of a delta is the state it was taken against.

> **When a law is minted from a DELTA, the law inherits the delta's baseline.
> State the baseline in the law, or the law is a measurement pretending to be a
> principle.**

That is MEAS-10 committed **at the level of a law** rather than a number — easy
to do, because a construct feels like a fixed thing while a walker feels like a
moving one. **What survives**: the census does induce a partial order, but **a
single `+0` cannot establish it**, since the same construct is `+0` alone and
positive in company. The retracted law was the conjunctive law's **shadow** —
same fact (deltas are not additive), one true reading and one false one.

**AND THE FIGURES I STAMPED ARE WITHDRAWN.** *41.8% → 74.8%* counted
`SelectorExpr` as steppable, which §G8 had ruled `go/types` work. Reproducible:
**512 → 604 of 3 803**. The sharper half is *why the old number could not be
corrected*:

> **A number produced by a one-off script is a number that can only be
> WITHDRAWN, never corrected.**

That reach table left **no instrument** and its **vocabulary was unrecorded**.
MEAS-2/MEAS-3 exist for exactly this — a named instrument at a fixed path with
`--compare` is what makes a wrong number **fixable** rather than **disposable**.
It is now `construct_census.go --reach`, keeping the vocabulary as data.

**(2) §9.0a — EVERY SYMPTOM OF A MISSING LEMMA IS ALSO A SYMPTOM OF A MISSING
IMPORT** (SV's 8-second red, *"the failure was worth more than a green"*).
§L87's recorded obstacle was **wrong**: the four do-stepping lemmas were in
`Obs.lean` the whole time — **same namespace, one import away, out of scope**,
because the wip file imported `SelfCheck`, which does not import `Obs`.

> **Before recording an obstacle as "X does not exist", grep the namespace
> across the TREE, not the imports in scope.**

**The two failures are indistinguishable at the point of use**, and the
diagnosis a lane reaches for is the expensive one. **Second time in this tier
that a lane "needed" what it already had, and both were found by BUILDING** —
§9.0a's opening instance was the other. I recorded the direction too: the
failure is **flattering to the plan** — *"the lemma does not exist"* converts a
five-minute import into a scheduled inch, and the build agrees with it loudly,
every time.

**Rider landed with it:** the same tree-wide namespace grep, run **forward**, is
the **pre-flight name-collision check** for every name a landing declares — and
§9.0a's opening instance had *"`Res.le` … identical, in the same namespace, a
hard name clash waiting."* **One grep, two defects, opposite directions.**

**(3) §5.4b — THE PINNED COUNT'S CLEANEST LIVE DEMONSTRATION** (Wasm,
`f657041`; O1 proved, four pinned predictions, four matches).

> **The build is red and the thing that matters went green; only the pinned
> count separates them.**

Without the pin there are exactly two readings — *"red, so nothing is known"* and
*"the failures are the expected ones"* — and **no artifact distinguishes them**.
With it, the red is **partitioned**. That is pinning demonstrated **positively**,
where §5.4b previously had only the near-miss.

**(4) §9.0b — SHARED PREREQUISITES FIRST.** The census-ordered path takes
`rt_sub_trans` + `rt_sub_app` **before O3**, because **O2 and O4 need the same
pair**.

> **Order the work by what is SHARED, not by what is NEXT.**

Landed as **the conjunctive law with the arrow reversed**: there, constructs
worth little apart and much together; here, **one lemma worth little to its own
obligation and much to the three behind it.** Both are per-item pricing
failures with the same fix.

**(5) §7.2 — STALENESS, SPLIT BY PHASE** (Ada). 53 commits behind = **104
minutes of QUEUE** plus **4 commits during the 78-minute build**.

> **The staleness came from the QUEUE, not the BUILD.**

**This relocates the fix**: *"builds are too slow"* prescribes the expensive
technical answer, while the measurement prescribes a **scheduling** one. And the
reason the mis-attribution is the default: **a wait is invisible in the
artifact** — the build log shows 78 minutes and says nothing about the 104
before it. **Attribute staleness to a phase before prescribing a fix.**

**AND ADA'S CLOSURE FACT, recorded in §3.1 as an ASSET**: `LeanModels/Ada/`
imports **zero** `Core` modules — re-verified here by grep. A tier with an empty
Core closure is the cleanest subject for a **transfer argument**, since anything
proved about it is proved with the substrate out of scope. **A zero here is a
fact about the tier** (§5.2's counting rule), not a coverage gap.

**(6) §8 — THE POLARITY ENTRY GAINS ITS PAIR** (Lean tier, `29f868e`; censused
by READING before a tenure was spent). `TrProj.wf` needs the projected field
typed unconditionally; `ProjSound` typed it **only inside the Prop case**, so
*"when the structure's sort is not maybe-Prop, the definition said nothing
whatever about `v`"* — `wf` is **unprovable** against it. Fix: hoist the typing
out of the implication, Prop-squash on **levels alone** — strictly stronger,
identical soundness content, transports unchanged.

> **A definition whose guarantee lives inside an implication guarantees nothing
> when the antecedent fails. Check what the definition says when its INTERESTING
> case does NOT apply.**

**The two defects are one shape seen twice**, and the property that earns them
the same home: **neither was found by the compiler** — one by a proof, one by a
census, both definitions elaborating perfectly throughout. **A definition cannot
be type-checked into meaning what you intended.**

**Rider — the honest signature.** Upstream's redundant hypothesis was **omitted
rather than accepted-and-ignored** (*"`ProjSound` already carries it"*): an
unused parameter is a **false advertisement of what a definition depends on**,
and it charges every consumer a premise for nothing. **Take what you use; if a
hypothesis is redundant, say where its content already lives.**

**Index:** MEAS-118 (retracted, kept), MEAS-118a, MEAS-118b, MEAS-123 …
MEAS-126, STMT-110, STMT-111.

## 2026-08-23-architecture-43 — Wrong by answering; and a predicted cost inherits its construct's unit error

Two from the pyc successor's 3c-i-c census (branch `pyc-3cib2` at `0014d6d`;
**re-gate queued**, so both are landed conditional on that landing and say so at
the site).

**(1) §5.1 — THE INVERSE OF THE SILENT-WRONG-ANSWER FAMILY.** `e =
enumerate(d); d[2]='b'; list(e)` **raises `RuntimeError`** in CPython where a
snapshot model prints a value. It is not printing the *wrong* value:

> **A snapshot is WRONG BY ANSWERING, not by answering wrongly.**

**It inverts the diagnostic, which is why it needed its own paragraph rather
than a row.** The usual defect is *model and oracle disagree about a value*;
here they **do not disagree about a value at all — they disagree about whether
there IS one.** A comparator keyed on *"same printed value"* has nothing to
compare: the model succeeds, the language raises. **The row is catchable only
because both harnesses compare the exception CLASS** (MEAS-52) — a rule that
reads like hygiene until a construct arrives whose entire specified behaviour
*is* the raise.

**And the design consequence is why this is recorded rather than fixed once**: a
snapshot is not *approximately right* about such a construct, it is the **wrong
shape** — the mutation guard is a **feature of the iterator**, so a model that
cannot express *"observing this is an error"* has no correct value to choose.
Landed as §5.6's *rows the wrong model CANNOT STATE*, arriving from the verdict
side: **check a candidate model where the language's answer is a REFUSAL, not
only where it is a value.**

**(2) §5.4a — A FIFTH WRONG UNIT, and the first inside a PRICE.** `for k in d`
and `for i, k in enumerate(d)` **look like one construct and are two**: the
predicted `Kont`-record maintenance charge **never fires**, because `enumerate`
is a **`GenFrame`, not a loop cursor**. *"The paying case" was free.*

> **A predicted maintenance COST inherits the unit error of the construct it was
> predicted for.**

**What makes this member worse than the others, and it is my addition**: the
rest of the family mis-counts things that **exist**, and a wrong count can be
re-run against the tree the moment anyone doubts it. **A wrong cost prediction
is checkable only by doing the work** — or by censusing the construct it names,
which is the cheap half and the one that gets skipped. A prediction has the form
*"each X costs Y"* and is wrong **whenever X is the wrong unit, however right Y
is for real X's**, so the check is not *"is the estimate reasonable?"* but
**"is the thing being estimated one construct or several?"**

**Recorded with its provenance, because the direction matters: the refuted
prediction was the COORDINATOR'S.** §9's *a census that could have overturned
the plan* is evidence when it does not overturn and a **result** when it does.
**The failure mode avoided here is not a wrong estimate — it is an estimate
nobody could have checked**, which is what an unpublished one always is.

**RULING (c), landed beside it: an OPENING IS WITNESSED, NOT DECIDED.** The
never-stepped `enumerate` object's openings carry **the oracle's expectation**
and do not become **a second decision site**. Two decision sites about one
behaviour is the shape §5.2's *one execution, two projections* and §5.3's *the
oracle writes its own column* both exist to prevent — **nothing fails when they
diverge.** Admitting a construct the tier has not built is legitimate; **claiming
to know what it does is not**, and the difference is whether the expectation came
from the oracle or from the lane.

**Index:** MEAS-127, MEAS-128, STMT-112.

## 2026-08-23-architecture-44 — The quirk that blocks direct reuse can fund the crossing

One from the Wasm lane (**queued**; landed conditional on that landing and
stamped at the site), correcting §8 item 11 — text this lane wrote.

**THE CORRECTION.** Item 11 said the Mathlib `forall₂_*` route *"cannot apply
to this model at all."* **Mathlib ships the crossing itself —
`List.forall₂_iff_zip`** — and its side condition is a **length equality**,
which is precisely what `Resulttype_sub`'s constructor already carries **because
its zip-based `Forall₂` is length-blind.**

> **The length-blindness that made the API inapplicable is the same fact that
> supplies the bridge's premise.**

> **A generated model's relation being NONSTANDARD does not ORPHAN it from the
> library. Look for the IFF that CROSSES — its premise is often already carried
> by the generator's extra fields, so the same quirk that blocks direct reuse
> can FUND the crossing.**

The API does not apply **pointwise**; it applies **through a one-time bridge**,
and paying it once **restores the whole library downstream**.

**WHAT CHANGED AND WHAT DID NOT, because this is my text being corrected.** The
measurement was right — the constants differ, the pointwise route is red. **What
was wrong was the quantifier on the conclusion**: *"does not apply"* where the
evidence supported *"does not apply directly."* **A negative about a library is
a claim about a SEARCH**, so §9.7's rule for negatives governs it exactly — *an
obstruction that is only encountered is not measured* — and the nearest
alternative formulation was one search away.

**And the practical order it gives a lane, which is the part worth carrying:**
when a generated relation blocks a library, **do not price a hand-rolled
replacement first — price the BRIDGE**, one `iff` whose premise you may already
be holding. **A bridge is bought once; a replacement is maintained forever.**

**AND THE TELL NOW READS BOTH WAYS.** *A generated model's extra premises tell
you what its relation does NOT carry* — item 11's existing law — **and they are
the currency for crossing to the library**, because the bridge's side condition
is drawn from the same list. **What the relation lacks, and what you already
hold**, are the same sentence read in two directions.

**§5.4a — A PIN MAINTAINED IN THE LANDING THAT GREW THE ARTIFACT.** The port's
pin moved **5 → 9 declarations** as the port grew. Recorded because **routine is
the point**: a coverage pin is a **claim with a shelf life**, true when written
and quietly under-claiming from the next inch onward. **A pin updated later is a
re-measurement; a pin updated with the work is bookkeeping** — and only the
second is free.

*(Note: I could not find a rule under the literal name "the stale-pin rule" in
the charter or the wasm ledger, so this landed in §5.4a's pin material beside
`RE-PINNING IS RECOVERY, NOT DERIVATION` rather than as a citation to a rule I
could not locate. If it lives somewhere I did not search, this bullet should be
merged into it rather than standing alone.)*

> **ANNOTATION (coordinator confirmation; entry NOT rewritten).** Resolved, and
> the open question is closed in the direction that matters: **the rule has no
> formal name and no prior home** — it was a **coordination instruction to one
> lane**, carried in dispatches only. **Nothing to merge; the §5.4a bullet is
> its durable home**, and §5.4a now says so, because a rule living only in the
> message that carried it is §7.1a's purge hazard in miniature — every lane that
> never received the message never had the rule.

> **ANNOTATION (same confirmation) — THE ROUTING NOTE BELOW IS RATIFIED.** The
> coordinator confirmed the deviation was right and recorded **the dispatch as
> the error**: there is **no standing exception**, and `2026-08-23-architecture-33`'s
> norm governs. Landed into §9.5a as a precedent, because the case that tests a
> norm is the one where an **instruction** pushes against it — every other
> temptation to edit across lane lines is mere convenience.

**ROUTING NOTE — wasm-4 IS NAMED, NOT EDITED.** The dispatch said to annotate
`2026-08-23-wasm-4`. That entry is **another lane's dated record**, and this
lane's own rule (`2026-08-23-architecture-33`, §9.5a) is that such a record is
**named, never corrected in passing** — annotating it myself would turn a record
of their moment into a record of mine. The half-rehabilitation is therefore
recorded here and in §8, and the annotation is **filed to the Wasm lane as
INBOUND**, in its own immediate commit (§9.5a's tightening).

**Index:** MEAS-129, STMT-113.

## 2026-08-23-architecture-45 — A list is maintained by the attention that wrote the defect; and a new reader under-reads

Four dispatched from QoL's `95849db` (on master), plus one corollary from the
same commit that guards a rule this lane landed two days ago.

**(1) §5.4b + §7's tools table — THE SPIN WAS THE SHAPE, and the gate that
catches it works by DISCOVERY.** Reproduced first: `${2:-}` accepts a missing
value, `shift 2` fails with one argument left, and the loop re-enters on the
same argument — **28 value-taking flags across ELEVEN tools**, every one of
which spins if written last. One guard, `tools/argv.sh`, sourced by all (the
one-source rule, §5.4a). The `ci.sh` `argv-guards` step probes **every flag
found by READING the tools**:

> **A list would be maintained by the same attention that wrote the unguarded
> arm.**

**The mechanism is why this is a law and not a preference**: the lane that
forgets to guard a new flag is the lane that forgets to add it to the
checklist, and **the two omissions are the same omission** — so a
hand-maintained scope **cannot see it, by construction**. MEAS-19's *generated
and checked, never hand-maintained* aimed at a **gate's scope**, which sharpens
§5.4b's practical form: **enumerate the pointers by discovery, or the pointer
list is a second place to forget.**

**And the guard REFUSES rather than defaulting**, on the lane's own reasoning
that the near-miss is worse than the spin: a run that merely lost its `--gates`
value **completed and reported GREEN on the default floor**, with nothing in the
log. **A spin costs an hour; a silent floor costs the verdict.**

**(2) §7.2 — A TENURE NAMES BOTH HALVES AT OPEN**: *gates* and *gates asked by
the lane*, composed by `gates_planned` calling **the same `gates_compose` the
phase calls**, against a `DEFAULT_FLOOR` that used to be a literal inside the
phase.

> **An announcement that can drift from the phase lies in the reassuring
> direction.**

**Two properties, and only the second is unusual.** Printing the plan is
ordinary; **printing the two halves separately** is what makes a dropped
argument visible — *asked* and *will run* differ exactly when something ate the
request. And composing it with the phase's own function is the structural half:
a display-only re-implementation is **a second decision site**, and when the two
disagree **it is the announcement the reader believes**, because it arrives
first and looks like a summary. Generalized: **an announcement is generated by
the code it announces, or it is prose about a plan** — and the `DEFAULT_FLOOR`
extraction is the whole fix, since **a literal inside a phase cannot be
announced without being copied.**

**(3) §5.4b — THE READER LAW, owned TWICE in one landing by the lane that had
just written the rules it broke.**

> **A newly written reader defaults to UNDER-reading, and under-reading is the
> direction that reports "all clear".**

Matching one line missed `sites.sh --channel`, **a two-line arm** — the same
column-0 anchoring that had `--gate-set` reporting **16 of 44** — and the next
pass **discovered `--flag` from `ci.sh`'s own fixtures**, which is *a fixture is
not a TOOL*: the mirror of §9.7's *a fixture is not enforcement*, and
self-selection (§5.4) arriving through **test data** rather than source.

**My addition is the direction, because it is what makes a new reader dangerous
rather than merely immature**: a reader that under-reads finds fewer sites and
reports fewer problems, so its first run looks like good news. **The failure
mode of a new instrument is congratulation.**

**(4) §5.4b — THE RESTRAINT RIDER.** The pre-existing gate double-listing was
**flagged, not de-duped**.

> **A de-dupe could silently shrink a set.**

**An instrument auditing a set must not repair it**: de-duplication is an edit
made by the reader on data it does not own, and a wrong equality test removes a
member **while the count moves in the direction that looks tidy**. *The census
RECORDS and never adjudicates* (§5.4a) applies to a reader's **input**, not only
to its verdicts.

**(5) NOT DISPATCHED, TAKEN FROM THE SAME COMMIT because it guards a rule this
lane landed:** `--classify` now asks **the lakefile** instead of three hard-coded
prefixes, and its note names the consequence — outside all `lean_lib` roots,
never compiled, **so a rebase touching only it owes no re-gate.**

> **NOT COMPILED IS NOT NOT RUN.** A file `lake build` ignores is still Lean;
> `lake env lean` on it is Lean execution, and **A11 covers it regardless of
> whether any target does.**

The two facts sit one line apart and pull opposite ways — *"nothing rebuilds
it"* is true about the **build graph** and says nothing about the **lock** —
which is exactly how a rebase exception could be misread into an unticketed
run. And the classifier's restraint is the pattern worth copying: **the note
EXPLAINS, it never DOWNGRADES.** A tool that has learned something new tells the
lane about it **without quietly buying it a cheaper tenure.**

**Index:** MEAS-131 … MEAS-134, OPS-69 … OPS-71.

## 2026-08-23-architecture-46 — A guard that always fires; a procedure is not a gate; and WAITING names its trigger

Three from the Lean tier's standdown (`38766b4`, on master; the tier is WAITING
with working guards).

**(1) §5.4b — THE VACUOUS GATE'S MIRROR, measured by a lane on its OWN guards.**
Two of four fired at standdown and **both were self-inflicted**: the baselines
were pinned to **the lane's own branch commit** (`71829bf`), so **every future
commit would re-fire them.** The census drifted **raw 138 → 141 with real
113 → 113** — the movement was the lane's own docstring prose.

> **A guard that ALWAYS fires is exactly as useless as one that never can.
> Either way the lane learns to ignore it, and the drift it was watching for
> arrives unnoticed.**

**It is MEAS-35's mirror exactly** — the audit's class was *a `--compare` that
cannot exit nonzero*; this is *one that cannot exit zero*. The two look nothing
alike, one silent and one noisy, and they end in the same place: **a gate is a
channel, and a channel stuck at either value is off.**

**THE FIX NORM, and its second half is what I made sure landed.** Baseline
against **upstream, never yourself** — a `git worktree` pristine master (2.1 MB)
without touching the branch, correspondence now based at **`e0e3f6bcccb8`**.
*The re-baseline corrected WHAT THE GUARD WATCHES, not what we measured.*

> **A re-baseline is complete when it names what the guard now watches AND
> reports that no published fact moved.**

**Because re-baselining is the one repair that can silently erase the finding it
was meant to report**: *"we moved the baseline"* and *"we moved the goalposts"*
produce **identical diffs**, and only a published comparison separates them.
Here it is published — `rules_by_relation` unchanged (**STUB 17**, so the
*24%-maps-to-a-stub* headline holds), **113** real, **24** proof-layer.

**AND A THIRD MEMBER OF THE never-executed FAMILY**, beside *a check that has
never failed is a design, not a control* (§5.4) and *an amendment that has never
fired…* (§7.1a):

> **A duty that has never been EXECUTED is a plan, not a duty.**

Which is why running the guards was the lane's **first** act on entering
WAITING — and why running them is what found the defect.

**(2) §5.4b — A VOCABULARY RULE, because this section COUNTS things: A
PROCEDURE IS NOT A GATE.** The arena check is recomputed **by hand** from a
downloaded `results.json`, **no `--compare`, no committed baseline**. It caught
real movement (**66/67 → 67/67**), so it earns its place; calling it a guard
overstates it.

> **A procedure earns its place by what it CATCHES; a gate earns its name by
> what it RUNS. Instrument it, or rename it.**

**Not pedantry, because of enumeration**: §5.4b's pointer list is counted, and a
procedure counted as a gate adds a row **nothing executes** — it does not even
reach `DECLARED` on the four-state ladder, since there is no declaration for an
enumerator to find. **A gate set padded with procedures reads as coverage and is
staffed by memory.**

**And the honest gap recorded beside it**: the spec census **cannot run** (LaTeX
corpus purged) but its **baseline is committed and its instrument pinned**, so
re-fetching restores it. *"Armed and not runnable, and here is what restores
it"* is §5.4a's provenance remedy applied to a gate — **a gate that cannot run
today is a stated gap; a gate quietly dropped from the list is a coverage
claim.**

**(3) §9 — WAITING IS A STATE ONLY WITH AN EXECUTABLE TRIGGER**: *a DRIFT in the
census's `real` count, or `addInduct`/`VInductDecl.WF` leaving
`definitional_stubs` — which is PR #43 landing, and unblocks 15 of 24.*

> **WAITING names an executable trigger, or it is a euphemism for stopped.**

**The form matters**: *"when upstream is ready"* is unfalsifiable and ages into
silence; *"when this number moves"* is a check with a verdict the lane can be
**wrong about in public**. **And the enabling condition is affordability**, which
is the half a lane skips — the duty is pure Python over out-of-tree corpora, **no
Lean, no tenure, no ticket**, so it runs at any cadence. **A waiting duty priced
at a tenure will not be run, and an unrun duty is a plan** — so the two halves
are one design: name a trigger a cheap command can answer, and keep the command
cheap enough that nobody has to decide whether to run it.

**Index:** MEAS-135 … MEAS-139.

## 2026-08-23-architecture-47 — The shape set had a fourth member; and duplication is discovered by changing

Five from QoL's `b2150ae` + `ccdc839` (both on master).

**(1) §5.4a — THE ANNOTATE CHANNEL, and it is the sharpest member of the
position family yet.** `runIndetRaw : … Halt …` names the **type** and **no
constructor**, so every `sites.sh` channel — all greping `\.$CTOR` — was
**structurally blind** to it. A lane counted constructors and destructures,
called the change priced, and **red a tenure on the signature that survived.**
Live, full scan: **DESTRUCTURE 13, CONSTRUCT 18, ANNOTATE 20 — and all 20 name
no constructor.**

> **The type has MORE annotation sites than destructure sites, and the old
> census could see none of them.**

**The failure is one of KIND, not of threshold**, which is what I made the
paragraph turn on: no cutoff on the old channels could have found these,
because the thing counted never appears in them. The family's earlier members
were **wrong counts**; this is a **missing column**, and a missing column is
invisible to every check that reads the table.

> **A channel that greps the CONSTRUCTOR cannot see the TYPE. Enumerate the
> KINDS of position — destructure, construct, ANNOTATE — before enumerating the
> positions.**

**Rider, learned mid-landing: a leading dot and a qualifier are DIFFERENT
dots.** Excluding every preceding `.` rejects `LeanModels.C.Halt`; allowing
every dot accepts `.Halt`, an anonymous constructor. **What precedes the dot
decides** — and a discrimination that fine is the *ordinary* case in a
positional matcher, which is why *"just grep the name"* produces numbers wrong
in both directions at once.

**And one cost note against the usual expectation:** the stripper is the
expensive part and does not depend on the pattern, so the second regex **rides
the first traversal** — 3 626 → 3 732 files in the same 45 s budget. **The
channel is free.** Worth checking before a channel is refused on performance
grounds.

**(2) §7.2 — THE SECOND COPY, found by CHANGING the thing it guards.** Putting
`refusal_census` in the floor surfaced that `gate_floor` **carried its own
second copy of the list** — *the classified and unclassified paths could have
run different gates, silently.*

> **Duplication is discovered by CHANGING, not by reading.** A second copy is
> invisible while the value is stable; it announces itself the first time the
> value moves, and only to whoever moves it.

**Landed with the procedure**, so it is usable rather than rueful: when you
change a constant more than one path consumes, **grep for the OLD VALUE before
you grep for the name** — the stale copy still carries it, and the name may
differ. It is also why MEAS-28's instrument reports **contracts** as well as
names: a second copy of a *list* rarely shares a spelling with the first.

**And the second defect from the same wiring is the more instructive one,
because it would have WORKED**: `gate_runner_targets` would have succeeded **by
accident** inside the floor (which also names `diff_test`, supplying the runner)
and failed under `--gates-only`. **A dependency satisfied by a NEIGHBOUR is not
a dependency met — it is a dependency hidden, and it surfaces as someone else's
red.**

**AND THE FLOOR CHANGE REACHED THIS DOCUMENT, correctly, in the same commit.**
§7.1a **enumerated** the floor's members, so that sentence was wrong the moment
the floor changed; the QoL lane landed the doc edit with the code — doc-first
working from the other side. The law I took from having been on the receiving
end of it:

> **A document that ENUMERATES a set owns that set's maintenance. Enumerate only
> what you will maintain, or point at the source of truth.**

Stated without absolutism, because this charter does both deliberately: an
enumeration is **readable** where a pointer is **durable**. The honest framing
is that **an enumeration is a copy — and a copy in a charter is a copy the code
cannot see.**

**(3) §7.2 — THE `--classify-default` REJECTION, landed as a ruling.**

> **Classification NARROWS, so default-on makes NARROWING the default — every
> lane's coverage would depend on the classifier being right without anyone
> asking.**

The same reading the `--gates` ruling rejected, arriving through a convenience
instead of a flag: **a default that makes a run cheaper is a default that makes
a claim smaller**, and nothing in the log records a narrowing nobody requested.
The advisory resolves it — one enqueue line saying what the diff *would*
classify as, behaviour unchanged — and it runs **in a subshell** because
`classify_list` sets `BUILD_TARGETS`:

> **An advisory that leaked would narrow the build it only describes.**

**A description that can change its subject is not a description**, and the
subshell is what makes *"advisory"* true rather than intended.

**(4) §5.4b — A THIRD WAY A CHECK CAN BE HOLLOW.**

> **A row asserting that something did NOT change passes whenever the code never
> ran. It needs a sibling asserting the code DID.**

Caught live: the sentinel passed because `class_hint` was defined **after** the
self-test, so the call was command-not-found — a variable never touched is
trivially unchanged, and **only the output-expecting siblings failed (rc 127)**,
which is what exposed it. This is §5.3's vacuity ruling **inside a self-test**:
a negative assertion is the one row for which **absence of content is
indistinguishable from success.** So: **pair every "did not change" with a "did
happen" — the positive row proves the negative row was watching.**

**(5) §7.2 — A BUILD LOG MUST SAY WHOSE IT IS.** 68 logs grepped for a lane tag
matched **nothing**; every log was on disk and **not one could be attributed.**
**An artifact with no identity is not evidence — it is storage.** One
identifying line per attempt, stamped first because the redirect truncates.

**And its inertness is ASSERTED, which is the transferable half:** a header
riding inside the file whose failures are **counted** changes the input of every
downstream reader, so **the same red log with and without it yields
byte-identical error-line, failed-module and axiom-ledger verdicts**, and it
carries no hostname.

> **A stamp added to a measured artifact owes a DIFFERENTIAL: the same input,
> with and without it, must produce the same verdicts.**

*"Obviously inert"* holds right up until a counter matches a substring or a
reader keys on the first line — and **one differential run retires the
argument.**

**Index:** MEAS-140 … MEAS-144, OPS-72 … OPS-75.

## 2026-08-23-architecture-48 — A witness must fail for the reason it names; and INAPPLICABLE is not OPTIONAL

Two from pyc's 3c-i-c (**ticketed**; both landed conditional on that landing and
stamped at the site).

**(1) §5.4 — THE SPELLING HALF OF THE WITNESS-NAMING LAW.** A never-stepped-
binding row spelled `print(type(e).__name__)` would have **refused at `type`** —
a builtin out of tier — and been **filed as evidence about `enumerate`.**

> **A witness must FAIL FOR THE REASON IT NAMES**, and naming the row for its
> construct does not secure that: **the SPELLING has to be in tier too.**

**The mechanism I put beside it**: a row is a small program, and **every token in
it is a claim that the tier can run that token** — so a witness written in the
vocabulary a reader finds natural reports **the first thing the tier lacks**,
which is rarely what the row is about. The fix is the pattern: **minimal
spelling** — `print('bound')`, where **reaching the `print` IS the
observation**, leaving no second construct to fail first.

**And how it was caught is the part I would not let pass**: by **reading the
builtin tables before the ticket**, not by a red. The bad version would have
been **loud** — a refusal, not a wrong answer — and still wrong, because the
refusal would have been **filed under the wrong subject.**

> **A loud failure attributed to the wrong cause is a silent one for every
> reader downstream.**

That is what makes this the spelling half of *rows and witnesses are named for
the CONSTRUCT*: the naming law makes a row's **subject** durable; this one makes
its **evidence** honest, and a row can satisfy the first while failing the
second.

**(2) §9.7 — A FOURTH KIND OF NO-CODE CLOSURE: INAPPLICABLE, NOT OPTIONAL.** A
transition theorem was owed for a construct the trunk **refuses to step**, and
**a refusal has neither `GenSteps` nor `GenSilent`** — so nothing exists for the
theorem to quantify over.

> **The theorem is not WAIVED; it has NO SUBJECT.**

**The vocabulary is the whole point.** *Optional* is a judgement about
**priority** and invites a later reader to reinstate it; *inapplicable* is a
statement about **the tree**, and it carries the condition that would change it
— **the day the trunk steps that construct, the subject exists and the
obligation is live.** A closure recording *"not needed"* loses that trigger; one
recording *"no subject, and here is what creates one"* keeps it. Which is the
WAITING rule (`-46`) applied to an obligation instead of to a lane.

**And the line against WOULD-BE-VACUOUS**, since both end in *"do not write
it"*: a vacuous check **has a subject and cannot fail**; an inapplicable one
**has no subject at all** — the first is a design error the lane could commit,
the second is a fact about where the tier stands.

**RIDER — §5.2, AND IT IS A THIRD ZERO.** The inch's headline is that **the
whitelist did not move**: *it adds capability without adding a refusal.* **A
refusal census reports that result as silence** — a capability inch normally
shows rows *leaving* the whitelist, this one shows **nothing at all**, so **the
non-move is the finding and it has to be claimed in prose, because the artifact
cannot claim it.**

Now three zeroes, and they must not be pooled: a **zero count** for a class the
tier can emit is about the **corpus**; a **zero count** for one its API cannot
build is about the **tier**; a **zero DELTA across an inch that added
capability** is about **the inch**. **Same digit, three claims.** With the
limit stated: an unchanged whitelist proves the inch added **no new refusal**,
not **no new behaviour**.

**Index:** MEAS-145 … MEAS-147.

## 2026-08-23-architecture-49 — A full build is its own root; and 27 green rows that could not see the call site

Four from QoL's `2b3d608` (§5.4a-i is live on master — the increment-green
model, ledger, refusals and merge-bar line landed doc-first, in this lane's
file, with the code).

**(1) §5.4a-i — THE LEDGER'S SCOPE, and the section's own wording corrected.**
It said **per-CLONE**; the unit is **per WORKING DIRECTORY**, scoped by
**`--git-dir` and never `--git-common-dir`**, because **a linked worktree shares
the common git dir and has its own `.lake`.**

> **The cache is part of what produced the green.** Scope the evidence to the
> directory that holds it.

**This is the unit family arriving in git plumbing**, and it is the sharp kind:
`--git-dir` and `--git-common-dir` **differ on exactly the case the feature
exists for**, and the plausible-looking one is wrong. Worth flagging that a
worktree is **this repository's standard way of taking a pristine baseline**
(§5.4b's re-baseline norm), so the wrong scope would have misfired **precisely
where lanes are being most careful.**

**AND ONLY GREENS ARE RECORDED — reds record nothing.**

> **A ledger of ATTEMPTS is a log, and a log is not evidence of a verdict.**

The ledger exists to be **citable as a base**, and only a green can be cited; an
attempt history answers a different question for a different consumer (the build
log, now identified and attributable, `-47`). **Mixing them would make the
ledger's own name a claim it cannot keep** — a reader finding reds in a file
called `triad-greens` would be right to distrust everything else in it.

**(2) §5.4a-i — THE MODEL'S FIRST THEOREM, which survived its own
implementation bug.**

> **A FULL BUILD IS ITS OWN ROOT, HOWEVER IT WAS REACHED.**

An increment whose build was **not narrowed** is a full build whatever flags
produced it, so it **starts a chain** rather than extending one. Measured the
hard way: such a run was recorded at **`depth=1` under an older root** until the
full-build test was moved **first**.

**The distinction I made sure the text keeps**: *the invariant was right and the
implementation asked the questions in the wrong order.* The fix is a
**reordering**, not a rethink — and a lane reading only the bug report would
have concluded the model was wrong. Generalized:

> **When one predicate SUBSUMES another, ask it FIRST — or the subsumed one
> answers on its behalf, and the answer is quietly narrower.**

**(3) §5.4b — THE POINTER LIST APPLIES TO A TEST SUITE, which is where it is
hardest to believe.** Two bugs shipped past **27 passing unit rows**:

> **The rows tested `record_green`'s ARGUMENTS, not what the CALL SITES pass.**

Every row pointed at the function; **none pointed at the seam** — so the suite
was exhaustive about the callee and blind to the caller, and **the end-to-end
run was the only thing that could see it.** §5.4b's own claim arriving where a
lane is least likely to audit, because **27 green rows read as thoroughness.**

Filed as the **fixture-vs-reality family at the INTEGRATION SEAM**, beside *a
fixture is not enforcement* and *a fixture is not a tool*, with the sentence
that makes it actionable: **a unit row supplies its own arguments, so it tests
the function against the author's belief about the call. Where a suite's inputs
are authored, its coverage stops.**

**(4) RIDER — ABSENCE IN A NEW COSTUME.** `targets=` came out **empty for a full
build** because `sed 's/^$/all/'` **does not fire on empty INPUT** — *there is
no line for it to match.* A substitution that rewrites an empty **line** is not
one that rewrites empty **input**, and the pattern cannot tell them apart.

> **A transform on nothing produces nothing, and reports success doing it.**

I listed the family's costumes together, because that is the useful part: a
`null` measured on an absent repo, a zero-row census, a negative self-test row
that never ran, and now a `sed` with no line. **The constant is that the empty
case takes the success path** — so the check never changes: **name what the
non-empty case would produce, and assert that.**

**Index:** MEAS-148 … MEAS-153.

## 2026-08-23-architecture-50 — The goal is COMPLETION, and a milestone is a waypoint

**From Thomas directly, landed in §9 as strategy — the highest authority in the
charter, and it reframes every item under §9.**

> *"It's not enough to stop at 'we proved one function works.' The goal is to
> COMPLETE the lean-surfaces project for the target languages. That's months of
> work or more — don't call the goal done after a day."*

**(1) §9.0 IS NEW, AND IT SITS FIRST IN THE STANDING STRATEGY.** Each tier's
endgame is **full-spec support, measured by that tier's own conformance suite**
— test262 (ES), gcc.c-torture (C), ACATS (Ada), sv-tests (SV), the Wasm spec
suite, Go's stdlib reach instrument, and Python's refusal surface plus the
flagship theorem. Landed as a table so no lane has to ask which number it is
judged by.

> **Every lane ledger carries its standing SPEC-COVERAGE NUMBER, updated per
> landing, stamped with its sha.**

**In the LEDGER, not only in a charter**, for the reason `-47` had already
established from the other side: **a ledger is appended per landing so the
number moves with the work, while a number in a charter is a copy the code
cannot see.**

**And I said what the instruments were for**, because that is the sentence that
makes the section cohere rather than read as a new demand: suites driving scope
(§5.6), coverage as `stated/(stated+refused+out-of-tier)` (§5.5), the four
refusal causes with separate retirement schedules (§5.2), reach censuses
(§9.0b) — **all of it exists to make that one number honest and re-derivable.**
A completion goal without an instrument is a wish; **the instruments were built
first, and this is the target they were built for.**

**(2) A MILESTONE IS A WAYPOINT — and this lane published the milestone that
prompted it.**

> **"The exemplar is complete" describes an EXEMPLAR. It never describes a
> TIER.**

**The failure mode already had a name here**: it is §5.4's construct-versus-
verdict naming law **at the scale of a project**. And the reason a waypoint
reads as an ending is worth keeping, because *nothing about the waypoint is
wrong*: a completed exemplar is the first thing in a tier that **feels
finished** — theorem, clean axioms, a name. **The defect is entirely in what a
reader infers next.** Hence the enforceable form:

> **A claim of completion cites a SUITE NUMBER and its SHA, or it is a claim
> about an artifact and not about a tier.**

`2026-08-23-architecture-37` is **annotated** accordingly (not rewritten), and
§5.6 now says *waypoint* at the milestone itself.

**(3) DEFERRED-UNTIL-CONSUMER UNLOCKS ARE AUTHORIZED WHEN THE CONSUMER IS
COMPLETION.** This document has been strict that *adding a snapshot without a
consumer is designing against nothing* and *predicting a consumer is not having
one*. One consumer is now standing:

> **The spec surface IS a consumer. A deferral whose trigger was "when someone
> needs it" is unlocked when COMPLETION needs it.**

**First instance: Go's `go/types` extractor tier** — deferred while nothing
consumed selector resolution, now required because the stdlib reach the tier is
measured by runs through it (§5.4a's *value or reference* split already named it
as the extractor's work).

**And I landed the guard that keeps this from retiring a law that has paid for
itself**: completion authorizes **the work**; the census still authorizes **the
order**. *"Completion needs it eventually"* is true of every construct in the
language and therefore **prices nothing** — the reach census says which unlock
is next, and the conjunctive law says which ones must ship together.

**(4) §9 — WAITING TIGHTENS: it is a property of a SLICE, never of a LANE.**

> **A blocked slice waits. The lane's foreground moves to a new censused
> corner.**

First instance the Lean tier, whose upstream-blocked obligations keep their
trigger and their standing guard duty while the lane's foreground is
re-censused. **A lane with nothing to do because one slice is blocked has not
measured its corpus** — §9.0b's partial order read as a work queue: the blocked
slice is one node, and **a census that produced only one node was not a
census.**

**THIS LANE'S OWN STANDING NUMBER, stated rather than skipped.** The
architecture lane models no language and has no conformance suite, so it has no
spec-coverage number; **recording the exemption is the point** (§5.4b: a
documented exception is an exception, an omission is an undocumented one). What
it carries instead, per landing: **`docs_check` marked-block count** (91/91
today) and the **law-index id ranges** minted, which are the closest thing this
lane has to coverage — *how much of the tree's checkable prose is checked, and
where each law durably lives.*

**Index:** MEAS-154 … MEAS-159.

## 2026-08-23-architecture-51 — A row that kills two wrong models; and a minted law caught its own lane's future error

Four from Go (`da9a7bc` + `fef0b79`, both on master).

**(1) §5.6 — A FOURTH TIER ATOP THE ACCEPTANCE HIERARCHY.**
`runtime.printuint`'s array never escapes, so the case is **one array, two
operations**: `b := a` copies, `s := a[:]` aliases, `gc` says `"wSyz"` —
**arrays-as-headers gives `BSyz`, slices-as-copies gives `wxyz`.**

> **Both wrong models fail the SAME ROW, in OPPOSITE directions** — strictly
> better than `Reverse8` and `out[:cap(out)]`, each of which killed one.

**Two things one row buys that two rows do not**: it refutes both candidates,
and **the DIRECTION of the failure names WHICH wrong model you have** — the
difference between a refutation and a **diagnosis**.

**And I said plainly that the top two tiers rank on different axes**, so the
hierarchy is not misread as a single ladder: *cannot be stated* is strongest on
**when** you learn (design time); *fails in opposite directions* is strongest on
**what** you learn (which candidate survives). **A row can be both**, and a lane
choosing should ask which it is short of.

**(2) §9.7 — THE REGISTER FIRED PROSPECTIVELY, and that is a different KIND of
evidence.** §G8 wrote *"pricing it as reach would be the motivated error"*;
§G20 priced `SelectorExpr` as reach (**+1 189**); §G21's census caught it
**before a line was built** — split like `ArrayType`, measured as **executable**
reach with `cmd/` and `unsafe`/C excluded: **+203, not +503. Overstated 2.5×.**

> **A law minted from one lane's error caught the same lane's FUTURE error,
> before it was paid for.**

**The audit showed the families were DESCRIPTIVE** — they named defects already
in the tree. **This shows one is PREDICTIVE**: written as a warning about a
mistake nobody had made yet, the lane made it anyway, and **the warning's own
instrument stopped it.** A taxonomy cannot do that.

**And the honest reading of the outcome matters as much as the catch**: the
correction did **not** kill the tier — **+203 on a 587 baseline is still +35%
and still the largest move available** — so the authorization stands and the
tier is **sized on 203**. *A law that catches an overstatement is not a law that
cancels the work; it is a law that prices it.* Pointer added at §5.4a's
motivated-error rule.

**(3) §5.2 — A FIFTH CORRECTNESS SHAPE: A RESOLUTION CAN BE WRONG, NOT MERELY
MISSING.** `pkg.F` where `pkg` is **shadowed by a local** is a value selector
wearing a package's name.

**The two failures land on opposite sides of this section's own boundary**,
which is why it needed naming: a **missing** resolution is a **REFUSE** — loud,
classed, retiring on a schedule; a **wrong** one is **a value**, so it is a
**DIVERGE**, the verdict this scoreboard requires to be zero.

> **Every resolution rung owes a SHADOWING ROW.**

Generalized past `pkg.F` to every name-to-thing step — imports, selectors,
methods, builtins: wherever a model turns a **name** into a **thing**, the
language usually lets the same spelling mean something else, and **a tier that
models only the expected binding builds a resolver that cannot be wrong in its
own tests while being wrong in the corpus.**

**(4) §9.0 — GO'S SPEC-COVERAGE TABLE IS THE TEMPLATE**, and I recorded the
three properties as the shape other tiers copy rather than the numbers:
**two denominators with the choice's cost stated (3.5 points)**, because a
single figure hides a modelling decision; **the syntactic-upper-bound guard** —
*a syntactic-only win must never be banked there; recognising `fmt.Println` as a
package call is not running it*; and **the ceiling at current vocabulary**,
which is the retracted `+0` law's lesson applied to a coverage figure — **a
coverage number is a delta against a vocabulary and moves when the vocabulary
does.**

**RIDER — the `(function, argument)` law became a PROCEDURE.** Copy-by-value is
the decider and **the corpus does not do it**: `a[:]` outnumbers bare-identifier
copying **1 911 to 152**; 1 407 `[N]T` occurrences yield **23** possible copies;
all six in-reach candidates are wrappers taking `*[N]byte`, **pointers precisely
to avoid copying.**

> **No corpus witness is not a dead end; it RELOCATES the discriminator into
> the call.**

**Census for a witness → if none, move the discriminator into the call →
confirm the call is one a caller would write.** Go ran exactly that sequence and
it produced the one-array-two-operations row above. That is the moment the law
stopped being a description and became a procedure.

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; law-index ids minted here **MEAS-160 … MEAS-164, STMT-114**.

## 2026-08-24-architecture-52 — The resolution gate is two-sided; a file needs every function it calls; and a commit cannot contain its own hash

Three from Go E1 (`4a9f9ec`) with two riders, and three from SV's 17-second red
(re-ticketed).

**(1) §5.2 — THE RESOLUTION GATE IS TWO-SIDED, which completes the shape landed
yesterday.** **484 shadowing binding sites across 198 stdlib files**, so this is
a live surface. Both directions are real: **reckless** resolves a shadowed use
(**wrong answer**, DIVERGE); **timid** refuses an unshadowed one (**lost
reach**, a REFUSE that need not exist).

> **A merely-CONSERVATIVE resolver fails this gate exactly as a reckless one
> does.**

**The timid direction is what a naive fix causes**, which is why it needs rows
and not a note: Go's `:=` binds **only from its declaration point**, so a use
**preceding** the shadow and one whose shadow is in a **sibling block** must
both still resolve. Battery: **10 rows, exit 6, non-vacuity run — reckless fails
4, timid fails 2.**

Landed as the paired-guard law arriving where it is hardest to believe, since
one side of the pair **looks like caution**: **a correctness gate bounds BOTH
error directions; over-refusing is a failure mode, not a safe default.** And I
noted the reason pooling them would hurt: the reckless side is a **DIVERGE**
(must be zero), the timid side a **REFUSE** (shows up in coverage) — pooling
hides a correctness defect inside a coverage number.

**(2) §9.0b — THE CONJUNCTIVE LAW'S THIRD LEVEL: BUNDLE → FAMILY →
PACKAGE-FUNCTION.** §G21 priced `math/bits` at **+7** from the package ranking;
E1 built the mechanism and measured **+0**.

> **A file needs every FUNCTION it calls, not the package's name.**

Blocked by `Add64` (2 077 sites), `Mul64` (1 038), `Sub64` (186) and `Div` —
**all multi-value returns, blocking 88% of `math/bits`' call sites.**

**And the lane read its own `+0` correctly, which is the retraction paying
off**: *not a rung on its own AT THIS VOCABULARY, not worthless.* That is
exactly the reading `2026-08-23-architecture-42` bought, arriving one inch later
in the lane that paid for it.

**The scheduling consequence outranks the number**: the next rung is multi-value
returns, **a walker rung**, reached from an extractor rung — so **the
extractor/walker alternation is what the census SAYS TO DO, not a scheduling
convention.** My addition: **an alternation adopted as a convention is a rhythm;
one derived from a census is a consequence**, and the difference shows the first
time the census says *two walker rungs in a row* — a convention would resist
that, a consequence has nothing to resist with.

**(3) §7.2 — A GIT MECHANIC THAT DEFEATS THE OBVIOUS STAMP.**

> **A COMMIT CANNOT CONTAIN ITS OWN HASH.** An `--amend` to insert it
> invalidates it, leaving a citation to a **destroyed** commit.

The §9.0 stamp discipline asks each landing to carry its sha, and the natural
move produces a message naming a commit **that no longer exists** — not stale,
**without a referent**. **Each rung's sha lands in the FOLLOWING commit.** I
recorded it as a property of the artifact rather than a workflow preference: a
self-referential identifier is impossible for the same reason a checksum cannot
cover itself.

**RIDERS FROM THE SAME RUNG, both about what an acceptance case must CONTAIN.**
**A dispatch table with one entry is indistinguishable from a hard-coded
answer** — the walker vendored **two** functions for that reason: *one row
proves an answer, two prove a lookup*, which is §5.3's vacuity ruling one level
down, in the implementation. And **the gate landed WITH the capability**: the
resolver self-test went into the triad gate list in the same landing, so the
shadowing discipline is enforced by the gate and not the operator. *Fixes live
in gates* is usually retrospective; **applied at birth it costs nothing and
skips the incident** — the cheapest form the rule takes and the easiest to skip
while the capability still feels well understood by its author.

**(4) §7.1a — `set_option autoImplicit false` IS A REQUIRED LOUDNESS GUARD FOR
MODEL FILES** (SV). The 17-second red was loud **only because that option is
set**; without it Lean would have **silently bound the unknown identifier as an
implicit universe variable** and failed **later and stranger**.

> **It converts a strange late failure into a named 17-second one.**

**It is a loudness control, not a style preference** — the setting does not
prevent the mistake, it decides **where and under what name** it surfaces. And
the general shape, since every tier meets a version: **a language feature that
silently supplies a plausible meaning for something the author did not write is
a loudness hazard**, and the fix is always to turn it off in files that ARE the
model, where a wrong meaning is a wrong semantics.

**(5) §9.0a — THE PRE-FLIGHT'S SECOND HALF.** The clash check finds **duplicate
declarations** — names you DECLARE. It says nothing about **identifiers that
resolve NOWHERE** — names you USE. An **import-reachability check** completes
the pair: resolve every capitalized identifier a new file uses to its defining
module, confirm the module is in the closure. **The two halves are the same
query pointed in opposite directions**, and the second is the one a lane skips
because *"the build will just tell you"* — which it does, in whatever vocabulary
the missing name happens to trigger. **Its one false positive was NOTED, not
papered over** (a docstring naming another tier's type); comment-stripping is
the known fix, and recording it is what keeps the check from being quietly
narrowed to silence the noise.

**(6) §9.0 — SV IS THE SECOND LANE TO LAND ITS STANDING NUMBER, with two
disciplines the template did not yet name.** **LIVE is the honest
denominator** — 18/21 envelopes, because **a vacuous row must not read as
agreement**:

> **A coverage number's DENOMINATOR counts what could have DISAGREED.**

§5.3's vacuity ruling in the denominator, which is the more dangerous position:
**a denominator is quoted without its definition far more often than a verdict
is**, and dead rows inflate only in the flattering direction. And **11/11
stepper constructors, six through the delegating arm** — *they are not
reimplemented, they are forwarded, and the `agrees` theorem proves the
forwarding.* **Delegation normally weakens a coverage number**; the theorem is
what converts it from a liability into a legitimate numerator entry.

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-165 … MEAS-171, STMT-115, OPS-76, OPS-77**.

## 2026-08-24-architecture-53 — A goal theorem nobody has typed; and a false premise vacates rather than weakens

Eight dispatched from two sources — the R-track chain document (merged in
`7906a8d`) and SoftFloat's `Round.lean` (`ec1e79b`, ticketed) — plus two table
additions. **All eight landed; one arrived sharper than dispatched.**

**(1) §9.0 — THE TARGET MUST BE TYPED.** The flagship existed **only in prose**.

> **A goal theorem nobody has TYPED is one nobody can typecheck against.**
> **A chain document's first rung is the STATEMENT, and a WAITING lane cannot
> cite an unstated theorem as its target.**

**This closes a gap in `-46`'s WAITING rule**, which required an executable
**trigger** and said nothing about the **target** — a trigger that fires against
an unwritten theorem tells a lane to start work it cannot check it has finished.
The pair is now complete: **a state names the trigger that ends it AND the
statement that defines done.** The failure is quiet, because prose about a
theorem reads exactly like the theorem until someone elaborates it.

**(2) §5.4a — THE RE-FOUNDING DENOMINATOR, second instance of MEAS-127.** Rung
6 priced at **221**, actual **57**: the population was *every statement in the
affected files* (**558**) rather than the ones a re-founding touches (**200
across three files**).

> **A re-founding's size is the count of statements that NAME the interpreter.**

**SV's honest-denominator law pointed at COST rather than COVERAGE** — the same
defect in different clothes, and **both inflate while looking conservative.**
That word is what stops the re-measurement, and I said why it should not:
**a 4× over-estimate kills the work outright**, which is what it nearly did
here, and **a killed inch produces no correction, because nobody measures what
was never attempted.**

**(3) §9.0 — A DECLINED ALTERNATIVE IS RECORDED WITH THE MEASUREMENT THAT
DECLINED IT.** `twinAgrees` declined **on the plan's own pricing** — transport
pays only above ~100 mostly-mechanical theorems in one file, and no file clears
it.

> **Record the fork WITH the computed price, so a later lane finds it COMPUTED
> rather than re-derived.**

**A declination without its number must be re-litigated by every new reader**,
and re-litigating is expensive precisely because the number was. The provenance
law pointed at a **road not taken**.

**(4) §5.3 — A FALSE PREMISE VACATES RATHER THAN WEAKENS.** Plain `BoundRefines`
is FALSE (refuted at `.int 5`), so the original `RecursionStep` was **vacuously
true** — green, elaborating, about nothing.

> **A false premise does not weaken a theorem — it VACATES it, and a vacated
> theorem PASSES.**

**Which is why `BoundRefinesW` is load-bearing and the chain must use it
throughout**: one downstream statement left on the old premise re-opens the hole
silently. **The other vacuity shapes announce themselves as EMPTY** — a run that
executed nothing, a row that never ran. **This one announces itself as a
proof**, the worst available disguise: nothing missing, the tactic closed, an
artifact that is a theorem in every respect except subject matter.

**(5) §5.4b — THE SECTION CITATION IS MECHANICALLY CHECKABLE, and I landed it
sharper than dispatched.** Verified: `docs/python-monadic-rebuild.md` cites
`§8.5` four times and has no §8.5 — and the lane had already written *"the
anchor dangles"* at its head, which is honest and **is not a control**.

**But MEAS-30 already rules it**: *inside a `.md` an untagged `§` is an INTERNAL
reference*. So these are not dangling anchors, they are **untagged
cross-document citations** — the intended referent is this charter's §8.5 and
the spelling says that document's. **The defect is a missing filename, not a
missing section**, which is a different and much smaller fix. Gate shape landed;
the fix stays routed to the rebuild lane.

**(6-7) COOKBOOK §24 — `op_correct` MENTIONS NO ALGORITHM, and omissions are
STATED.** SoftFloat deliberately did not write the computable `roundQ` before
stating `op_correct`, and the tie rule is a **parameter** (ties-to-even /
ties-to-away become instances). The trap, stated so it is recognizable:
**any correct implementation is structurally the same finite computation**, so a
statement phrased in its terms collapses to *"this computes what this
computes."* **The tell is that the spec file imports or restates the
implementation — a spec that cannot be read without the code is not a spec.**

And the omission half: `ReprQ` carries **no upper exponent bound** because
overflow is mode-dependent — folding one in would silently redefine *"nearest
representable"* as *"nearest representable **or ±∞**"*. **§0.1's forbidden move
arriving as tidiness.**

**(8) §9.0 — THE NUMERATOR'S HALF, third instance, and the lane excluded its own
work to get it right.** SoftFloat's number is **1/12 with 21 real landed
theorems EXCLUDED**.

> **The DENOMINATOR counts what could have DISAGREED; the NUMERATOR counts only
> what the family's own definition ADMITS.**

**Both halves fail in opposite directions**, which is why neither alone
suffices: a padded denominator **understates** while looking rigorous, a padded
numerator **overstates** while looking industrious — **and the second is the
tempting one**, because the 21 theorems are real, landed and green, and the only
thing wrong with counting them is that they do not answer the question the
number asks.

**TWO MORE LANES' NUMBERS.** **ES: 38/66 kinds, 2 869 → 4 118, +1 249 matching
its census prediction exactly** — and I recorded why that is more than a number:
**every other reach figure in this document is a measurement; this one is a
prediction that was then measured**, which is the only way an instrument's
ACCURACY is ever established. **An instrument that has never predicted has never
been tested.** And **the Lean tier NAMED, NOT COUNTED its 28th obligation** —
the vacuity-in-denominator family through the opposite door: **not a dead row
inflating the denominator, but a live obligation kept out of it until its
premise is proved. Named so it cannot be forgotten; uncounted so it cannot
flatter.**

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-172 … MEAS-178, STMT-116 … STMT-118**.

## 2026-08-24-architecture-54 — When the ambient verdict is constant, every bit is in the pin

Three from Wasm O3 (`fd96fce`, verified on master) plus a roster fact that
turned out to be a defect in this document's own registry.

**(1) §5.4b — THE COMPLETE EXHIBIT, and it is stronger than the one this section
already had.** **Exit code was `1` on ALL FOUR tenures.** Nothing in the exit
status separated *"the port went green"* from *"the port regressed"* from
*"unchanged"* — only the pinned shape did, and it caught **both directions
across consecutive tenures**: **MISS at 85489** (1 error, arity), **MATCH at
69357** (built, 12 s, 0 errors).

> **When the ambient verdict is CONSTANT, every bit of information is in the
> pin.**

The O1 landing gave this section its first **positive** demonstration; this is
the first where the same pin **convicted and then cleared the same artifact
across successive runs**. **A guard that fires in only one direction is half a
guard**, and the baseline being `SubtypingPort` built/errors rather than the
tenure's exit code is the point: **the exit code was constant across every
outcome the guard exists to distinguish.**

**(2) §8 item 11 — THE BRIDGE IS PAID, and the correction's SHAPE is the law.**
`rt_bridge` pays it once and `rt_sub_app` **collapsed to `exact
List.rel_append h1 h2`** — a hand-rolled replacement would have been maintained
forever to reach the same line, which confirms the ordering I landed in `-44`
(price the bridge first).

**The new half is that the compiler REFINED the claim rather than refuting
it.**

> **"Does not apply at all" is a claim about a LIBRARY, and only WRITING THE
> BRIDGE measures how much weaker the true statement is.**

The finding was **right about the lemmas and wrong about the library**, and
those are different claims with different evidence: *these lemmas do not fire*
is settled by a red; *this library cannot reach this model* is settled only by
**attempting the crossing** — §9.7's rule for negatives is what separates them.

**So the correction is recorded as a REFINEMENT, with both halves, not as an
erratum.** An erratum deletes the finding and takes its correct half with it; a
refinement keeps *the lemmas do not apply pointwise* — still true, still useful,
still the reason the bridge is needed — and adds the quantifier the evidence
supported.

**(3) THE PRIOR-ENTRY HYGIENE IS THE SAME DISCIPLINE POINTED BACKWARD.** The
lane flagged its own overstatement **unprompted** and **preserved the correct
half**; compare the Lean tier's form — *entries 17 and 19 predate the finding
and should be read with the qualifier attached, rather than rewriting them.*

> **A qualifier may attach to a RANGE of dated entries.**

The annotation norm at a **second scale**: one entry takes an annotation, a
*range* takes a **standing qualifier** — and both beat the edit that would make
a ledger read as though the lane had never been wrong.

**(4) §1.2 — THE ROSTER FACT WAS A DEFECT IN THIS DOCUMENT'S TABLE.** The analog
tier (Spice/Circuit, §6.1) is **staffed as of today**, dormant since July, **22
`sorry`s**. The registry's status column said **active** — **true of the code
and false of the staffing.**

> **A tier can be ACTIVE IN THE TREE and DEAD IN THE ROSTER.**

**Both halves were honest readings of one word, which is the whole defect**: a
reader planning work needs *"is anyone on this?"*, a reader pricing a dependency
needs *"does it build?"*, and **the column answered whichever question the
reader brought.** The row now carries both, and the rule generalizes:

> **A status column NAMES WHAT IT MEASURES. In-tree and rostered are separate
> facts; a single word that can be true of either will be read as both.**

The unit family arriving in a table's **vocabulary** rather than in a count —
with the same tell: **the word looked like a property of the tier, and it was a
property of a question.**

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-179 … MEAS-183**.

## 2026-08-24-architecture-55 — A verdict certifies a tree, never a title

Seven from the Ada successor's reconstruction (adoption redo `342a1f5`, tenure
queued, merge pending green). **All seven landed.**

**(1) §5.4a-i — THE WRONG-TREE GREEN, and it completes a ladder this section
already had two rungs of.** A prior *"adoption tenure"* was **GREEN** — true
lock line, clean gates, exit 0 — certifying a tree (`ea56aea`, identical to the
ticket commit's tree) containing **only backlog-doc changes.** The adoption had
**never been implemented**; `Value.lean` still carried **all 8 `ADOPT`
markers.**

> **The green was TRUE and answered a different question than the ticket asked.**

> **A verdict certifies a TREE, never a TITLE.**

**Landed as the exact DUAL of the enqueue-tree stamp**, which is the framing
that makes both usable: **the stamp stops the tree changing AFTER enqueue;
nothing checked that the tree ever CONTAINED the work the title promises.** One
guards the interval, the other guards the premise, and **a tenure can satisfy
the first perfectly while failing the second completely** — this one did.

> **ANNOTATION (Ada, `44ae259`; entry NOT rewritten).** The ranking below is
> **AMENDED, not withdrawn**: duration drops to **third** and **`Built` vs
> `Replayed`** becomes the second witness. The reasoning here was right that
> duration is not primary and right about why; what it got wrong was treating
> duration as the best available *second* witness when a stronger one was in the
> log all along. Carried forward in `2026-08-24-architecture-63`.

**And I kept the witness RANKING, because it is the transferable part**: tree
identity is **primary** (the verdict *is* about a tree, so it is the only
witness speaking in the verdict's own terms); duration is **corroborating**
(**4 seconds cannot be a Mathlib-rooted adoption**) and still second, because a
duration is a fact about *this run* while the claim is about *this tree*. **A
lane that leads with duration will one day meet a warm cache and conclude
nothing is wrong.** Tools-lane aid noted: a **diffstat-vs-master line in the
triad header** would have made the 4-second doc-only green self-evident.

**(2) §5.2 — A REFUSAL USED AS AN INSTRUMENT.** The census cannot see
`AssignStmt`'s target-child shape (libadalang's `CallExpr` covers calls **and**
indexed components), so inch 2 will **refuse every non-simple target** with
`RefusalCause.unsupported` citing ARM 5.2.

> **A refusal is a PENDING MEASUREMENT: honest, countable, and read off the
> MODEL by the next census.**

**The alternatives are both worse** — guessing the split puts an unmeasured
number in the plan, deferring waits on an instrument nobody is building. And it
**inverts the usual direction of evidence**: normally the instrument measures
the model; here **the model measures for the instrument**, which is available
whenever a model can *recognize* what it cannot *handle*.

**(3) §2.5 — A PARAGRAPH RANGE IS EDITION-RELATIVE.** Census pinned Ada 2022,
tier at 2012, and **5.2.1 sits inside "5.1–5.3"**.

> **A clause number RESOLVES; a RANGE enumerates — and a range is a claim about
> which clauses EXIST in an edition.**

Settled **without the 2012 RM**, by corpus: **zero `TargetName` nodes in 4 821
ACATS sources** (also zero `DeclExpr`/`ReduceAttributeRef`/`Parallel*`). **The
corpus decided an edition question the missing document could not** — recorded
as a **method**, since the obvious moves are to defer or to assume continuity,
and assuming continuity is the motivated error (it is the answer that lets the
work proceed). **With its limit stated**: this settles **presence**, never
**semantics** — stretch it further and a missing document has been swapped for
an argument from silence.

**(4) §5.4b — PARTITION INSTRUMENTS BY CORPUS DEPENDENCE, measured under a real
purge.** The scratchpad purge took ACATS, the ARM texts and adatools; **every
number was re-derived from git-tracked, content-pinned census JSONs.** **4 of 5
instruments self-test PASS with no corpus**; the one that needs it **refuses
loudly with the acquisition path.**

**Both halves are required and are usually confused**: an instrument that could
run corpus-free but reads the corpus anyway turns an outage into a tree-wide
red; one that needs it and merely **skips** turns an outage into **silence**
(MEAS-9). **The purge is the test that separates them**, and this is the first
time this tree has had one run across a full instrument set.

**(5) §5.2 — TWO TIERS CHOSE THE SAME `π` INDEPENDENTLY, WITH OPPOSITE
NARROWING.** Go and Ada each instantiated the payload as **a citation into their
own standard** (`SpecRef` / `ArmRef`), and they **diverge on the class set**: Go
narrows and excludes `undefined`; Ada does not, because its `undefined` bucket
is a real product — the ARM's **bounded errors**.

> **Convergence on the PARAMETER plus divergence on the INSTANTIATION is exactly
> what a correct parameterization looks like.**

Had both narrowed the same way, the honest reading would be that the family had
guessed a **default** rather than found a **parameter**.

**(6) §5.4b — A GATE CAN BE POINTED BY ACCIDENT, which the four-state ladder
does not distinguish.** `LeanModels.lean` does not import `LeanModels.Ada`; the
tier reaches the default build **only through the `Examples` glob**.

> **A gate reached by ACCIDENT retires when somebody tidies an unrelated file.**

*A dependency satisfied by a neighbour is not a dependency met*, pointed at a
gate's **reachability** — and **worse in one specific way**: the neighbour case
fails loudly elsewhere, this one fails **silently here**, because deleting the
last example that imports the tier changes **nothing in the gate set**. So the
enumeration owes one more question after *what is it pointed at*: **WHAT MAKES
IT RUN?** Fix with the Ada lane; the shape is the register's.

**(7) §9.0b — THE `+0` DISCLOSED IN THE PLAN, second instance and the lane cited
Go's precedent itself.** Inch 2 moves ACATS coverage by exactly 0 and **says so
in the plan**: *it must not be sold as a coverage rung.*

**A `+0` disclosed in the plan is a different artifact from a `+0` explained in
the retrospective** — the first is a lane pricing its own inch honestly **while
it could still have chosen a different one**. **Both are correct and only the
first is a control**, and it is the cheapest one available: at plan time the
sentence costs nothing, afterwards it costs the appearance of progress.

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-184 … MEAS-191, STMT-119**.

## 2026-08-24-architecture-56 — The guard is inside the thing it cannot see; and a count in prose without its unit

Seven from the analog tier's founding census (branch `analog-m0-census` at
`491b944`, **uncompiled and stated as such**; `docs/backlog/analog.md` founds
the lane — **17 lanes now**). **Verified against the branch and the tree, not
the dispatch summary** — and one item was a defect in this document.

**(1) §5.3 — THE STRUCTURAL APEX OF THE VACUITY FAMILY.** Non-vacuity is **a
chain of two links**: an inhabited **world** set, then an inhabited **behavior**
set. `RealizableUnder` exists to stop empty behavior sets and **is itself
guarded by `allowed world`** — so **an unsatisfiable `allowed` discharges all
three obligations at once** and `#assurance_report` prints a real-looking
result. **24 assurance cases, 0 carrying a world witness.**

> **The guard's blind spot is POSITIONAL, not an oversight — it cannot see the
> outer link BECAUSE IT IS ITSELF INSIDE IT.**

**Why this is the apex and not another instance**: every other vacuity here is a
**missing check**. This one is a check **added for the right reason, correctly
implemented, and structurally incapable of catching the case that subsumes
it** — no care inside the guard reaches it. General form: **enumerate the LINKS
of a non-vacuity chain and ask, per link, which guard is OUTSIDE it.**

**(2) §9.0 — A COVERAGE BOUND HAS A DIRECTION, and must state it.** Go's
syntactic measure **over**-counts; the analog grounding grep **under**-counts
(`dram_bank_256x32` reads ungrounded while grounded under another spelling, and
the instrument flags it **`NO-GROUNDING-WITNESS` in its own output**).
**"Syntactic ⇒ upper bound" is not general** — the direction depends on whether
the measure can produce false positives or false negatives, **and a measure can
do either.** So a coverage number carries **three** things that fail
independently: denominator, numerator, and **sign**. *Two lanes quoting bounds
in opposite directions and neither saying so is how a cross-tier table becomes
unreadable.* And the instrument naming its own uncertain rows is the honest form
of a lower bound: **a caveat is prose; a flagged row is data.**

**(3) §3.2 — THE DEFECT WAS MINE, AND IT IS FIXED.** *"Spice 11, Circuit 11,
Verilog-A 1"* carried its unit in the **paragraph** and not the **sentence**,
and a dispatch quoting the sentence sent a lane hunting **eleven `sorry`s that
do not exist.** Re-verified here: Mathlib-importing files are **11 / 11 / 1**,
and the analog tier has **zero `sorry`, zero `axiom`/`opaque`/`partial`/
`native_decide`** — the only `sorry` token is `Surface.lean`'s **guard against**
one.

> **A count in prose without its unit becomes whichever count the reader
> needs.**

*A status column names what it measures* **one level up — and worse there,
because a sentence TRAVELS**: a table row is read in its table; a number in
prose is **quoted**, and the quotation leaves the unit behind. And **note the
direction of the misreading**: `11` read as *incomplete work* rather than
*dependency* — **a reader supplies the unit that makes the number actionable**,
so an unlabelled count is read as whatever would give the reader something to
do.

**(4) §5.4a — A CONCESSIVE-PROSE GREP FINDS PROVED THEOREMS AS READILY AS OPEN
ONES.** `Spice/DramDifferentialSenseUnbalanced.lean:1899` reads as an open
obligation and is **a docstring on a theorem proved two lines below** (verified).
**An open-obligation census reads the DECLARATION, not the commentary** —
`sorry`, `axiom`, `partial`, an admitted constant — because those are states the
elaborator knows about. **Concessive prose is a writing style, and the tiers
that write the most careful docstrings score worst on it**: the ranking exactly
inverted.

**(5) §5.3 — PRIORITY OF PRACTICE, cited.** The July tier **implemented this
ruling in Lean before the family minted it as prose in August**: `AssuranceCase`
structurally refuses assembly from unrelated theorem names (`Circuit/Surface.lean`,
verified on master); `SourceBinding`'s equalities block circuit substitution (on
the branch). **`Surface.lean` is now cited as prior art where §5.3 is stated** —
the convergence standard arriving **from code to prose** rather than the other
way round.

**(6) §7.1a — THE LOUDNESS GUARD GAINS A DEPLOYMENT CLAUSE.** Re-measured here:
**1 of 163 `LeanModels` files, 0 of 188 under `Examples`.**

> **A loudness guard adopted as law but present in 1 of 163 files is a DECLARED
> gate that is not yet POINTED, and the register records the ladder position
> ALONGSIDE the law.**

Because **a law without its deployment number reads as a property of the
tree** — *the rule is adopted* and *the tree obeys it* are different claims.
Three-part adoption landed: **required for new files immediately; retrofit
per-tier riding natural touches (§9.2); explicit binders first where elaboration
depends on auto-bound implicits.** The third has teeth, and `Surface.lean` is
the exhibit — it **hard-codes arity 10 and position 4**, so a flip there is **a
semantic change, not a hygiene change**: *a setting that changes how many
binders a declaration has is not a style setting in any file that COUNTS
binders.*

**(7) §9.0 — AN UNCLOSABLE OBLIGATION IS ADMITTED IN THE ARTIFACT'S OWN
OUTPUT.** `#assurance_report` prints **`model validity: MISSING`, 12 sites**.

> **A standing disclosure lives where the CLAIM is served, not where the apology
> is filed.**

**The two placements have different half-lives**: a caveat document is read once
by whoever goes looking for caveats; the artifact's output is read **every time
the claim is used** — and an architecturally-unclosable gap is precisely the
kind that outlives everyone who remembers it. It does not discharge the
obligation; **it prevents the obligation from being forgotten while it stays
open**, the same service *named, not counted* performs for a denominator.

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-192 … MEAS-197**.

## 2026-08-24-architecture-57 — Completeness is counted per orientation; and a pin move declared in advance

Four from Wasm O2/O4 (`6bd3ca1`, verified on master; **§9.0 = 4/5**).

**(1) §9.0 — ORIENTATION IS A COUNTING UNIT INSIDE THE NUMERATOR.** The two
duals consumed **opposite orientations of the same split lemma**.

> **A lane that had proved only one would be exactly HALF DONE AND NOT KNOW
> IT** — the name is in the numerator either way.

> **When a lemma family has an orientation, completeness is counted PER
> ORIENTATION, not per lemma NAME.**

**The unit family arriving inside a coverage count, and the hardest instance to
notice, because the artifact is genuinely there**: the lemma exists, elaborates,
is cited, closes its goal. Only the **dual consumer** reveals the name covered
half a fact — and the two-orientations census reading, **taken before the
work**, is why the second orientation was not discovered by a lane finding its
proof does not apply.

**(2) §5.4b — THE DRIFT FAMILY'S MISSING CASE: the guarded artifact
LEGITIMATELY changing.** O5's prerequisite `ais_empty_typing` **is one of the
six broken baseline declarations** (errors 371 and 380 inside its 295–412 span),
so repairing it **takes the pin 6 → 4** — and the lane **declared the change
before writing the fix.**

> **A pin move is DRIFT or a DELIBERATE CHANGE, and the only thing that
> distinguishes them is PRIOR DECLARATION plus NAMED DEPARTURES.**

The section had *never fires*, *always fires*, and *re-baseline reports what did
not move* — **all three assume the artifact should not move.** This is the case
where **it should**, and **after the fact a legitimate repair and a silent
regression produce the same diff.** Declaration converts one into the other and
is cheap **only before**: afterwards *"that change was intended"* is
unfalsifiable and arrives from the one person with a motive.

**(3) §9.0b — THE LAST RUNG RE-PRICED IN ADVANCE.** O5 is **not** the six-line
job O2/O4 were: **~118 lines of prerequisite that cannot be copied** (no working
Lean original exists) ahead of a **183-line induction**.

> **The last rung is the tall one, and the census says so IN ADVANCE.**

**Same control as the `+0`-in-plan, opposite sign** — one discloses that a rung
buys less than its position suggests, the other that one costs more. Both are
worth nothing afterwards, and **the tell that a chain has not been censused is
that its rungs are all the same size.**

**(4) §5.6 — THE HIERARCHY RANKS CLAIMS, NOT CLAIMANTS.** The coordinator raised
*"these errors are your new proofs"* from a log tail; the lane **refuted it by
measurement** — byte-for-byte baseline reproduction at the same six lines,
`grep` for `SubtypingPort` errors **= 0** — **not by assurance**, and **quoted
its instrument.**

> **A coordinator's hypothesis enters at the same rung as a lane's self-report,
> and leaves by the same door.**

**Recorded because the asymmetry is the natural failure**: a hypothesis from the
coordinating role arrives with standing, and the cheap response is agreement —
which would have written a false statement into the register with **more**
authority than a lane's own report carries.

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-198 … MEAS-201**.

## 2026-08-24-architecture-58 — The guard built to pin the tree points at the index

One from the Wasm lane, checking whether it could safely edit before its tenure.
**Verified against the tool, not the dispatch**: `tools/triad.sh:1181-1183`,
`tree_stamp()` is `git -C "$CLONE" write-tree`.

**THE DEFECT.** **`git write-tree` hashes the INDEX. `lake` builds the WORKING
TREE.**

> **An uncommitted, unstaged edit between enqueue and acquire is INVISIBLE to
> A6's enforcement — and the green would certify a tree the gate never saw.**

**(1) IT IS THE WRONG-TREE FAMILY ARRIVING INSIDE THE GUARD BUILT TO PREVENT
IT.** The enqueue stamp exists **precisely** to pin the certified tree, and it
points at **the one object `lean` does not read.** §5.4b's pointer question —
*what is this pointed AT?* — aimed at a **guard** rather than a **gate**, with
the sharpening the analog apex supplied: **correctly motivated, correctly
implemented, against the wrong object.** Nothing is a slip; `write-tree` does
exactly what it says, and what it says is not what the build reads.

**Read with `-55`, the pair is the whole ladder**: that landing showed a green
certifying **a tree the ticket's title did not describe**; this one shows the
guard that pins the tree **pinning a different tree than the one built**. *The
stamp and the title were both checked against something other than the artifact.*

**(2) HOW IT WAS FOUND IS ITS OWN LAW.** The lane **almost deferred a safe
edit** for fear of the stamp, then **read the implementation instead of obeying
the reputation** — and found **the fear unfounded and the guard hollow in the
same read.**

> **A guard's REPUTATION and its MECHANISM drift apart silently. The lane that
> reads the mechanism inherits BOTH facts.**

**My addition: both directions cost something, and different people pay.** An
**over-estimated** guard taxes every lane that obeys it — here, a deferred edit
for a rule that did not apply. An **under-estimated** one taxes whoever
eventually trusts a green it did not earn. **The same read settles both**, which
is the practical argument for reading a guard before working around it: the cost
is bounded and it is the only move that can return **either** answer.

**(3) THE DISCLOSURE MADE IT A FINDING RATHER THAN AN EXPLOIT** — *"mine is
comments-only and I'm declaring it rather than relying on the hole."*

> **The same hole, used silently, is indistinguishable from the Ada incident.
> Declared, it is a tool defect with a named fix.**

**The drift family's declaration rule one level up — at PROTOCOL COMPLIANCE
rather than at an artifact.** There, prior declaration separates a legitimate
baseline change from a silent regression; here it separates **a lane working
within a known-imperfect protocol** from **a lane quietly relying on the
imperfection** — and **after the fact the two produce the same tenure.**
Declaration is cheap only before, and it is the entire difference between a hole
that gets fixed and a hole that gets used.

**Fix with the tools lane** (working-tree hash via temp index, both ends,
old-stamp tolerance for the eight live tickets). **Until it lands the rule
stands as written, and a lane that must edit says so at enqueue.**

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-202, OPS-78, OPS-79**.

## 2026-08-24-architecture-59 — Re-pointing a guard is not monotone tightening

Six from QoL's four-item landing (`22ed755`, merged `b98b4d0`) plus one sunset.
**Verified against the tree**: `STAMP_VERSION="v2"` and the `GIT_INDEX_FILE`
temp index at `tools/triad.sh:1192-1208`.

**(0) THE SUNSET.** Yesterday's interim rule (OPS-79) applied *until the fix
lands*. **It has landed** — working-tree hash at both ends, `add -A` so a new
untracked `.lean` cannot slip in, `.gitignore` honoured, **0.31 s vs 0.015 s**,
twice per tenure. **OPS-79 now applies only to tenures whose tickets carry v1
stamps**, and the law-index row says so rather than being deleted.

**(1) §7.2 — THE RE-POINTING FLIPPED AN OLD VERDICT, DELIBERATELY.** The old
stamp **refused an index-only edit**; the new one **accepts** it — *content
staged but absent from the working tree will never be elaborated, so it is not
part of what the tenure certifies.* **The old refusal was a false alarm in the
other direction.**

> **Re-pointing a guard is NOT monotone tightening. A guard aimed at the right
> object flips some of its old verdicts, and each flip owes its reasoning WHERE
> THE CHECK LIVES.**

**The necessary companion to MEAS-202**, and I said why it needs saying:
*"we fixed the guard"* invites the reading that everything it used to reject it
still rejects, **plus more**. A re-aimed guard is **a different guard**, and a
lane meeting the newly-accepted case a year from now will ask whether it was
considered — the answer belongs in the test comment, **not in a landing message
nobody greps.**

**(2) §7.2 — THE SECOND CONSUMER WAS FOUND BY THE FIX, NOT BY A SECOND
INCIDENT.** `record_green` also called `write-tree`, so a green taken with an
unstaged edit **recorded the index's hash and could be judged CITABLE while the
elaborated content was something else.**

> **When a defect is found in a PRIMITIVE, census its other callers before
> closing.**

**And the exposure audit is the part worth copying**: all merged greens were
porcelain-clean, and **clean ⇒ index == working tree** — *the defect was live,
and the population that could have been affected was measured rather than
assumed.* MEAS-28 read backwards: **sharing a primitive is what made one fix
sufficient, and what made one defect reach two guards.**

**(3) §7.2 — MY OWN RECOMMENDATION LANDED WITH A DEVIATION, and the deviation
was right.** I proposed a diffstat-vs-master line in `-55`. **"0 `.lean` files"
is not docs-only**: `lakefile.toml`, `lean-toolchain` and `lake-manifest.json`
carry no `.lean` and **invalidate the whole graph** — printing `DOCS-ONLY` for
them would **reproduce the tree/label mismatch the line exists to expose.**

> **Ask the ORACLE that already answers the question. A label re-derived inline
> is a SECOND classifier, and it will be weaker than the first.**

**A line added to catch a mismatch that introduces a mismatch of its own** is
the failure this section keeps finding, and the fix is §5.4a's: one reader, and
it is the one that already exists (`classify_path`, printing
`NOT docs-only (lakefile.toml)`).

**(4) §7.2 — THE ABSENCE TAXONOMY BELONGS AT THE PRINT STATEMENT.** Three
members — `n/a-foreign-tree` (refused before trying), `n/a-no-merge-target`,
`n/a-unrelated-histories` — against **`0 files`**, which **is** a measurement.

**Every earlier member of this family was an absence INSIDE an instrument**; this
one is **at the boundary where the instrument speaks**, and that is the last
place the distinction survives: **once `0` is printed, no reader can recover
whether the question was answered or declined.**

**(5) §9.5 — AN ID IS ONE TOKEN, which is what makes `--strict` adoptable.**
`G1 — t` yields `G1`: a real entry under an older scheme (**warn**).
`INBOUND FROM THE SOFTFLOAT LANE — …` yields `INBOUND`, five tokens where one
belongs (**junk; `--strict` exit 3**).

> **A migration-tolerant gate distinguishes OLD-VALID from NEVER-VALID, or
> `--strict` can never be adopted.**

**The arithmetic, not the taste**: a gate treating every pre-scheme heading as
junk fails on **history**, so it could only be switched on after a tree-wide
rewrite — the big-bang §9.2 forbids. With the distinction, **the strict mode's
failure set is exactly the set somebody can fix today.** The guard was
**extended, not duplicated**, and the undated headings were being counted
**inside the generated file, where the lane that wrote the heading never
looks** — *a count that lands only in an artifact its subject does not read is a
count nobody acts on.* Six of the eight belong to other lanes, so `--strict`
sits at **declared** (§5.4b) **on purpose, with the reason recorded rather than
the adoption forced.**

**(6) §5.4b — A THIRD WAY A SIGNAL GOES DEAD.** The tenure-class heuristic
hard-coded `{github,origin}/master`, so a fork whose default branch is named
otherwise **fell back to a full tenure — conservatively, therefore silently.**

> **A heuristic that fails conservatively is exactly how a heuristic stays
> broken: a full tenure every time and no one the wiser.**

> **A failure mode that only ever costs TIME has NO CONSTITUENCY FOR FIXING
> IT** — nobody is wrong, nothing is red, and the bill is paid in minutes spread
> across everyone.

**This completes the stuck-channel family**: a gate that never fires, a guard
that always fires, and now **a heuristic that always answers the safe way** —
all three carrying zero information, and this one **hardest to retire because
its symptom is indistinguishable from correct caution.** The fix was to **ask
the remote which branch is its HEAD** rather than guess better: *a heuristic
with a fallback nobody can see should be replaced by a question somebody can
answer.*

**(7) AND THE NEW GUARD CONVICTED THIS DOCUMENT WITHIN THE HOUR — one of the
seven malformed headings is THIS LANE'S.** `docs/backlog/wasm.md:634` is my own
INBOUND, and it is malformed **because §9.5a tells filers to write it that
way**: the heading starts with `INBOUND`, so the generator invents `INBOUND` as
the id — *five tokens where one belongs*, the exact case the law I had just
landed calls junk.

**The two rules are both load-bearing and genuinely conflict**: the index's
INBOUND **class** is derived from that first token, so §9.5a's spelling is what
makes the rendering work, while the id law is what makes `--strict` adoptable.
**Recommended resolution recorded, not taken**: the id goes first, `INBOUND`
moves into the title, and the generator classes on the **title prefix**.
**Routed to the tools lane** — the generator is theirs, and re-spelling six
other lanes' headings to match a shape I chose is the cross-lane edit §9.5a
exists to prevent.

> **A CONVENTION IN A CHARTER CAN BE A DEFECT IN A TOOL.**

**§9.5a was written for readers, and the generator reads it too** — a rule about
how humans write headings became **an input to a program**, and nobody
re-checked it against the program's grammar. Meanwhile the existing headings sit
at **OLD-VALID — warn, never fail**, which is item (5)'s migration vocabulary
doing its job **on this document's own convention, one landing after it was
written.**

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-203 … MEAS-209**, and **OPS-79 sunset**.

## 2026-08-24-architecture-60 — The merge fixes what is false; only the owner sees what is now redundant

A merge, a ruling, and a corrected census. Merged QoL's `qol-model-matches-code`
@ `5fa7492` into master and resolved the conflict in this lane's document.

**THE MERGE.** QoL reconciled four present-tense claims that its own fix had
falsified — §5.4a-i (theirs), §7.2's registration and A6 description (mine), and
`OPS-78`. **The analysis was preserved intact; only tense and status moved**,
plus a `RESOLVED` paragraph carrying the two consequences a future reader needs.
**Verified for sense, not just cleanliness** — and that mattered:

* **`OPS-78` resolved by COMBINING, nothing dropped from either side.** QoL's
  shelf-life-free statement — *a guard must hash the object the BUILD reads,
  never the one beside it* — **subsumes** my symptom line, which survives inside
  its parenthetical along with the fix sha. **`OPS-79` is mine and untouched**,
  sunset intact.
* **AND THE UNION SAID THE FIX TWICE.** QoL's `RESOLVED (22ed755)` paragraph
  landed forty lines above my *"the fix has landed"* paragraph from `-59`.
  **Neither edit was wrong**; the duplication existed **only in the union**.
  Consolidated into one `RESOLVED` paragraph carrying **both** halves — QoL's
  temp-index mechanism, index-only acceptance and accept-and-log versioning,
  plus my verification citation, the 0.31 s/0.015 s cost and the OPS-79 sunset.
* One merge artifact fixed: a mid-sentence line break left in §5.4a-i.

**(1) THE RECONCILIATION REGIME — RULED, since it touches this lane's ownership
norm.** The question was whether the fixing lane reconciles at the merge or
whether reconciliation is INBOUND like everything else.

> **It SPLITS, and the test is one question: does the edit change what the
> document CLAIMS, or only WHEN it claims it?**

**TENSE AND STATUS reconcile at the merge, by the lane that landed the fix** —
*"the stamp IS `git write-tree`"* goes false the moment the fix lands, **the
fixing lane is the only party who knows that**, an INBOUND would leave the
charter **false for a round-trip**, and model-matches-code makes divergence a
**blocker**, not a queue item. **REASONING, LAWS AND DATED ENTRIES stay
INBOUND** — a lane reconciling a status may not restate a law, re-scope a
finding, or delete an analysis on the way past.

**Two conditions make the first half safe and QoL met both**: preserve the
reasoning intact, and say in the landing exactly what changed and why.

**And the owner still audits — the half that cannot be delegated.** The very
first exercise of this ruling produced a **correct reconciliation that left the
section saying the same thing twice.**

> **Reconciliation-by-edit is right for TENSE and owes an owner's pass for
> COHERENCE. The merge fixes what is FALSE; only the owner sees what is now
> REDUNDANT.**

**(2) THE CENSUS MOVED, AND THE COMPOSITION IS THE FINDING.** Re-measured here:
**7 malformed, not 6** — and **one of them is not an entry at all.**
`docs/backlog/go.md:11` is `## SPEC COVERAGE — the completion metric`, **a
standing section header** carrying §9.0's own required number; the other six are
INBOUND entries.

> **Two remedies for one symptom, distinguished by what the heading IS**: an
> **entry** missing an id gets **an id**; a **section header** gets **demoted to
> `###`** — never an invented id, **which would put it in the index as an entry
> that does not exist.**

**The unit family at the heading level.** The guard reports a **syntactic**
class and **two semantic kinds sit inside it** — *the check was right; the unit
underneath it was two things.* **And it is why the guard warns rather than
auto-fixing**: a gate repairing its own findings would have written an id onto
that header, **the flattering repair applied to the one case it cannot
classify.**

> **A guard that can NAME a defect it cannot CLASSIFY must hand it to someone
> who can.**

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-210 … MEAS-213**.

## 2026-08-24-architecture-61 — A declared divergence is a debt, not a verdict

Eight from two sources — R-track rung 1 (chain doc `68327fb`; `flagship.lean`
ticketed) and pyc inch 2 (branch `pyc-del` @ `485e7a3`, ticketed, pending
green). **The ruling request is answered first, because it was the one item that
could not be landed as an observation.**

**(8) THE RULING — §5.0a IS NEW: DECLARED DIVERGENCES.** CPython's dict-iterator
error state is **sticky**; the model's is **not** — inherited and named from
`enumDict`, `§pycomplete-14`. The lane gave it **no witness row** because a row
would be a **DIVERGE**, so it lived only in prose — and *never-hide-errors says
prose is not a ledger.* **Both halves were right**, which is why it needed a
ruling.

**The resolution separates two things the word was carrying.** `DIVERGE` is a
**verdict about a run**: the model answered, the answer was wrong, and **nobody
decided that in advance.** What the lane holds is a **decision already taken,
with a name and an owner.**

> **A divergence the tier has DECIDED to carry is not a verdict. It is a DEBT —
> registered, aged and gated, never narrated.**

**The invariant is untouched: `DIVERGE` stays zero, always.** Admitting these
would make the one number that means something mean nothing. They go to a
**machine-readable register beside the refusal whitelist**, six fields — SITE,
ORACLE behaviour, MODEL behaviour, **INHERITED FROM** (blank = originated, a
heavier claim), **DECLARED** (so it can be aged), **RETIREMENT CONDITION**
(*"when someone models it"* is not one, per §9's WAITING rule).

**Gated in BOTH directions**, which is what makes it a ledger: *is the model
still divergent here* (a silently **fixed** divergence leaves a stale
declaration — a false claim that reads as diligence) and *is it still the one
described* (a silently **widened** one is the same row describing a bigger
fact — worse, and invisible). **Counted in §9.0 as a THIRD quantity**:
`declared-divergences: N` **beside** the coverage number, because folding it
into the numerator would claim the behaviour and into the denominator would
claim the tier never reached it — **both false**. **Aging hooks §9.7**: a row
past several audits with an unmoved retirement condition is a finding, since *a
debt nobody has priced in months is a debt nobody is going to pay.*

**Why not the alternatives**, stated so this is not re-litigated: a *whitelist*
puts the row inside the scoreboard's vocabulary and invites *"some DIVERGEs are
fine"* — and **a whitelist is a permission, not a debt: it does not age.** Prose
in the tier doc is **what this ruling replaces.**

**(1) §9.0 — THE TYPED-TARGET LAW GAINS ITS ECONOMICS.** The campaign's namesake
theorem cost **one scratch elaboration** — *the rung listed first, blocking the
most WAITING triggers, was the cheapest item on the board*, and had never been
anyone's task because every archived ladder ends *"…and then
`bound_refines_fuelModel` assembles."*

> **A goal theorem that only ever appears as the LAST LINE OF PLANS will never
> be written. Type the target before the path to it.**

Three properties, and the third is why it outranks a scheduling note: the
statement is **cheap**, it makes **every progress claim falsifiable**, and **it
is the only artifact that can tell a lane it has been serving something it never
checked.** My addition: **a path is measured against its target**, so a chain
with no typed target measures its rungs **against each other** — internally
consistent, locally green, unfalsifiable.

**(2) §9.0 — ASSEMBLY-DIFFICULTY ZERO AS A DESIGN GOAL.** Strong induction
discharged **once**, side conditions all `omega`'s, **exactly two named
obligations with no proof shape**. Stated as a goal rather than an outcome
because **difficulty parked in the assembly is paid again by every re-founding
and is invisible in the obligation list**: *a hard assembly is an obligation
list that lies about its own length.*

**(3) §5.4a-i — THE AFFIRMATIVE USE, third instance.** The lane **committed the
index rather than the working tree**, because post-certification verdict prose
would have changed the certified tree. **The negative reading catches a green
that answered a different question; the affirmative one tells a lane which
honest commit PRESERVES the certification** — decline the rebase (SV), decline
the fold-in (R-track), commit the index. Three lanes, independently: §9.3's
convergence standard applied to a law's **use**.

**(4) §5.4a — THE INGESTION-REWRITE AVAILABILITY RULE, STATED FROM A ZERO.**
`iter(d)` extracts as a plain `Call` with **zero extractor sites**.

> **An ingestion rewrite is available exactly when the construct's meaning is
> decided by SYNTAX.**

**A rule stated from a zero beats the same rule stated from a success**: the
working rewrite told the lane it was available *here*; the zero tells it **what
property made it available there.** The previous inch's shape was never about
`ListComp` — **it was about syntax deciding meaning**, which nobody could know
while it kept working.

**(5) §5.4 — A CLOSED-LIST DOCSTRING IS A TIME BOMB.** `Expr.genAllocFree` named
*"a closed list of two"*; **`iter` is the third**, and without the fix ordinary
Python reports **`internal: heap well-formedness violation`** — the 2026-08-13
incident **replayed from a comment.**

> **A docstring that ENUMERATES is a census that no instrument re-runs.**

**The closed-list form is the aggravating factor, not the enumeration**: a
drifting list is a stale claim, but *"a closed list of two"* **licenses code to
assume completeness** — the reader who adds the third member is told, in the
file, that there is none. **The docstring did not merely go stale; it argued
against its own repair.** And it came back **through a comment**, because the
code was fixed and the sentence that would recreate it was not.

**(6) §5.4a — SAMPLING-POSITION BIAS.** The for-loop census **sampled one rule
from one cursor position**; the churn regime is **two CPython rules**, and the
refusal is honest to both.

> **A census sampling from ONE POSITION measures the rule that position is
> subject to, not the construct's rule.**

**The unit family with the SAMPLING FRAME as the unit** — every earlier member
had a wrong unit of counting; this one counts a correct unit **from a privileged
vantage**, and the number is right about what it saw. **The tell is a census
whose sites are all structurally alike**, which reads as a clean population.

**(7) §5.3 — THE DEEPEST ONE: A DIFFERENT HYPOTHESIS WITH THE SAME STATEMENT.**
`sbEvict_lit`'s ∃-quantified body **hid the previous inch's ingestion change
from the compiler**: zero theorems break, three prose sites stale, and the
`room` hypothesis **now prevents an unmodelled STATE CHANGE where it used to
prevent a REFUSAL.**

> **The statement is identical, the meaning moved, and no tool can see it.**

**Everything else in this section is visible to something** — a red, a census, a
diff, a verdict. **A premise whose purpose changed under a stable statement is
visible to nobody.** The lane asked what instrument could; **my answer: none, at
the statement level — and the rationale becomes checkable the moment it is
written as a claim with a witness.**

> **Drop the hypothesis, and a specific named thing must happen.** Write that
> thing down as a row, and the rationale is no longer prose.

**When the purpose moves, the row's SUBJECT changes and the row breaks even
though the theorem does not** — §5.3's *pair every "did not change" with a "did
happen"*, applied to a premise. **With the limit the lane itself named**:
witness pairs cover **behaviour**, and **an unwritten rationale stays
unfalsifiable no matter how good the instruments are.** The fix is not a better
tool; **it is a sentence that could be wrong.**

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-214 … MEAS-220, STMT-120 … STMT-122**.

## 2026-08-24-architecture-62 — The ruling met reality within the hour, and reality had four corrections

Five from the pyc lane's §5.0a implementation design, plus a compliance rider.
**STATE STAMP: the design is drafted off-repo (`scratchpad/pyc-inch3-handoff.md`)
and is NOT verifiable from this clone** — landed on its account, **conditional on
inch 3**, and **owed a re-read at that landing.**

**(1) §5.0a — THE `MODEL` FIELD IS A MEASUREMENT, NOT A READING, and this is the
hole in my own six-field spec.** The first row's MODEL field was **read from the
code, not run**, and the lane **flagged its own field as unverified.**

> **A debt row's `MODEL` field is a measurement. The row and its instrument land
> in ONE COMMIT — they land together, or the row is prose with a schema.**

**A register whose fields are read rather than run is the thing it was built to
replace.** The whole argument for §5.0a over prose was that prose cannot be
gated; **a row asserting *the model does X* on someone's reading has imported
prose into the schema and made it look like data.**

**(2) §5.0a — A DEBT WHOSE PROBE IS BLOCKED BY ANOTHER DEBT, resolved by
LAYERING.** Observing the stickiness in-tier needs `except RuntimeError:` — **a
whitelisted refusal**: *the tier's own refusal surface blocks the program-level
probe of its own divergence.* The probe moves to the **model level** (a Lean
`#guard` at the frame stepper; **the build is the gate, two-sided** — became-
sticky fails, any-other-move fails), leaving **one hole the build cannot see**:
the guard's deletion. **The harness checks the guard's PRESENCE**, and row and
guard are **deleted together or not at all.**

> **The BUILD gates the CONTENT; the HARNESS gates the EXISTENCE. Each layer's
> blind spot is the other's subject.**

**Generalized past this row**, because the property is not special: **a check
strong enough to verify content is usually blind to its own removal** — a
deleted check produces no output to be wrong. **Pair it with a cheaper check
that only asks whether it is still there.**

**(3) §5.0a — A RETIREMENT CONDITION IS A CONSTRAINT PAIR.** `except_builtin`
must **leave the whitelist first** (blocker **named**, not hand-waved), **and**
`exc_lab::gen_closes` must **stay MATCH** — *closing on exception is correct for
a user generator, so a fix that flips it has fixed the wrong thing.*

> **A retirement condition names what must CHANGE and what must NOT. The
> negative half is protection against the FLATTERING REPAIR.**

**Third appearance of that hazard** — §5.4b's paired guard, §5.2's two-sided
resolution gate, now a debt's retirement — and the pattern is stable: **wherever
a condition can be satisfied by moving the wrong thing, name the thing that must
hold still.** A condition with only a positive half is a target, and **a target
can always be hit from the wrong direction.**

**(4) §5.0a — INHERITED-FROM-SELF IS A REAL CASE.** Upstream is the same lane
(`enumDict` → `iterDict`, both pyc), and **the field still does its work because
ORIGIN ≠ SITE.**

> **With no other lane to wait on, the retirement condition gets STRONGER, not
> weaker.**

**A blank `INHERITED FROM` claims the divergence ORIGINATED here** — a heavier
claim and a false one — and it **loses the only pointer to the decision that
created it.** The temptation is real (*"it is us either way"*) and exactly
backwards: **self-inheritance removes the excuse, not the citation.**

**(5) §5.3 — THE MECHANISM, WHICH SHARPENS YESTERDAY'S ENTRY.** The `room`
hypothesis's failure mode changed **LOUD → QUIET**: an ∃-quantified body plus **a
proof that never opens it.**

> **The hypothesis is unchanged and still needed. What changed is that its
> VIOLATION IS NOW SILENT.**

**That is better than yesterday's *"the meaning moved"*.** The premise did not
move and the theorem did not move; **the OBSERVABILITY of the premise's failure
moved**, and observability is not a property any tool in this tree measures —
caught **only because the lane re-read its own prose.** The repair discharges my
own prescription exactly: dropping the hypothesis now produces **a wrong world,
with the exact heap inequality and two named witnesses** — *none of them prose.*

**AND A HYPOTHESIS TAXONOMY, because the retirement move differs by kind**:
**TIER** (widen the tier), **MODELLING** (model the thing), **BRIDGING** (prove
the relation). `room` was reclassified **tier → modelling**, and the
reclassification changed what closing it means:

> **The honest retirement is to MODEL THE EVICTION, not to widen the tier.**

**Misclassification licenses the wrong repair, and the wrong repair is the
cheaper one** — widening a tier is a declaration, modelling a behaviour is work.
**So the taxonomy is not bookkeeping: it stops a hypothesis being retired by
redefining the question**, and a row carrying a hypothesis names its **kind** for
the same reason a refusal names its **cause**: *the kind determines who owes the
work and what "done" looks like.*

**RIDER — §7.2, A COMPLIANCE INSTANCE SHOWING THE RULE OBEYED RATHER THAN
ENFORCED.** The lane read master through an **isolated bare mirror** rather than
fetching into its frozen worktree, so **the enqueue stamp never came near the
ticketed tree.**

> **Reading master and BEING on master are different needs.**

**The naive reading of §7.2 is that a lane holding a ticket is blind until it
releases.** It is not — **the constraint is on the WORKING TREE, not on the
lane's knowledge** — and **a lane that believes a protocol forbids more than it
does will either stall or break it.** `-58`'s reputation-versus-mechanism law
arriving as a **success**: *the lane that reads the mechanism finds the room the
reputation denied.*

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-221 … MEAS-225, STMT-123, STMT-124**.

## 2026-08-24-architecture-63 — Duration is a corroborator, not the witness

Eight from two merged sources — Ada's adoption green (`44ae259`, **fifth tier on
Core**; verified here: `LeanModels/Ada/` now imports Core in 1 file, was 0) and
Go's §G23 (`9a6d6ad`, sha filled at `6c7a2b3`).

**(1) §5.4a-i — MY WITNESS RANKING IS AMENDED, and the lane found it by applying
this section's forensics to ITS OWN HONEST BUILD.** The predecessor's dishonest
**4 s** and Ada's honest **2 s** *look alike in the summary and opposite in the
full log.*

> **Duration is a CORROBORATOR, not the witness.**
> **`Built` vs `Replayed` is the primary witness that a module ELABORATED — a
> fact the summary line does not carry.**

**Ruled order: TREE IDENTITY → `Built`/`Replayed` → CLOCK.** Recorded as an
**amendment, not an erratum** (MEAS-181, my own law): the original was **right
that duration is not primary and right about why**; what it got wrong was
**treating duration as the best available SECOND witness** when a stronger one
sat in the log the whole time. **Both halves stand**, and `-55` is annotated
rather than rewritten.

**(4) AND THE SECOND WITNESS MUST BE READ FROM THE RIGHT PHASE.** Go's triad log
carried **330 `Replayed` lines — from the GATE phase's runner, not the build**;
the build's own were **30 `Built` / 2 `Replayed`, all eleven tier modules
`Built`.**

> **A witness is a TOKEN PLUS THE PHASE it was read from. A log is not a bag of
> lines.**

**The unit family arriving inside a log**: `Replayed` is a correct token counted
from the wrong region, **and the wrong region is the larger one** — so the
mistake is easy *and* flattering-in-reverse, since it makes an honest build look
replayed. **A grep over a whole log has already discarded half the witness.**

**(2) §5.4a-i — SEPARATE SHAS, DECLARED BEFORE THE MERGE, unprompted.** The lane
pre-declared *"you are merging the gated Lean landing, not a docs commit bundled
into it"* — **the certified-tree boundary at MERGE granularity.** A bundled
merge is **the wrong-tree failure with the evidence pre-mixed**: afterwards *"the
green covers this"* names a commit containing both the gated tree and whatever
rode along, and **no reader can separate them from the merge alone.** Fourth
affirmative use of tree-not-title.

**(3) §5.6 — A COMPANION METHOD, second instance, now with its own name: ASK
WHAT THE WRONG MODEL WOULD *PERMIT*.** A `GoVal.tupleV` would **accept programs
`gc` rejects** — *"assignment mismatch: 1 variable but … returns 2 values"*.
**Multi-valuedness is a property of the CALL SITE, never of a value.**

> **To choose between two model shapes, ask which one ACCEPTS a program the
> oracle REJECTS.**

**It is the acceptance hierarchy's dual and it applies EARLIER** — the hierarchy
needs a candidate row and a run; this is answerable **from the shape alone**.
And the reason it earns a row: **over-permissiveness is what a differential
corpus is worst at finding**, because a corpus is made of **valid** programs, so
**a model that accepts too much passes every one of them.** Nothing in the suite
is shaped like the counterexample; **only the question is.**

**(7) §5.6 — ACCEPTANCE POWER IS NOT ROW COUNT.** The carry-dropping wrong model
**passes 5 of 8 `add128` rows**; **only the ripple rows discriminate**, and all
three flips were run.

> **A row count is not acceptance power. The non-vacuity flips measure which
> rows do the work.**

**Eight rows sounds like a battery and behaves like three** — the other five are
not waste, but **a lane reading "8 rows" as strength has read the wrong
number.** §5.3's non-vacuity discipline used as **a measuring instrument** rather
than a hygiene check.

**(5) §5.3 — A THIRD MECHANISM IN ONE LANE, so the family becomes a TAXONOMY BY
MECHANISM.** `| _ => true` with unbound parameters: **body refused, fallback
fired, row passed**; the flip gave **0 errors**. Landed as a three-row table —
hand-typed oracle (§G13), byte-identical section (§G15), catch-all fallback
(§G23) — because they share a symptom and **no two are found the same way.**

> **A fallback arm returning `true` converts a failing run into a passing row.**

**And the catch-all is the worst of the three, because it converts a REFUSAL
into a PASS**: the other two produce rows that never had content; this one
**takes a working row, lets it fail, and reports the failure as agreement.**
*Every earlier vacuity in this section is an absence; this one is an inversion.*

**(6) §2.4 — ONE CLASS OF DUPLICATE IS FOUND BY THE COMPILER.** `bitLenSpec`
existed twice and **Lean's ambiguity error found it.**

> **A duplicated SPECIFICATION is found by the namespace, not by review.**

**The cheap corner of MEAS-28's problem** — `dupes.sh` exists because most
duplication is invisible to the language, so **the instrument's real subject is
duplication the compiler cannot see**, and a lane should not build a census for
the half that reports itself. **And the repair did more than deduplicate**:
`Len64`'s model **IS definitionally what §G15 proved.**

> **The best outcome of removing a duplicate is not tidiness; it is that a
> theorem stops being ABOUT the model and starts being TRUE OF it.**

**(8) §9.0b — THE `+0`-IN-PLAN CONTROL'S THIRD USE, with a prediction
attached.** Reach unmoved **deliberately and said in the plan**; the next rung is
**priced in advance at `+7` with all prerequisites discharged.**

> **A plan that prices its next rung EXACTLY is making a falsifiable claim.**

**Owed at that landing**: exactly `+7` records beside ES's exact prediction as
**calibration evidence**; **anything else is the more valuable row**, because a
missed prediction with all prerequisites discharged says something about the
**pricing method** rather than about the work.

**Standing number for this lane (§9.0):** no conformance suite — `docs_check`
**91/91**; ids minted here **MEAS-226 … MEAS-231, STMT-125**, and **MEAS-185
amended.**
