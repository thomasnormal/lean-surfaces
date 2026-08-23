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
section **one day after it was written**. And the Wasm lane ran the enumeration
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
**conditional on that landing** and says so at the site — a law citing a tree
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
