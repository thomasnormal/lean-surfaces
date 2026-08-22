# The ECMAScript tier's M2: the semantic model, PLANNED

**Status: a design, and no interpreter.** M1 is complete
(`docs/es-charter.md` §5, `docs/backlog.md` §L66): the corpus ingests,
66 node kinds round-trip, and 21 `#guard`s pass with no evaluator in the
repository. This document plans the evaluator — the monad, the
correspondence convention, the deferral boundaries and a priced inch
ladder — and per §L25's law it does it **census first**. Every number
below is a run of `harness/es_m2_census.py`, landing with this document;
rows in `docs/es-m2-census.json`.

Edition `ES2026` at the `es2026-errata` revision throughout
(`docs/es-edition.json`).

---

## 0 THE CENSUS, and the three things it decided

### 0.1 The floor is set by the HARNESS, not by the tests

Every test262 test evaluates `harness/assert.js` and `harness/sta.js` in
its realm **before its own source** (INTERPRETING.md). So the prelude's
requirements are mandatory for every test, and they are not a matter of
taste. Measured:

| | |
| --- | ---: |
| node kinds in `assert.js` ∪ `sta.js` | **27** |
| declaration forms used | **`var` only** — zero `let`/`const` |
| free identifiers | `Array`, `Infinity`, `JSON`, `Object`, `String`, `Test262Error`, `undefined` |

**But the vocabulary understates the floor, and reading the source is what
shows it.** `sta.js` defines `Test262Error` as

```
function Test262Error(message) {
  if (!(this instanceof Test262Error)) return new Test262Error(message);
  this.message = message || "";
}
Test262Error.prototype.toString = function () { … };
```

so before any test can *signal a failure* the evaluator needs function
objects with `[[Call]]` **and `[[Construct]]`**, `this` binding, ordinary
objects, property get/set, `[[Prototype]]`, `instanceof`, and `throw`.
**The ordinary object model is rung 0, not a later rung** — there is no
arrangement of the corpus in which it is deferrable.

**The good news is on the success path.** `assert(mustBeTrue)` returns
immediately on `mustBeTrue === true`; `assert.sameValue` returns as soon
as `_isSameValue` holds. Every formatter — `String(value)`,
`Object.prototype.toString`, `JSON.stringify` — runs **only when a test
FAILS**, and `assert.js` even guards `typeof JSON !== "undefined"`. So a
PASSING test needs almost none of the intrinsic surface it mentions, and
the first scoreboard is far cheaper than a reading of the prelude
suggests.

### 0.2 The built-in obligation is about a dozen names

The intrinsic list is **derived from the pinned spec**, not typed by hand:
ECMA-262 clause 19 (The Global Object) enumerates the realm's names, one
heading each — **59 of them**. Of those, **51 are referenced** by the
18,114-test language-core slice; 8 never are (`Atomics`,
`FinalizationRegistry`, `Float16Array`, `Iterator`, `decodeURI`,
`decodeURIComponent`, `encodeURI`, `encodeURIComponent`).

Ranked by tests referencing them:

| intrinsic | tests | | intrinsic | tests |
| --- | ---: | --- | --- | ---: |
| `Object` | 1957 | | `String` | 496 |
| `undefined` | 1809 | | `SyntaxError` | 395 |
| `TypeError` | 1218 | | `Number` | 342 |
| `ReferenceError` | 1166 | | `Boolean` | 204 |
| `eval` | 1028 | | `isNaN` | 177 |
| `Symbol` | 974 | | `NaN` | 155 |
| `Array` | 569 | | `Infinity` | 140 |

**The top 12 cover 10,335 of 11,248 intrinsic references — 91.9%.** This
is the ES form of the C lane's result that *"the libc obligation is not
libc, it is `printf`"* (`docs/c23-goal.md` §1.3), and it is stronger,
because **three of the top names are error constructors the LANGUAGE
throws** — `TypeError`, `ReferenceError`, `SyntaxError` are semantics, not
library. Strip those and `undefined`/`NaN`/`Infinity` (which are values,
supplied by existing), and the genuine library obligation at the top of
the corpus is `Object`, `eval`, `Symbol`, `Array`, `String`, `Number`,
`Boolean` — **seven names**.

**A free identifier here is one of three things and only one is a
built-in**, which is why the census buckets them. Besides intrinsics there
are `arguments` (389 tests — a language binding), and **153 distinct
deliberately-unresolvable names** (`X` 112, `p1` 109, …) which are the
*subject* of ReferenceError tests: the tier's job is to throw for them,
not to supply them. A census that pooled the three would have ranked
`unresolvableReference` beside `Object`; the first version of this
instrument did exactly that, and also counted object-literal KEYS
(`configurable` appeared 1,327 times) until non-reference `Identifier`
positions — keys, labels, member names — were excluded. Both corrections
are in the instrument's `--self-test`.

### 0.3 The completion types are NOT equally weighted

Across the slice:

| construct | sites | | construct | sites |
| --- | ---: | --- | --- | ---: |
| `ThrowStatement` | 17863 | | `BreakStatement` | 194 |
| `ReturnStatement` | 13117 | | `LabeledStatement` | 141 |
| `TryStatement` | 1152 | | `SwitchCase` | 84 |
| `CatchClause` | 1092 | | `ContinueStatement` | 74 |

`throw` and `return` are everywhere; **`break`/`continue`/labels are
three orders of magnitude rarer**. That does not make them optional — a
completion record has four abrupt types and the semantics must carry all
four — but it does say where the corpus's weight is, and §4's ladder
spends effort accordingly.

---

## 1 THE MONAD — and completion records ARE its return discipline

### 1.1 The stack, taken from the family and not re-derived

`docs/family-architecture.md` §3.4 fixes the substrate, with the layer
order established by `rfl` rather than by taste:

```lean
-- (illustrative — the family's substrate shape, quoted from §3.4)
abbrev SemM (W : Type) (ρ : Type) := ExceptT ρ (StateT W Halt)
```

This tier adopts it **by shape, not by spelling**: if the structures
census moves the base to `EStateM`, nothing below changes, because
everything below is stated in terms of *what the stack does* — retains
`W` on the error branch, short-circuits on `ρ`, carries `Halt`'s
fuel-exhaustion and unsupported outcomes — and not in terms of which
combinators spell it.

Fixed by the family and inherited without argument: **fuel is an index on
the step function, never a layer** (as a layer it does not typecheck —
the recursion argument disappears); **nondeterminism is an explicit
parameter**, not an effect. Neither is re-litigated here, and §2.3 shows
ECMAScript has almost nothing to point the second one at.

### 1.2 ρ IS the abrupt completion record — the whole of it

> **DECISION: `ρ = Abrupt`, carrying all four non-normal completion
> types**, not `throw` alone with the rest as a flow-sum in `α`.

```lean
-- (illustrative — the shape this design proposes, not yet in the tree)
inductive Abrupt where
  | throw    (value  : Val)                    -- ε is RVal-like: see §1.3
  | ret      (value  : Val)
  | brk      (target : Option String)
  | cont     (target : Option String)
```

**The argument is the spec's own notation, and it is close to
decisive.** ECMA-262 writes abrupt propagation as an OPERATOR: `? Foo(x)`
appears at **2,328 sites** in `ES2026` and `! Foo(x)` at **555**, while
`ReturnIfAbrupt` — the ES5-era spelling those abbreviate — appears **0
times** (`docs/es-charter.md` §1.3). `?` propagates *any* abrupt
completion, which is `ExceptT`'s bind and nothing else. Under this
decision the correspondence is mechanical:

| the spec writes | the model writes |
| --- | --- |
| `? Foo(x)` | `← foo x` |
| `! Foo(x)` | `← foo x` at a **total** variant, with the cannot-throw obligation discharged (§1.4) |
| `Return Completion(…)` | `throw`/`pure` at the matching arm |
| `UpdateEmpty(c, v)` | a `catch` that fills an `empty` value |
| LabelledEvaluation's absorption | a `catch` at exactly the construct the spec names |

The alternative — `throw` in `ρ`, the other three summed into `α` — is
the Python tier's shape (`PyPost`'s `next`/`ret`/`brk`/`cont`/`err`
arms), and it is right *there* because that tier's `Run` was designed
before the substrate existed. Here it would make every statement's `α` a
sum and force every sequencing point to case on it — which is the
boilerplate `ExceptT` exists to remove — and, worse, it would break the
one-line correspondence with `?` that §2 is built on.

**What the Python precedent DOES give**, and it transfers whole: `PyPost`
is a *flow-aware postcondition* with one arm per flow shape, and the ES
proof layer will want exactly that against `Abrupt`'s four arms. The
precedent belongs at the **specification** layer (`PyPost`), not at the
**monad** layer (`ρ`), and keeping those apart is the point of citing it.

### 1.3 ε is RVal-like — the recorded requirement, met

`docs/es-charter.md` §4.1 recorded this tier's requirement on the
substrate's error type: **a thrown JS value is an arbitrary ECMAScript
language value**, not a closed enum and not necessarily an `Error` —
`language/statements/throw/S12.13_A2_T2.js` throws a primitive. So
`Abrupt.throw` carries a `Val`.

That makes this tier the second consumer the C charter said would settle
the question (`docs/backlog.md` §L35 priced the `Run` move at 149 lines /
24 files / 1,251 sites). **The question is the architecture lane's and is
not blocking here**: this design needs only that `ρ` be a tier-chosen
type, which the family's `SemM W ρ` already provides by being
parametric. If the arch lane's answer lands mid-flight, the only thing
that changes is where `Abrupt` is declared, not what it contains.

### 1.4 `!` is an obligation, not an assumption

`! Foo(x)` asserts the call **cannot** return an abrupt completion. 555
sites say so, and a tier that implemented `!` as "assume it didn't" would
be inventing a fact the spec merely records. Design:

* every abstract operation gets its ordinary `SemM` form;
* an operation the spec ever calls with `!` **additionally** gets a total
  form whose type has no `Abrupt`;
* the two are tied by a lemma — *this operation, at these argument
  constraints, never throws* — and until that lemma exists the `!` site
  uses the ordinary form and the surrounding proof carries the
  obligation.

This is the C lane's UB discipline turned around: there, refusing is the
product; here, **`!` is a place the spec claims a refusal cannot happen,
and the model owes a proof rather than a shrug.**

---

## 2 CORRESPONDENCE — one Lean definition per abstract operation

### 2.1 The convention, restated with a citation format

`docs/es-charter.md` §1.3 fixed it and §1.4 measured why the citation is
a triple: **one Lean definition per typed clause, cited by
`(edition, clause-id, step)`** — a triple because clause ids are not
stable, and 6,776 test262 rows already cite ids the current draft no
longer defines.

The `ES2026` core slice's obligation, by clause type:

| clause type | in the whole spec | what M2 owes |
| --- | ---: | --- |
| abstract operation | 489 | the ones clauses 5-17 reach |
| **syntax-directed operation** | **202** | the evaluation core: one `def` per production it matches |
| internal method | 59 | the ordinary-object slots, then exotics |
| concrete method | 48 | environment records, mostly |
| numeric method | 36 | Number/BigInt arithmetic |
| built-in function | 527 | **out of the language core** — §3.2 |

The language core is **907 clauses / 1,365 algorithms / 6,216 numbered
steps**. That is the honest size of the target, and it is 44% of the
document's steps.

### 2.2 Mechanical checkability, from day one

A correspondence claim nobody can check is a comment. Two instruments,
both cheap, both in the M1 pattern where the census is the oracle:

1. **A manifest**: every Lean definition carries its `(edition, clause-id,
   step-range)`; a checker asserts each cited clause **exists in the
   pinned spec** (the census already parses all 2,262 clause ids) and that
   no two definitions claim the same clause.
2. **A coverage number**: cited clauses ÷ core-slice clauses, published
   per rung. This is the ES analogue of `engine262`'s 1,782 `#sec-`
   anchors, of which 1,141 resolve — a working implementation of this
   spec independently arrived at the same convention, and its coverage is
   measurable, so ours must be too.

### 2.3 The ∀-order parameter has nothing to point at — confirmed for M2

`docs/es-charter.md` §2.3 measured zero occurrences of all five
order-latitude phrasings, and §2.4 filled the family's behaviour-class
table with an **empty** undefined-behaviour cell. M2 inherits that: the
family's nondeterminism-as-parameter machinery is **not instantiated by
this tier at all** in the core slice. The one clause that would need it —
clause 29, the Memory Model — is outside the slice and is the same
obstacle C's R6 names.

---

## 3 THE DEFERRALS, each with its refusal cause

Refusals keep the charter's three causes (`docs/es-charter.md` §3.6), and
every deferral below names which one it raises. **None of them is a
debt**; each is a boundary with a number.

### 3.1 The event loop and job queues — DEFERRED, boundary stated

**Single-script semantics first**: one Script, evaluated to completion,
no job queue, no microtask checkpoint, no host event loop.

The boundary is a **host hook**, which is what makes the refusal clean
rather than arbitrary. `HostEnqueuePromiseJob`, `HostEnqueueGenericJob`,
`HostEnqueueTimeoutJob` and `HostEnqueueFinalizationRegistryCleanupJob`
are 4 of the spec's 16 host-defined abstract operations
(`docs/es-charter.md` §2.2), so a program that needs a job to run reaches
a clause the specification itself defers to the host.

> **A test that requires a job to be drained REFUSES with cause
> `environment`** — the same cause `docs/family-architecture.md` §3.5.4
> assigns to transcendental accuracy. Not `unsupported-construct`: the
> construct is modelled, the HOST is absent.

**Measured, and the residue is tiny**, because the charter's slice
already excludes every `async`-flagged test: in 18,114 core-slice tests
there are **26 `AwaitExpression` sites**, `Promise` is referenced by **16
tests**, and `ImportExpression` by 175. **A single-script evaluator is not
a crippled one on this corpus** — it is very nearly the whole of it.

### 3.2 The built-ins — a REFUSAL CAUSE, never a debt

The 527 `built-in function` clauses are outside the language core by the
charter's slice, and §0.2 measures the real surface: seven library names
carry the top of the corpus. An unmodelled one raises
**`unmodeled-intrinsic`**, which retires by widening the slice and is
reported separately from tier gaps precisely so 23,109 unbuilt built-ins
can never read as a language-tier failure.

### 3.3 Generators — IN SCOPE, and they must be DEFUNCTIONALIZED

This is the deferral that is **not** one, and it needs saying because the
naive plan is impossible.

`docs/family-architecture.md` §3.4 rules, as a property of the substrate
and not of any tier: **`SemM` cannot SUSPEND.** `ExceptT ρ (StateT W
Halt) α` unfolds to `W → (Except ρ α × W)` — an `α`, or a `ρ`, plus a
`W`, and no third case. *"A tier that plans a suspension effect is
planning something the types do not admit."*

ECMAScript generators suspend mid-body, and they are **inside** the core
slice: `YieldExpression` is 1,171 sites and arrives at ladder step 12.
So:

> **DECISION: a generator is a defunctionalized continuation living in
> `W`, and resumption is an ordinary call — never a suspension effect.**
> §3.6 (1a) is the family's pattern; SystemVerilog is its worked example;
> and **the Python tier has already done this exact thing for this exact
> construct** (AGENTS.md H4: `Obj.generator` with a stack of `GenFrame`s,
> `yield` admitted in statement position, `break` = pop the loop frame).

That precedent is worth more here than anywhere else in the family: same
problem, same language family, already solved once in this repository,
and the Python lane's recorded findings (the `genPlan` free-scrutinee
requirement; `termination_by structural fuel` on every mutual member)
transfer directly.

`async`/`await` is the same mechanism plus the job queue, so it lands
behind §3.1 rather than beside it.

### 3.4 What else is out, briefly

`eval` is referenced by **1,028 tests** and is a language feature
(direct eval sees its caller's scope), not a library one — it is in scope
but late, because it needs the environment-record layer complete.
Modules, Annex B and ECMA-402 stay out per the charter's slice.

---

## 4 THE INCH LADDER, priced

Prices are in the program's units: an INCH is one landable, separately
green step; a SESSION lands one to three. The ladder's *order* is
measured — `harness/es_m2_census.py` computes the greedy vocabulary
ladder over the slice — and its *content* is the design above.

### 4.1 The measured vocabulary ladder

Seeded with the prelude's mandatory 27 kinds, each step adds the ONE node
kind that clears the most still-blocked tests:

| step | construct added | clears alone | cumulative (of 14,045 parsed) |
| ---: | --- | ---: | ---: |
| 0 | *the prelude's 27 kinds* | — | **2,828** |
| 1 | `ObjectExpression` | 174 | 3,002 |
| 2 | `Property` | 725 | 3,727 |
| 3 | `AssignmentPattern` | 246 | 3,973 |
| 4 | `ObjectPattern` | 577 | 4,550 |
| 5 | `EmptyStatement` | 240 | 4,790 |
| 6 | `ArrowFunctionExpression` | 211 | 5,001 |
| 7 | `ArrayPattern` | 219 | 5,220 |
| 8 | `ArrayExpression` | 820 | 6,040 |
| 9 | `ForOfStatement` | 456 | 6,496 |
| 10 | `RestElement` | 556 | 7,052 |
| 11 | `SequenceExpression` | 288 | 7,340 |
| 12 | `YieldExpression` | 269 | 7,609 |
| 13 | `WithStatement` | 219 | 7,828 |
| 14 | `SpreadElement` | 163 | 7,991 |
| 15 | `ForInStatement` | 99 | 8,090 |
| 16 | `ImportExpression` | 76 | 8,166 |

**Sixteen constructs take the reachable corpus from 2,828 to 8,166.** The
shape of the list is itself a finding: steps 2-10 are almost entirely
**destructuring and object/array literals**, which matches the charter's
observation that `destructuring-binding` is the slice's largest feature
tag at 5,495 tests. A tier built in "textbook order" — control flow,
then operators, then objects — would clear far fewer tests per inch.

The usual caveat, stated as the C lane states it: this is reach of the
**vocabulary**, what the evaluator must accept. It is not a claim that
the semantics would run any of these tests, because at M2's start there
is no semantics.

### 4.2 The inches

| # | inch | what lands | price |
| ---: | --- | --- | --- |
| 1 | **The value model** | `Val` (the 8 language types), `Val.typeof`, SameValue/SameValueZero, ToBoolean/ToNumber/ToString/ToPrimitive as `SemM` operations. Number is core `Float` (`docs/es-charter.md` §4.2(a): Layer 1 is supplied, kernel-reducible). | 1-2 sessions |
| 2 | **The monad + completion records** | `SemM`, `Abrupt`, the `?`/`!` convention, `UpdateEmpty`, and the correspondence manifest checker (§2.2). No evaluation yet. | 1-2 |
| 3 | **Objects and the prototype chain** | Property descriptors, the ordinary `[[Get]]`/`[[Set]]`/`[[GetOwnProperty]]`/`[[DefineOwnProperty]]` internal methods, `[[Prototype]]` walk, `instanceof`. **This is §0.1's floor.** | 3-4 |
| 4 | **Environments and functions** | Environment records, scope chains, `[[Call]]`, `[[Construct]]`, `this` binding, `arguments`. Closes the prelude. | 3-4 |
| 5 | **Statements and expressions over the seed vocabulary** | The 27 prelude kinds' SDOs — the `Abrupt` arms get exercised for real. | 3-4 |
| 6 | **THE FIRST SCORE** — the rung-0 scoreboard | `harness/es_refusal_census.py` + the runner; §5. | 2 |
| 7+ | **The ladder** | §4.1's steps, re-censused before each. Destructuring (steps 3-10) is one campaign, not eight inches. | 2-4 each |

**~15-20 sessions to the first real score, with the score at inch 6 rather
than at the end** — deliberately the shape `docs/c-semantics-design.md`
chose, and for the same reason: a tier that cannot report a number until
it is finished cannot be steered.

---

## 5 RUNG 0 — the first scoring target, measured

### 5.1 Which tests, and how many

A test is scoreable only if the evaluator has **both** its syntax and the
realm names it reaches. Counting either alone overstates the target, so
the census crosses them:

| intrinsics the realm supplies | tests in the prelude's vocabulary | **AND within budget** |
| --- | ---: | ---: |
| none | 2,828 | **1,205** |
| the error constructors | 2,828 | **1,289** |
| + `Object` | 2,828 | **1,351** |
| + `String`,`Array`,`Number`,`Boolean` | 2,828 | **1,820** |

> **RUNG 0 = the 1,205 core-slice tests that need only the prelude's 27
> node kinds and no intrinsic beyond what `assert.js`/`sta.js` define.**
> Rung 0+ = 1,351 with `Object`, and 1,820 with six built-ins.

These are `test/language/**` tests, positive and negative-runtime, from
the charter's language-core slice — not a hand-picked set, and
regenerable by the instrument.

### 5.2 What the verdict instrument needs

`harness/es_refusal_census.py`, the sibling of the Python lane's
`refusal_census.py` and of the C lane's specced-but-unbuilt
`c_refusal_census.py`. **It is not built in this dispatch**, because it
has nothing to run until inch 5 — an instrument with no subject is a
stub. Its spec:

* **Input**: the rung-0 test list (regenerated, never stored as rows), the
  pinned edition, and the prelude.
* **Per test**: evaluate `assert.js`, then `sta.js`, then the test, in one
  realm, under fuel.
* **The oracle is test262's own rule**: a test PASSES by **not throwing**;
  a `negative` test passes by throwing the named error class at the named
  phase. No output modelling anywhere — the charter's §3.2 result.
* **Verdicts** MATCH / REFUSE / DIVERGE / TIMEOUT, with **DIVERGE zero,
  always**, and REFUSE broken out by its three causes
  (`unsupported-construct` / `unmodeled-intrinsic` / `environment`) which
  are never pooled, because they retire on completely different schedules.
* **The strict/sloppy double run is part of the verdict**: a test without
  `onlyStrict`/`noStrict`/`module`/`raw` is TWO runs and MATCH means both.
  Runs and tests are reported separately so a denominator cannot silently
  halve.
* **LIVENESS IS LOAD-BEARING HERE IN A WAY IT IS NOT FOR THE SIBLINGS.**
  A test passes by *not throwing*, so **a model that evaluated nothing and
  threw nothing would score MATCH on every positive test.** The row must
  carry a statement/step count and a zero is never agreement. The charter
  flagged this at §3.3 and it is repeated here because it is the one way
  this scoreboard can be silently, totally wrong.
* One runner process for the whole batch; one row per test in test order;
  a `runner-error` row rather than a missing row; non-zero exit only on
  DIVERGE; and **no whitelist for silencing a mismatch**.

---

## 6 WHAT THIS DESIGN DOES NOT DECIDE

* **Where `Abrupt` lives** — the architecture lane's second-consumer
  question (§1.3). Not blocking: `SemM W ρ` is parametric today.
* **Whether the base is `ExceptT`/`StateT` or `EStateM`** — this design is
  stated by shape, so the structures census can move it without reopening
  anything here.
* **The proof layer.** M2 is an evaluator and a scoreboard. `PyPost`'s
  flow-aware-postcondition shape is named as the precedent (§1.2) and
  nothing more is committed.
* **Property-key ordering.** Integer-index-then-insertion order is
  specified and must be modelled, but which representation pays for it is
  an inch-3 question, not a charter one.

---

## 7 WHAT LANDED WITH THIS DOCUMENT

* `harness/es_m2_census.py` — the instrument: the mandatory-prelude seed,
  the greedy vocabulary ladder, the spec-derived intrinsic surface, and
  the rung-0 crossing. `--self-test` covers three refusal paths plus the
  two classification bugs it was written with (object-literal keys as
  intrinsics; a ranking destroyed by `sort_keys`).
* `docs/es-m2-census.json` — every number above.
* `docs/es-semantics-design.md` — this document.
* `docs/backlog.md` § — the record.

**No Lean, no interpreter, and no change to any existing file.**
