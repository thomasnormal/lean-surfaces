# The ECMAScript lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the ES lane.** Ids are `YYYY-MM-DD-es-<n>` and need no reservation, because
the lane name makes them unique — which this lane has its own reason to want:
its entries were renumbered **four** times in one day around collisions
(`L64→L65→L66`, then `L87→L88`), each time under the push-time re-read §9.5
retires.

**Everything before 2026-08-22 is in `docs/backlog.md`** and stays there; this
lane's history is §L66 (the founding charter), §L78 (the M2 design), §L82
(M2 inch 1) and §L88 (M2 inch 2), and every one of those references keeps
resolving.

---

## 2026-08-22-es-1 — M2 INCH 3: environments, `[[Call]]`, `[[Construct]]` and `this` — and the spec CORRECTED this lane about `[[ThisBindingStatus]]`

`LeanModels/Es/{Env,Function}.lean` + `Examples/es/functions/guards.lean` —
**523 new lines of Lean, 26 new `#guard`s (108 in the lane), 63 `@[es_spec]`
lemmas.** The design is §L78's; this is its inch 4 (this lane's third).

**SIZED FROM THE PINNED SPEC BEFORE BEING WRITTEN**, the same discipline as
inch 2: the clauses realized here carry **204 numbered steps** in `ES2026` —
`[[Construct]]` 24, `OrdinaryFunctionCreate` 23, `OrdinaryCallBindThis` 18,
`SetMutableBinding` 14, `[[Call]]` 14 — against inch 2's 159.

### THE SPEC CORRECTED THIS LANE, and the guards are what asked it

`NewFunctionEnvironment` (§9.1.2.4) was written with
`[[ThisBindingStatus]] := initialized` for a non-derived function, reasoning
that only a *derived* constructor has to wait for `super()`. **Three guards
failed at once**, all with "Super constructor may only be called once": every
ordinary `[[Call]]` threw, because `BindThisValue` (§9.1.1.3.1) refuses to
bind a `this` that is already `initialized`.

Read back from the pinned text, the clause says: **lexical ⇒ `lexical`, else
`uninitialized`** — full stop. `derived` plays **no part in that clause at
all**; it decides only whether `[[Construct]]` builds `thisArgument` up front
(§10.2.2 step 5). The record starts *uninitialized* and `BindThisValue` is
precisely what initializes it, so a record that began `initialized` had
already been bound and the second bind is the error the message names.

**The correction is the method working.** A plausible reading of one clause
was refuted by executing another, and the cost was one compile because the
guards exercise `[[Call]]` end to end rather than testing the record in
isolation.

### THE ACCESSOR REFUSAL IS RETIRED, and the boundary got NARROWER

Inch 2 refused every accessor `[[Get]]` because `[[Call]]` did not exist.
Now an accessor whose getter is a **builtin runs**, and it receives the
RECEIVER as its `this` (§10.1.8.1 step 8) — both pinned. What replaces the
per-feature refusal is **one** boundary: `OrdinaryCallEvaluateBody`
(§10.2.1.4) on an `ecmascript` body, which needs the statement evaluator
(inch 5). **A rung is supposed to move a refusal down the stack and make it
narrower, and this one did.**

One structural note, recorded because it is a real constraint and not a
preference: **Lean forbids `Ordinary.lean` importing `Function.lean`** (the
import would cycle), so the COMPLETE §10.1.8.1 lives in `Function.lean` as
`getV` (= §7.3.2 `Get`) and `ordinaryGet` remains its data-property
fragment, its docstring saying so. The alternative — parameterizing
`ordinaryGet` by a call-back at inch 2 — would have put a hole in the object
model for a caller that did not exist yet.

### `this` IS THE THREE-MODE CLAUSE, and strict is complete

`OrdinaryCallBindThis` (§10.2.1.2, 18 steps) is where `this` is decided, and
all three arms are pinned: **lexical** (an arrow) binds NOTHING so the lookup
walks outward — which *is* lexical `this`, not a special case; **strict**
binds the argument exactly, `undefined` included, with no coercion; and
**sloppy** substitutes the global object or boxes a primitive, both of which
need the realm, so both **refuse** with `unmodeledIntrinsic` rather than
inventing a global. **Strict mode is complete — which is what `sta.js` is,
and half of what test262 runs.**

### THROW vs REFUSE, kept straight in both directions

The environment clauses are where the distinction earns itself, and every one
is a guard: an unresolvable name **throws** `ReferenceError` (§9.4.2 step 3),
reading a binding before initialization **throws** `ReferenceError` (the TDZ,
which is why `Binding.value` is an `Option` — a record defaulting to
`undefined` could not tell `let x` from `let x = undefined`), assigning to a
`const` **throws** `TypeError` in strict code and is **SILENTLY IGNORED**
otherwise (§9.1.1.1.5 step 7.b, the one place the spec asks a write to do
nothing), and calling a non-callable **throws** `TypeError` (§7.3.14). All of
those land in `ρ` where a `try` can catch them. Only the unmodeled refuses.

### The `sta.js` construction shape, end to end

`new F()` on a base constructor returns **the object it made** (§10.2.2 step
13, not the body's `undefined`); that object's `[[Prototype]]` **is**
`F.prototype`, so `instanceof` finds it; and `MakeConstructor` sets
`F.prototype.constructor === F` (§10.2.5 step 6). Everything but the body
statements is exercised, and the body's refusal is pinned rather than hidden.

Non-vacuity checked five ways: claiming a sloppy `const` assignment takes
effect, the TDZ throwing `TypeError`, an unrelated object being an instance,
the body refusal's cause flipped, or an arrow having a `this` binding — each
fails with the expression printed.

### Also adopted this landing

**`docs/backlog/es.md` is this file** (§9.5), **`tools/triad.sh` replaced
`es-build.sh`** (validated at `--lane es`; note `--lane` rejects hyphens, so
the old `es-lane` tag would not have parsed), and the lane is on **`master`**
after the A13 seeding branch trap recorded in §L88.

### Triad — GREEN, and `triad.sh`'s DEFAULT GATE SET is narrower than this lane's was

`lake build` **3723 jobs, exit 0**; `docs_check` **83/83**, 29
illustrative-exempt; `diff_test` **1427 cases, 0 failed, 118 whitelisted, 1309
matched** (1394 → 1427 is sibling growth, not this lane's — the ES lane still
adds no rows to either Python harness). Coverage VERIFIED by olean timestamp,
not assumed: `Env.olean`, `Function.olean` and `functions/guards.olean` are all
stamped **21:45**, inside the tenure.

**THE RSS GUARD FIRED ON ITS OWN CHAIN, AND THE RETRY WAS RIGHT.** Attempt 1
died at **exit 137** — `tools/triad.sh`'s own kill line, reaping *our* chain
when it crossed the limit, exactly as amendment 11 specifies and by parentage
only. The script recognised 137 as a RESOURCE KILL rather than a red build and
re-ran; attempt 2 went green. **A shared script implementing the amendment
correctly is worth more than six lanes each reading it**: this lane's retired
`es-build.sh` had the same guard, and would have had to get the 137-vs-red
distinction right on its own.

**A GAP THIS LANE OWES ITSELF, found by reading the log rather than trusting
it.** `tools/triad.sh`'s DEFAULT gates are `docs_check; diff_test` — and
**`script_corpus` is not among them**, though the retired `es-build.sh` ran it.
The default is not wrong (gates are a lane's business, and the script takes
`--gates`), but a lane migrating to it inherits a NARROWER gate set silently.
Re-run under its own ticket with `--gates` naming all three; recorded here
because the failure mode is a landing that reads green against fewer checks
than the one before it, which no amount of care at the build itself would
catch.

### ADOPTION OWED — `RefusalCause π` (family-architecture `14bdd7a`), by touch

Read, and **not applied mid-inch**: `LeanModels/Es/Completion.lean` is
untouched by this landing and adopts at its next touch, per §9.2.

The ruling: `Core` carries the FOUR §5.2 classes as `RefusalCause π`,
parameterized by a tier payload. For this lane π is **the host-hook name**.
Concretely, at next touch:

* **GAIN two constructors, both PRESENT AND GATED EXPECTED-EMPTY** —
  `undefined` and `order-dependence`. This is the part of the ruling aimed at
  this lane, and it is the right correction: omitting `undefined` because
  ECMAScript has none made the emptiness *a fact about the type, invisible to
  the scoreboard*, which cannot then tell **"this language has no UB"** from
  **"this tier did not model that column."** §4.3's Wasm prescription —
  *expect the bucket empty, and gate it* — needs a constructor to be about.
  **Both gates are the scoreboard-visible form of measurements this lane
  already published**: §L66 measured "undefined behaviour" occurring ONCE in
  3.08 MB in a sentence asserting there is none, and ZERO occurrences of all
  five order-latitude phrasings. The gates make those two headline findings
  checkable instead of quotable.
* **`unsupportedConstruct` → class `unsupported`**; **`unmodeledIntrinsic` and
  `environment` both → class `environment`**, with the split moving into the
  payload.
* **The split is PRESERVED and registered as a candidate FIFTH class.** It was
  not flattened: inspection found it tracks §5.2's own criterion — a built-in
  outside the slice retires by widening the slice, a host facility does not
  retire by building more language. If a second tier independently makes the
  same split, §9.3's convergence standard promotes it. *One tier's distinction
  is a payload; two tiers' identical distinction is a class.*

## 2026-08-22-es-2 — `RefusalCause π` ADOPTED, both expected-empty gates PROVED — and the ladder was being read one layer up

Two things, and the second is a correction this lane owed the coordinator
rather than the other way round.

### THE LADDER CONFIRMATION — the next rung is NOT the destructuring cluster

The dispatch named the destructuring/literals cluster as inch 4, from this
lane's own 16-step ladder, and asked for a confirmation against the census
first. **The confirmation says otherwise, and the census is what says so.**

`docs/es-m2-census.json`'s ladder is a **VOCABULARY** ladder — what the
INGESTER accepts — and `docs/es-semantics-design.md` §4.1 says so in as many
words: *"this is reach of the vocabulary… It is not a claim that the
semantics would run any of these tests."* All 66 kinds have been ingested
since M1. So adding `ObjectExpression` to the ingester buys **zero** tests,
because nothing evaluates `if (x) return y` yet.

Read the other column and it resolves: the ladder's **step 0 is 2,828 tests
reachable with the PRELUDE'S 27 SEED KINDS** — and those 27 are exactly
`ExpressionStatement`, `IfStatement`, `BinaryExpression`, `CallExpression`,
`VariableDeclaration`, `ReturnStatement`, `TryStatement`, `SwitchStatement`
and friends: **the kinds this tier can ingest and cannot evaluate.** The
rung-0 target (1,205 tests) is defined as syntax ∩ intrinsics over that same
seed. **So the next rung is the EVALUATOR over the seed vocabulary** — this
lane's design-ladder inch 5 — and the destructuring cluster is the rung
*after* it, at which point the vocabulary ladder starts meaning something.

**Sized before writing, as ever**: that evaluator is **397 numbered steps**
(reference records 39, operands 8, operators 82, calls 38, statements 28,
declaration instantiation 152, the still-owed conversions 50) against inch
3's 204 — so it SPLITS. Expressions + reference records + conversions is one
landing; statements, declaration instantiation and body evaluation is the
next, and that one reaches the first score.

### THE ADOPTION — `RefusalCause π`, four classes, both gates PROVED

Taken now rather than deferred, and the reason is small but real: **inch 4
adds refusal sites**, and adding call sites to a type already ruled to change
is building debt. `Core` does not export `RefusalCause` yet, so this file
carries the family SHAPE under the same adoption note `SemM` has — replaced
by the core export when it lands, not a variant.

* Four classes, `RefusalCause π`, `π` = `EsDetail` (an `EsCause` + a name).
* `unsupportedConstruct → unsupported`; `unmodeledIntrinsic` and
  `environment` → **class `environment`**, with the split moved into the
  payload and **preserved** as the registered candidate fifth class.
* **`esRefusal` is the tier's ONLY cause constructor**, which is what makes
  the gates mean something.

**THE TWO EXPECTED-EMPTY GATES ARE THEOREMS, not comments:**

    theorem es_never_undefined      (k n) : (esRefusal k n).isUndefined       = false
    theorem es_never_orderDependent (k n) : (esRefusal k n).isOrderDependence = false

Both by `cases k <;> rfl`, plus
`es_class_is_unsupported_or_environment`. **This is the checkable form of
this lane's two headline measurements** — §L66 measured "undefined behaviour"
occurring ONCE in 3.08 MB, in a sentence asserting there is none, and ZERO
occurrences of all five order-latitude phrasings. Until now those were
quotable; now a UB refusal cannot be built without bypassing `esRefusal` and
breaking a theorem. Non-vacuity checked: asserting the tier CAN emit
`undefined` fails with "not definitionally equal".

**One reclassification the adoption forced, and it is a real one.**
Sloppy-mode `this` substituting the global object was refusing as
`unmodeledIntrinsic`; it is a **host facility** — the global object comes
from the realm the HOST provides, and it does not retire by widening an
intrinsic slice. Moved to `hostFacility`. The split earning its keep the
first time it was applied is the argument for keeping it.

115 `#guard`s in the lane, 67 `@[es_spec]` lemmas, lint clean.
