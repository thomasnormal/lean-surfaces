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

## 2026-08-22-es-3 — M2 INCH 4(a): reference records and the conversions, and the tier now has TWO verification strengths

`LeanModels/Es/Convert.lean` + `Examples/es/convert/guards.lean` — **the
operations layer expressions are built from.** 4(b) is the AST walk itself
(expressions *and* statements, since one walk serves both), plus declaration
instantiation and body evaluation, which reaches the first score.

**Sized first: 191 numbered steps** — reference records 39, conversions 63,
the binary-operator applications 28, `IsLessThan` 38, `IsLooselyEqual` 23.

**INCH 1'S CONVERSION REFUSALS RETIRE.** `Value.lean` shipped `ToBoolean`
alone and said why: everything else can reach an object. Objects arrived at
inch 2 and `[[Call]]` at inch 3, so `ToPrimitive`, `ToNumber`, `ToString`,
`ToPropertyKey` and `ToObject` are real now, and `OrdinaryToPrimitive`'s
METHOD ORDER — `"string"` tries `toString` then `valueOf`, every other hint
the reverse — is pinned, because that order is what `[] + {}` depends on.

**The `Val`-equality discipline carried through, as instructed.**
`ToNumber(undefined)` is NaN, so a guard pins that the result is
`sameValue`-equal to itself and **`strictEquals`-UNEQUAL** to itself — the row
that shows the three equalities still matter after conversion, not just
before it.

### TWO VERIFICATION STRENGTHS, and naming which is which is the finding

`numberToString` (§6.1.6.1.20) splits inside one function:

* the **NaN / ±Infinity / ±0** arms are `rfl`-provable and carry `@[es_spec]`
  lemmas — including **`-0` rendering as `"0"`**, the row that separates
  `String(-0)` from `Object.is(-0, 0)`;
* the **exact-integer** arm is **NOT**. It goes through `Float.toInt64`,
  which is `@[extern]`, and `rfl`, `decide` AND `with_unfolding_all rfl` all
  fail on it **in both directions**, while `#guard` evaluates both.

**This is §L88's asymmetry again — `#guard` is a weaker oracle than `rfl` —
but with the OPPOSITE resolution, and the difference is the whole point.**
There a pure-Lean reformulation existed (`List Char`), so the law said move
the DEFINITION, and it moved. Here the obstruction is an extern primitive
with no kernel-reducible substitute short of the bit-level model, and
correctly-rounded decimal conversion is already scheduled and owned elsewhere
(`docs/family-architecture.md` §3.5.5 step 3). **Claiming a lemma that cannot
be proved would be worse than naming the gap; weakening the definition until
`String(42)` refuses would be worse than both.** So the gap is stated in both
the definition and the lemma file, and the tier's verification strength is now
a thing a reader can look up per primitive rather than assume uniform.

### The refusal boundary, narrower again

Every refusal added here is `environment`-class and names the realm:
`ToObject` on a primitive, property access or assignment on a primitive
(§6.2.5.4 step 3.a boxes it), and sloppy assignment to an undeclared name
(which creates a GLOBAL property — a **host facility**, the second time that
classification has been the right one). The `undefined`/`null` arm of
`ToObject` is complete and THROWS, as does `ToNumber`/`ToString` of a Symbol
and `ToPrimitive` of an object with neither method — all program outcomes in
`ρ`, catchable.

One deliberate `unsupported`-class refusal: `StringToNumber` outside the
decimal-integer fragment. The StringNumericLiteral grammar (hex, octal,
binary, exponents, `Infinity`) is its own sub-language and a rung; guessing a
number for `"0x10"` would be exactly the silent wrong answer this tier exists
not to emit, so `ToNumber("0x10")` refuses and a guard pins that it does.

**`IsLessThan` answers THREE values, not two** (§7.2.13, 38 steps): `none` for
NaN, modelled as `Option Bool` so it cannot be confused with `false` — which
is the confusion the spec's own three-valued answer exists to prevent, and
what makes all four relational operators false for NaN.

165 `#guard`s in the lane, 77 `@[es_spec]` lemmas, lint clean, five guard
files green. Non-vacuity checked three ways (`1 - "2"` claimed to
concatenate, `String(-0)` claimed `"-0"`, `ToNumber("0x10")` claimed 16).

Three mechanical notes for the next lane: **`try` is a reserved keyword**
(a local `rec try` does not parse); **`String.trim` now answers a
`String.Slice`** with no `.toList`, so char-list forms are both the portable
and the kernel-reducible choice; and a multi-line `SemM.refuseHost\n "msg"`
parses as two terms, not an application.

## 2026-08-22-es-4 — TWO CORRECTIONS ACCEPTED: `#guard` is NOT a kernel oracle, and the "no substitute" claim was wrong by ONE PROJECTION

Both came from the SoftFloat lane, both were **re-measured here before being
accepted**, and both refute something this lane wrote down.

### 1. `#guard` IS NOT A KERNEL ORACLE — and this lane said it was, three times

Measured here, on **one expression**:

    #guard (42.0 : Float).toInt64 == 42          -- PASSES  (exit 0)
    example : ((42.0:Float).toInt64 == 42) = true := by rfl     -- FAILS
    example : ((42.0:Float).toInt64 == 42) = true := by decide  -- FAILS

`#guard` runs through `evalExpr`, which honours `@[extern]`, so it passes
**identically whether a declaration reduces in the kernel or is opaque to
it**. A `#guard` over floats is attested by the **host FPU**, not by Lean.

**This retracts a phrase this lane repeated in §L82, §L88 and in
`harness/es/float_probe.lean`'s own docstring** — "every `#guard` is decided
by the KERNEL". It is not. The docstring was ours and is fixed in this
landing.

**The float finding itself SURVIVES, and the reason is worth stating rather
than glossed.** §L66's conclusion — core `Float` is kernel-reducible on the
pin — never rested on the guards: it rested on the `example … := by rfl`
lines, including `(0.1 : Float) + 0.2 = 0.30000000000000004`. Those ARE
kernel claims and they pass. The guards beside them were misdescribed, not
load-bearing. **A file that had used only `#guard` would have proved nothing
and looked identical**, which is the whole lesson, and it is why the guards
are kept as the DIFFERENTIAL half — host answer beside kernel answer — rather
than deleted.

### 2. "No kernel-reducible substitute short of the bit model" — wrong by one projection

Inch 4(a) recorded the exact-integer arm of `numberToString` as
guard-verified-only, and reasoned that no substitute existed "short of the
bit-level model." **The bit model IS core's `Float.Model`, one projection
away.** Two expressions change:

    n.toInt64   →   n.toModel.toInt64
    t.toFloat   →   Float.ofModel (Float.Model.ofInt64 t)

Re-checked here: `numberToString 42.0 = some "42"`, `-7.0`, `1000.0` and
`0.5 = none` all close by **`rfl`** now, where the extern pair closed under
neither `rfl` nor `decide`. **The "two verification strengths" note is
withdrawn — there is one.** Four lemmas that had been dropped as unprovable
are restored (81 `@[es_spec]` in the lane, from 77).

**What stays blocked is narrower and correctly stated**: RENDERING a
non-integer needs correctly-rounded shortest-round-trip decimal conversion,
`Float.toString` is opaque, and core ships no decimal printer — SoftFloat step
3. **DETECTING** a non-integer is now provable; only rendering one is not. The
earlier note conflated the two.

### The shape of both mistakes is the same, and it is worth naming

Each was a **negative claim made from a failed attempt** — "`rfl` failed, so
nothing can prove this" and "`#guard` passed, so the kernel accepted it."
Neither was measured against an alternative. The house law covers the first
direction (*a refusal path that is only designed is not one*); these are the
second: **an obstruction that is only encountered is not measured either.**
The SoftFloat lane measured both by replicating the function with core-only
imports and diffing the tactics, which is what this lane should have done
before writing "no substitute exists."

Still owed, and NOT done here (by-touch, and this touch was Convert/Spec/
float_probe): the `Core.Outcome` substrate replacement — see the next entry.

## 2026-08-22-es-5 — SUBSTRATE ADOPTION ON HOLD: this lane's `Halt` is the RICHER shape, and importing Core now would DELETE the ruling

Recorded so the next reader does not "helpfully" perform the import.

**HOLD, at the coordinator's correction.** The earlier note said adopt
`Core.Outcome` by import at the next substrate touch. The arch lane measured
otherwise: `Completion.lean`'s `inductive Halt α` has **Core's exact shape
with a RICHER payload**. Core's `Loud.unsupported` carries a bare `String`;
this lane's carries `(cause : EsRefusal) (message : String)` — **which IS the
`RefusalCause π` ruling implemented.** Importing today would replace a
structured cause with prose and silently undo §L88's own rule that a refusal
*carries its CAUSE as data, not as prose, so a scoreboard need not parse
English*.

**This is why the last landing flagged rather than guessed.** The reconciliation
was reported as "a real design step, not a mechanical import swap" — Core's own
text says a tier needing more causes adds its own `.except` layer rather than
extending the base, which is a third shape again. Guessing between three would
have been a coin flip on a semantics-visible field.

**What happens instead**: the rebuild lane is landing Core's `RefusalCause π`
plus a **subsuming** `Loud` payload, lifting THIS lane's shape as the closest
existing one. When it lands the adoption is a **substitution**, not a
redesign, and the two expected-empty gate theorems
(`es_never_undefined`, `es_never_orderDependent`) **transfer unchanged** —
they are stated about `esRefusal`, this tier's only cause constructor, not
about the base.

**Verified and unchanged by the hold**: this lane's base is structurally
correct against Core's — `ok | timeout | unsupported` ≅ `Except Loud`, and
**state-discarding on both loud arms**, which is Core's stated requirement. So
this is not one of the family's two wrong-base sites; it is the site the
correct shape is being lifted FROM.

Inch 4(b) proceeds on this lane's own `Halt`.

## 2026-08-23-es-1 — M2 INCH 4(b): the expression walk, and a clamp warning found a LIVE bug in this tier

`LeanModels/Es/Eval.lean` + `Examples/es/eval/guards.lean`. **198 `#guard`s in
the lane** (from 165), 81 `@[es_spec]` lemmas, six guard files, lint clean.

**Structurally recursive on FUEL, never `partial`** — the walk decreases fuel
at every subexpression, so the whole evaluator stays kernel-reducible. That
matters more since 2026-08-22-es-4: `#guard` is not a kernel oracle either, so
a `partial` evaluator would be a thing *nothing* could check.

**The inch-1 `Node` shape paid off.** Splitting a node's properties into
SCALARS and CHILDREN — done then to keep `Node` off the mutual-inductive
`deriving` path — is exactly the split an evaluator wants: `operator` and
`computed` are read as flags, `left`/`object`/`callee` are recursed into. A
decision taken for a compile-time reason turned out to be the semantic one.

**Two guards are worth more than the rest, and both are about what did NOT
run.** Short-circuiting is pinned with a right operand that THROWS if
evaluated (`false && <undeclared>`), so a pass proves the right operand's
world never existed — not that a pair was computed and one selected. And the
converse is pinned too (`true && <undeclared>` DOES throw), so the first set
is not passing merely because the right side is unreachable. `typeof
undeclared` is `"undefined"` while READING the same name throws — the one
operator that tolerates an unresolvable reference, and it only works because
`evalRef` builds the reference without reading it.

**One bug the guards caught immediately**: `typeof` routed *every* argument
through `evalRef`, so `typeof 1` refused as a "non-assignment-target". The
reference path exists only for the unresolvable-name case; everything else is
an ordinary value.

### THE CLAMP WARNING FOUND A LIVE INSTANCE HERE — `%` is WITHDRAWN

The SoftFloat lane's warning was preventive for `ToInt32`/`ToUint32` (this
tier has not built them). **It was not preventive for `%`.** `applyBinary`
carried

    | "%" => return .num (a - b * (a / b).toInt64.toFloat)

and `Float.toInt64` **CLAMPS** out of range — so a large quotient silently
produced a wrong remainder that **every in-range test would have passed**.
That is the flattering direction, which is the one this tier exists to refuse.
`%` now REFUSES, naming the reason, until it can be built on the exact-value
route.

**Both `toInt64` sites were audited, not just the reported one.**
`numberToString`'s is guarded by `n.abs < 1e15` — far inside Int64 — so the
clamp cannot fire there, which is why the model route is right for that arm
and wrong for a modular one. The distinction the warning draws is exactly the
distinction the guard makes.

### OWED — `ToInt32`/`ToUint32` on the exact-value route

Not built here; recorded so it cannot be built the wrong way later. ES's
`ToInt32`/`ToUint32` (§7.1.6/§7.1.7) reduce **modulo 2^32**, while
`Float.Model.toInt64` **clamps**, so the model route that fixed
`numberToString` is WRONG here. They go on SoftFloat's `toInt_eq_truncate`,
which is stated over the EXACT value precisely so a modular conversion can take
`mod 2^32` of the truncated exact integer without inheriting the clamp.

**Two out-of-range witnesses to pin in both directions** when they land:
`ToUint32(2^32 + 5) = 5` and `ToUint32(-1) = 4294967295`. An in-range-only
battery would pass under the clamped implementation, which is the whole point
of writing the witnesses down before the code.

Checked for SoftFloat's `INBOUND` entry and `toInt_eq_truncate` at
`92fcfcb`: **neither is on master yet**, so there is nothing to renumber or
close today. This entry is the standing obligation until it is.

---

## 2026-08-23-es-0 — M2 INCH 5: statements, declaration instantiation, and function bodies — a Script RUNS, and Core's `Outcome` was adopted in the same touch

`LeanModels/Es/{Object,Completion,Function,Spec,Eval}.lean` +
`Examples/es/statements/guards.lean` — **~690 new lines in `Eval.lean`, 44 new
`#guard`s (250 in the lane), 82 `@[es_spec]` lemmas.**

**SIZED FROM THE PINNED SPEC BEFORE BEING WRITTEN**, the discipline inches 2
and 3 set: the named abstract operations realized here carry **422 numbered
steps** in `ES2026` — `FunctionDeclarationInstantiation` 127,
`GlobalDeclarationInstantiation` 68, `CaseBlockEvaluation` 48,
`ForLoopEvaluation` 30, `BlockDeclarationInstantiation` 24,
`ScriptEvaluation` 20, `InstantiateOrdinaryFunctionExpression` 20 — against
inch 3's 204 and inch 2's 159. (`ForInOfLoopEvaluation`'s 18 are NOT counted:
`for…of` refuses, because it needs the iterator protocol.)

### THE INCH-3 REFUSAL IS RETIRED

`OrdinaryCallEvaluateBody` on an `ecmascript` body was inch 3's one boundary.
`Body.ecmascript` now carries its `Code` — the ingested `params` and `body`
Parse Nodes, per §10.2.3 steps 6-7 — and `Eval.evalCallBody` runs it.
Functions call, close over their environment, hoist, construct, and return.

### THE LAYERING THAT MADE IT POSSIBLE, and what it still costs

`Function.lean` cannot import `Eval.lean`, so the complete
`OrdinaryCallEvaluateBody` could not go where `[[Call]]` lives. The tier
already had the answer: `Ordinary.ordinaryGet` is the accessor-free fragment
and `Function.getV` is the complete §10.1.8.1. Inch 5 uses the SAME shape —
`Function.ordinaryCallEvaluateBody` stays the fragment and refuses;
`Eval.evalCallBody`/`callComplete`/`constructComplete` are complete and are
what the evaluator calls. `Examples/es/functions/guards.lean` now pins that
the fragment KEEPS refusing, which is what stops a caller that forgot to move
up from scoring a false pass.

**The price, stated rather than buried:** `Convert.ordinaryToPrimitive` and
`Function.getV` still reach `[[Call]]` through the OLD, builtin-only
`callValue`, because they sit below `Eval.lean`. So a user-defined
`valueOf`/`toString` reached by COERCION, and a user-defined GETTER, still
refuse. That is `2026-08-23-es-1`.

### THREE COMPLETION TYPES ARE THE MONAD'S, ONE IS THE RETURN VALUE

`ρ = Abrupt` already had all four constructors from inch 1, which turned out
to be the whole design: `return`, `break` and `continue` are RAISED, exactly
like `throw`, so no statement threads them by hand and none can be dropped by
forgetting a case. `SemM.catchRaise` — new, and the only new operator on the
monad — is where each is absorbed: `evalCallBody` takes the `return`,
`runLoop` takes an unlabelled `break`/`continue`, `try` takes the `throw` and
RE-RAISES everything else, which is why `return` crosses a `try`.

A refusal and a timeout live BELOW `ExceptT ρ`, so `catchRaise` cannot see
one. A `try` that could swallow a refusal would let an unmodeled construct
score as a pass; `Spec.lean`'s `rfl` pins that it cannot.

### `empty` IS NOT `undefined`, and the corpus says so

`evalStmt` answers `Option Val` — the completion VALUE, `none` for the spec's
`empty`. Collapsing the two at the leaves would make
`eval("1; if (true) { }")` answer `1`; §14.6.2 step 5 runs
`UpdateEmpty(…, undefined)` and the answer is `undefined`. That is exactly
what `Examples/es/test262/if_cptn.json` asserts, and it is guarded.

### CORE'S `Outcome` WAS ADOPTED IN THE SAME TOUCH

Per the coordinator's instruction, the substrate was touched once. `EsRefusal
:= RefusalCause EsDetail`, `SemM W ρ := SemMWith W ρ EsDetail Unit`; the local
`RefusalCause`, `Halt`, its `bind` and its `Monad` instance are DELETED, not
wrapped.

**The 7-site price was right, and incomplete.** The destructuring sites were
exactly 7, all in the guard helpers — the concentration argument held. But the
number was quoted as the price of the adoption, and it was not: it counted
only `.unsupported`, missing 22 CONSTRUCTION sites (`Halt.ok` ×7,
`Halt.timeout` ×13, `Halt.unsupported` ×2) across five modules. The true
mechanical surface was ~30. **A price grepped for one constructor is not a
price for the type.**

### TWO SILENT WRONG ANSWERS, FOUND BY READING THE SPEC AGAINST THE MODEL

The inch was written, green, committed and QUEUED FOR ITS TRIAD before this
was noticed. It was found by re-reading §14.7.4.4 to check a docstring claim,
not by any test failing — and both defects were the kind this lane exists to
prevent, because they answer the wrong thing quietly instead of refusing.

**One.** `Abrupt.brk`/`cont` carried no `[[Value]]`, and `Completion.lean`
said so in as many words: "`empty` is the only case that arises for them in
the language core". §14.2.2 step 3 refutes it — `UpdateEmpty(s, sl)` applies
to an ABRUPT `s`, so the `break` out of `{ 5; break; }` leaves carrying the
`5`, and §14.7.4.4 step 3.c hands that to the loop. `while (true) { 5; break;
}` completed `empty` where the language says `5`.

**Two.** `V` starts at ***undefined***, not `empty` (§14.7.4.4 step 1;
§14.12.4 step 2 says the same for `switch`). The loop seeded it with `empty`,
so `eval("1; while (false);")` answered `1` where the language says
`undefined`.

Both are exactly what test262's `-cptn` family tests, so the rung-0 slice
would have scored them as failures — or worse, as passes on the tests that do
not look. **The ticket was CANCELLED rather than spent validating a tree with
a known wrong answer in it**, the fix landed, and five guards now pin the
corrected clauses. `Abrupt.updateEmpty` is no longer the identity.

**The lesson is the one the lane keeps relearning: a docstring that argues a
field is unnecessary is a claim, and a claim is worth exactly one re-read of
the clause it is about.** The same shape as `NewFunctionEnvironment` in inch
3 — except that one was caught by three guards failing, and this one was
caught only because a docstring was checked. The missing guards are the real
defect, and they are written now.

### WHAT REFUSES, DELIBERATELY

Each is a guard, so it fails the day the boundary moves: the `arguments`
object (needs `%Object.prototype%` and `@@iterator`), a non-simple parameter
list, generators and `async`, `for…of`/`for…in`, labelled jumps, destructuring
in a declaration or a `catch` parameter, and any node outside the pinned
vocabulary.

---

## 2026-08-23-es-1 — the coercion/accessor cycle: move `ToPrimitive` and `[[Get]]`'s accessor walk into the evaluator's mutual block

ECMA-262's real dependency knot is `ToPrimitive → Call → EvaluateBody →
Evaluation → ToPrimitive`, and Lean's one-file `mutual` is where a knot has to
go. Today `Convert.ordinaryToPrimitive` and `Function.getV` sit below
`Eval.lean` and reach the builtin-only `callValue`, so a user-defined
`valueOf`/`toString`/getter refuses.

Two shapes were considered and the cheap one is worse: parameterizing the
conversion chain by a caller threads an extra argument through every
signature in `Convert.lean`. The honest fix is to merge the knot — the
coercion chain, the call chain and the evaluator — into one `mutual`, which is
what the spec itself is. It is a restructuring, not a semantics gap.

---

## 2026-08-23-es-2 — the Directive Prologue (§11.2.2), and non-strict `this`

Every function this tier creates has `[[Strict]] = true`, inherited from inch
3's `FuncData` default and now also written by `instantiateFunction`. The
prologue is not read, so `"use strict"` is neither required nor detected.

It is observable through `this`: `OrdinaryCallBindThis`'s sloppy arm needs the
global object and the wrapper intrinsics, so a non-strict function called bare
REFUSES where it should see the global object. The refusal is loud, so nothing
scores a false pass — but half of test262 runs each test in both modes, and
the sloppy half cannot be scored until this lands.

---

## 2026-08-23-es-3 — the global object, and §16.1.7's `CreateGlobalVarBinding`

`GlobalDeclarationInstantiation` puts `var` names on the global OBJECT, so
`var x` at top level makes `globalThis.x`. This tier has no global object, so
`instantiateDeclarations` puts them in the declarative record for both §16.1.7
and §10.2.11. The observable that separates them is `this.x` at top level, and
`resolveThisBinding` already refuses without the global object — so no test
can reach the difference and score a pass. It lands with the realm (inch 6).

---

## 2026-08-23-es-4 — the corpora are BACK, the ecma262 pin was RECOVERED not guessed, and `esmeta` was the QUIET half of the `rev()` defect

All four corpora are on disk again and the census REGENERATES: `ecma262`
`d89c03f2db8a597bc915b363a6518d0cc8acdbc0` (2026-07-27), `test262`
`3655e7464de3d52643ecddd4b5f9f4f3e7f62398` (2026-08-10), `engine262`
`c7939eaf0bcfa292b4a8872e78f4c221bc2477a2` (2026-08-09), plus `acorn` for the
frontend probe.

### THE ecma262 PIN WAS NEVER RECORDED, AND IT WAS RECOVERED RATHER THAN GUESSED

`docs/es262-census.json` carried `"ecma262": ""` — the exact artifact `rev()`'s
own docstring quotes as the trap it was hardened against. Deriving a pin from
the HTML's date header would have been a guess with provenance attached.
Instead it was recovered and then CHECKED:

1. `git ls-remote tc39/ecma262` carries an annotated tag **`es2026-errata`** —
   the same token `docs/es-edition.json` already records as `spec_revision` —
   dereferencing to `d89c03f2…`.
2. That commit's `spec.html` hashes to `032ecc74…`, **byte-identical** to
   `spec_sha256`: it is the file the census actually read.
3. `--edition docs/es-edition.json` re-ran `check_edition` against the checkout
   and passed.

**It is not a pin with a stated provenance; it is the commit that reproduces the
recorded hash.**

### THE REPRODUCTION

`test262` 26/26 keys identical, `engine262` 6/6, `frontend` 14/14 (18,114
attempted / 14,045 parsed / 4,069 rejected / **66 node types**, 0 runner
errors), `spec` 21/23 with `core_slice` exact. Three leaves in the whole
artifact differed, all three intended: `sources.ecma262` (was `""`),
`spec.path_name` (the input's filename), and `spec.esmeta`.

### `esmeta` WAS A MEASUREMENT OF AN ABSENT REPO — and it is now HARDENED

Stored: `{ignore_entries: null, ignore_file_present: false, workflows: []}`.
Actual at the pinned commit: **11 ignore entries and three CI workflows**
(`esmeta-installer`, `esmeta-typecheck.yml`, `esmeta-yetcheck.yml`).

With only a bare fetched HTML on disk there is no `esmeta-ignore.json` and no
`.github/workflows`, so the probe recorded **"ECMA-262 has no ESMeta
integration"** when the opposite is true. **This is the same defect class
`rev()` was hardened against, in a field nobody hardened** — a `false`/`null`
that reads cleaner than "this measurement has no state". `rev()` refusing was
the LOUD half; this was the quiet half that got through.

It is worse than a wrong number: the charter cites TC39's per-PR extractor as
the premise the whole lane rests on, and this row looked like the corroboration
for it. **The conclusion was right and the census was not the evidence.**

`census_spec` now emits `{"measured": false, "why": …}` when the spec is not in
a checkout. It is a FIELD and not a `Refusal` because `--spec` legitimately
takes an extracted `spec.html` (the module header documents `git show
es2026:spec.html > f && … --spec f`), and that run should still census the
clauses it CAN see — what it must not do is emit a `false` that reads like a
measurement.

### THE STANDING RULE

**A scoreboard number taken without its corpus present is not a weaker number,
it is a number about nothing.** Before any scoreboard inch: corpora on disk,
pins in `sources`, and a `--compare` that reproduces.

---

## 2026-08-23-es-5 — the audit's other two rows: a docstring that outlived its code, and a lint blind to legal Lean

From `docs/quality-audit-2026-08-23.md` (`00fe2dc`), "## es".

### TWO `ADOPTION NOTE`s ASSERTED A CORE ABSENCE CORE HAD ALREADY CONTRADICTED

`LeanModels/Es/Completion.lean` said, twice, that `LeanModels/Core/` "does not
yet export" a `SemM` / `RefusalCause` and that this file therefore defines the
shape locally. Both were false as of `eeeb1fd`, and — the sharper part —
**both survived the very commit that falsified them**: the adoption imports
Core and instantiates `SemMWith`/`RefusalCause`, so the prose contradicted its
own module, forty lines above the code doing the opposite.

This is the third instance in two days of one law: **a docstring is a claim,
and a claim outlives the code it described unless something checks it.** The
first was `NewFunctionEnvironment` (caught by three guards failing), the second
`Abrupt.updateEmpty`'s "empty is the only case that arises" (caught only
because the clause was re-read), and this one was caught by neither — it took
an external audit. The guards check the code; nothing checks the prose.

### THE LINT COULD NOT SEE A ONE-LINE DOC COMMENT

`harness/es_lean_lint.py`'s scan closed a doc comment with
`rstrip().endswith("-/")`. `/-- doc -/ def f := 1` is legal Lean and closes on
the OPENING line with the declaration trailing it, so the scan missed the close
entirely and ran on to the next line that happened to end in `-/` — **reporting
an attachment verdict about a different part of the file.**

The fix finds `-/` anywhere on the line and, when text trails it, attaches to
THAT. Three self-test cases pin it: the legal one-liner is not flagged,
`/-- doc -/ #guard` is, and — the one that shows the real damage — a one-liner
followed by a genuinely misattached spanning comment now reports line 2 rather
than swallowing it.

**Both rows are the lane's own instruments failing quietly rather than loudly**,
which is the failure mode the whole tier is built to refuse.

---

## 2026-08-24-es-1 — the data-literal inch: object and array literals, `UpdateExpression`, and the Array exotic object

`LeanModels/Es/{Object,Ordinary,Eval}.lean` + `Examples/es/literals/guards.lean` —
**35 new `#guard`s (290 in the lane).**

**§9.0 ledger: 38/66 node kinds stated; 0 test262 scored.** In-vocabulary tests
go **2,869 -> 4,118**, matching the census's predicted +1,249 exactly.

**SIZED FROM THE PINNED SPEC BEFORE BEING WRITTEN: 195 numbered steps** —
PropertyDefinitionEvaluation 35, ArraySetLength 34, Array
Initializer/ArrayAccumulation 33, the four Update operators 40, Array
[[DefineOwnProperty]] 18, Array Init Evaluation 12, Object Init Evaluation 11,
ArrayCreate 7, CreateDataPropertyOrThrow 3, CreateDataProperty 2. Against inch
5's 422 and inch 3's 204.

### THE CENSUS REDIRECTED THE INCH, and that is the finding

The discriminating decision was expected to be `ObjectExpression`'s value
model — property order and duplicate keys. **It was already correct.**
`Obj.put` replaces IN PLACE (so a duplicate key keeps its first slot and takes
its last value) and `ordinaryOwnPropertyKeys` (§10.1.11.1) already sorted
integer indices ahead of creation-ordered strings, both written at inch 2 for
their own reasons.

So the object risk was never REPRESENTATION, it was **DISCIPLINE**: an
evaluator that appends to `props` directly bypasses a model that is already
right. Every property therefore routes through `CreateDataPropertyOrThrow` ->
`[[DefineOwnProperty]]`, without exception, and the four-way guard is what
holds it there.

**A discriminating decision can live in discipline rather than in
representation** — and a census is what tells you which.

### THE OPEN VALUE MODEL WAS THE *ARRAY*

`Obj` had no exotic marker, so an Array's live `length` was unrepresentable.
Added `exotic : Option ExoticKind`, mirroring `callable : Option FuncData` —
the tier's own precedent for "make it a field test, not a guess" (§7.2.3) —
plus §10.4.2.1's `[[DefineOwnProperty]]`, §10.4.2.4's `ArraySetLength`,
`ArrayCreate`, and an `esDefineOwnProperty` dispatcher that the `[[Set]]` path
now goes through so `a[5] = 99` reaches the array's own method.

### NO Float->Nat CONVERSION APPEARS ANYWHERE IN IT

The first shape converted `length` through `ToUint32` into a `Nat` and needed
`Int64.toInt`/`Int.toNat`, two conversions this lane has never exercised.
Indices arrive from `PropKey.arrayIndex?` as `Nat`, lengths live as `Float`,
and `Nat.toFloat` is total and exact over `[0, 2^32)` — so every comparison
happens in `Float` and the conversion is simply never made. **A conversion not
made is a conversion that cannot clamp**, which is the inch-4 `%` defect
answered structurally rather than by a guard.

`isExactUint32` is a ROUND TRIP through `Float.Model`, not a range check on a
converted value: `n.toInt64` is `@[extern]` and SATURATES, so `1e30` becomes
`2^63 - 1` and passes a naive range test. Guarded.

### THE THREE DISCRIMINATORS, EACH ORACLE-VERIFIED IN SOURCE SPELLING

Every expected value was read off a running engine BEFORE the Lean was
written, never derived from the prose.

* **Object order + duplicates.** `{b:1, 2:2, 1:3, a:4, b:5}` -> keys
  `["1","2","b","a"]`, `b === 5`. Fails four ways: append-no-sort gives
  `["b","2","1","a","b"]`; insertion-order-with-dedupe gives `["b","2","1","a"]`;
  index-sort-with-dedupe-to-end gives `["1","2","a","b"]`.
* **Elision.** `[1, , 3]` has `length` 3 and **no own property at 1**.
  Dropping the hole closes the array to `[1,3]`; filling it with `undefined`
  invents a property. `Node.kidsOpt` keeps the hole that `Node.kids` drops.
* **`ToNumeric` ordering.** `s = "3"; s++` answers the **Number** `3`.
  §13.4.3.1 converts BEFORE choosing the answer, so saving the old value and
  converting afterwards returns `"3"` — wrong in a way no numeric test catches.

Plus both directions of the live `length`: `a[5] = 99` grows it to 6, and
`a.length = 1` DELETES index 1 rather than renumbering.

### WHAT REFUSES

Spread in either literal (iterator protocol / `CopyDataProperties`), get/set
in an object literal (`2026-08-23-es-1`), shorthand methods (`[[HomeObject]]`,
the class inch), BigInt increment, and array truncation across a
non-configurable element — that last one unreachable in this tier, and checked
rather than assumed.

---

## 2026-08-24-es-2 — the tier's FIRST declared divergence: sloppy-mode `this` answers `undefined`, silently

`docs/es-declared-divergences.json` (new, `declared-divergences-0.1`), gated by
a paired guard in `Examples/es/statements/guards.lean`.

**§9.0 gains its third quantity: `declared-divergences: 1`.**

### THE FINDING

`instantiateFunction` creates every non-arrow function with
`[[ThisMode]] = strict`, because the Directive Prologue (§11.2.2) is not read.
In NON-STRICT code the language says `[[ThisMode]]` is `global`, and
`OrdinaryCallBindThis` (§10.2.1.2 steps 6.a-6.c) replaces an `undefined`
thisArgument with the global object. So `function f(){ return this }; f()`
answers **globalThis** in the language and **`undefined`** in this tier.

### WHY IT IS A DIVERGENCE AND NOT A GAP — the part worth recording

**The refusal for sloppy `this` already exists in `ordinaryCallBindThis`, and
it is correct.** It is simply UNREACHABLE, because no code path ever selects
`.global`. This lane has been writing refusals as boundaries all week; this is
the case where writing one was not enough, because **an unreachable refusal
guards nothing.** The model answers, and answers differently from the
language, without saying so.

That is exactly §5.0a's distinction: not a `DIVERGE` verdict (nobody was
surprised), but a decision the tier has taken and can state. `DIVERGE` stays
zero.

### GATED IN BOTH DIRECTIONS

* `es_div_1_still_divergent` — fails the day the prologue is read, so the
  declaration cannot go stale and read as diligence.
* `es_div_1_has_not_widened` — the `.global` arm must keep REFUSING, so that
  when it becomes reachable this turns into a loud boundary rather than a
  second silent answer.

### RETIREMENT CONDITION, and it is not "when someone models it"

Parse the Directive Prologue and let `[[ThisMode]]` be `global` for non-strict
code. The existing refusal becomes reachable at that moment and the debt
converts to a boundary. Tracked as `2026-08-23-es-2`.

**The register is the instrument this lane was missing.** Every earlier
boundary went into prose or a refusal message; this one could go into neither,
because the tier answers. It is the first row, and the search that produced it
should be repeated per inch rather than per audit.

---

## 2026-08-24-es-3 — a RED triad that measured nothing: the gate list is `;`-separated and shredded an inline validator into five false gates

`harness/es_register_check.py` (new), `docs/es-declared-divergences.json`
(canonical schema).

### WHAT HAPPENED

`2026-08-24-es-2`'s ticket passed `--gates` containing

    python3 -c "import json;d=json.load(...);assert ...;print(...)"

`tools/triad.sh` splits `--gates` on `;` **without respecting quoting**, so the
Python semicolons split one command into FIVE shell fragments:

    === gate: python3 -c "import json ===                          GATE FAILED
    === gate: d=json.load(open('docs/es-declared-divergences.json')) ===  GATE FAILED
    === gate: assert d['schema']=='declared-divergences-0.1' ===   GATE FAILED
    === gate: assert all(set(r)>={...} for r in d['rows']) ===     GATE FAILED
    === gate: print('...' % len(d['rows']))" ===                   GATE FAILED

The build was GREEN; the triad went RED on five gates.

### THE TWO SHAPES, and the second is the worse one

**One — a gate spec is CODE.** A `;`-separated gate list turns any inline
multi-line or semicolon-bearing command into N false gates. Either the runner
refuses a fragment that cannot parse as a command, or the spec forbids inline
multi-line code. Until one of those lands, **every gate must be a single
command with no internal `;`** — which in practice means a FILE.

**Two — the register was never validated.** Five `GATE FAILED` lines about a
JSON file, and not one of them read the JSON file. This is the
**unexercised-gate family**: a gate that fails for a reason unrelated to its
subject tells you nothing about its subject, and a red that looks like
diligence is worse than no gate, because it will be "fixed" by making the red
go away. The register had been sitting unvalidated behind five failures
*about* it.

### THE FIX, and why the checker self-tests in seven directions

`harness/es_register_check.py`, one file, one command, no semicolons. It
validates §5.0a's fields plus the ruling's `kind` and `guards`, refuses a
WAITING retirement condition (§9), enforces the paired-guard law by requiring
at least two guards, and — the part that closes this incident's own hole —
**checks that every guard the register NAMES is actually DEFINED in the file
it names.** A register that cites a guard nobody wrote is the same
unexercised-gate failure one level up.

`--self-test` exercises **both directions** (MEAS-42): one accept and seven
refusals. A gate that has only ever been seen to pass is exactly what produced
this entry.

### IT IS TEMPORARY BY CONSTRUCTION

`harness/divergence_register.py` is the canonical checker. When it merges this
file is deleted and the gate becomes `python3 harness/divergence_register.py`.
**MEAS-28 applies to inline validators too** — a second copy of a shared
instrument is the duplication that law polices — so a lane-local file is the
smaller wrong, and only until the shared one lands.

---

## 2026-08-24-sv-4 — INBOUND FROM THE SV LANE: ES lane's to conform its divergence register

*Filed by the SV lane. Id kept in the SV namespace so this lane mints
nothing in yours.*

`harness/divergence_register.py` — the shared checker, now merged — **fails
on `docs/es-declared-divergences.json` and on nothing else.** It was red in
an SV tenure (`sv 16951`, 2026-08-24) whose own content was green, which is
how this lane found it:

```
3 PROBLEM(S):
  docs/es-declared-divergences.json: missing top-level field 'probe'
  docs/es-declared-divergences.json: schema is 'declared-divergences-0.1',
    expected 'declared-divergences-1'
  docs/es-declared-divergences.json: row es-div-1 inherited_from is blank;
    use null to mean ORIGINATED here
  python  2 row(s), 4/4 guards held
  sv      1 row(s), 2/2 guards held
```

**This is not a checker defect and the SV lane is not proposing a checker
change.** The ES file is the **pre-ruling shape** — it was filed as the
DATA half before §5.0a's amendment split DATA / CHECKER / PROBE, and the
checker is correctly refusing a file that predates the schema it now
enforces. Relaxing the checker to accept it would un-gate a real
non-conformance, which is the opposite of what the register is for.

**Three edits, all in the ES lane's own file:**

1. `schema` → `"declared-divergences-1"`.
2. add top-level `"probe"` naming the ES probe. Your guards are recorded as
   `"Examples/es/statements/guards.lean: es_div_1_still_divergent"` — a
   **file-qualified** name where `python` and `sv` use bare names, so the
   probe field is probably that Lean file. **The SV lane cannot tell
   whether the checker resolves a Lean-guard probe the way it resolves a
   Python one**, and did not guess: if it does not, that is a genuine
   checker gap worth raising with pyc rather than working around.
3. `inherited_from: ""` → `null`. The checker distinguishes them on purpose
   — §5.0a says a **blank claims the divergence ORIGINATED here**, which is
   the heavier claim, and an empty string reads as neither.

**Why this lane did not just fix it.** Two of the three are mechanical, but
the `probe` field is not: it asserts *this file measures that row*, and
this lane cannot verify an ES probe measures ES semantics. Filing a
provenance claim on another tier's behalf is the same defect the registers
exist to prevent.

**Meanwhile the SV lane has dropped `divergence_register.py` from its own
`--gates`** — it was added voluntarily and is not in any class floor — and
kept its own `harness/sv_divergence_probe.py`, which passes. Stated plainly
rather than quietly, because dropping a red gate is exactly the move that
needs to be visible: it is red on your data, not on this lane's change, and
it goes back into SV's gates the day this file conforms.

**RESOLVED at `133e87d`** (this lane), before this entry was read — the schema
string went to `declared-divergences-1` and `inherited_from` to `null`.

**On the `probe` field: it is deliberately ABSENT, and the checker no longer
asks for it.** pyc's extension landed the DECLARATION SHAPE — with no `probe`
key each guard is `<path>: <name>` naming a Lean declaration and THE BUILD IS
THE RUN, since a `#guard` that stops holding fails the tenure. The shared
checker verifies the declarations still exist, which is the half a green build
cannot see. `python3 harness/divergence_register.py` now reports
`es 1 row(s), 2/2 guards held` with zero warnings.

**The lesson this lane takes from being the blocker**: a per-tier DATA file
consumed by a SHARED checker is a fleet-wide dependency. Mine sat
un-normalized for a day because it was filed as lane-local housekeeping, and
the moment a lane wired the checker into its gates my stale string became
their red. Shared-instrument data needs the urgency of shared-instrument code.
Thank you for the id in your own namespace — that convention worked.

## 2026-08-24-es-4 — object destructuring: one clause for both forms, and a latent `BoundNames` bug the plan surfaced

`LeanModels/Es/Eval.lean` + `Examples/es/destructuring/guards.lean` — **22 new
`#guard`s (312 in the lane).**

**§9.0: 40/66 node kinds stated; 0 test262 scored; declared-divergences: 1.**
In-vocabulary **4,118 -> 5,154**. Census predicted **+1,036**; actual **+1,036**.

**SIZED FROM THE PINNED SPEC BEFORE BEING WRITTEN: 149 steps** —
DestructuringAssignmentEvaluation 44, BindingInitialization 22,
PropertyDestructuringAssignmentEvaluation 17, KeyedBindingInitialization 16,
KeyedDestructuringAssignmentEvaluation 16, CopyDataProperties 14,
PropertyBindingInitialization 9, RestBindingInitialization 5,
RestDestructuringAssignmentEvaluation 4, RequireObjectCoercible 2.

### ONE CLAUSE FOR TWO OPERATIONS

§8.6.2 `BindingInitialization` and §13.15.5 `DestructuringAssignmentEvaluation`
walk the same patterns and disagree about exactly ONE thing: what happens at a
leaf. `bindPattern` takes `form : Option Bool` — `none` assignment
(`PutValue`), `some true` `var` (`SetMutableBinding`), `some false` lexical
(`InitializeReferencedBinding`) — and nothing else differs. The spec writes
them twice because it has no way to abstract the leaf.

### A LATENT BUG THE PLAN SURFACED, BEFORE ANY CODE RAN

`Node.declaredNames` (inch 5) collected every `Identifier` under a
declaration. Over a PATTERN that is wrong twice:

* `var {a: x} = o` binds `x` — a Property's KEY is not bound. Collecting it
  hoists `a` as well, and a hoisted `a` initialized to `undefined` turns what
  should be a `ReferenceError` into a silent `undefined`.
* `var {a = b} = o` binds `a` and READS `b`. Collecting the
  `AssignmentPattern`'s default hoists `b` the same way.

Both were invisible until patterns existed to exercise them — inch 5 wrote a
correct-looking `BoundNames` for a language subset with no patterns in it.
Fixed by skipping `key` and `right` in `declaredNamesOfChildren`, and both
directions are guarded.

### THE TWO ORACLE DISCRIMINATORS FALL OUT OF ONE ARM

* `{a = 5} = {a: undefined}` yields **5** and `{a = 5} = {a: null}` yields
  **null**: §8.6.3 step 2 tests the FETCHED value, never `HasProperty`.
* The initializer is evaluated only inside that branch, so a present property
  never runs it — visible only through a side effect.

Writing the arm as "test the fetched value, evaluate the initializer inside
the branch" gets both right; writing it as "look up the default, then override
if absent" gets both wrong. One arm, two guards.

### A MEASUREMENT BUG IN THIS LANE'S OWN LEDGER INSTRUMENT

The kinds count is produced by scraping `| .kind =>` arms out of `Eval.lean`.
`bindPattern` introduced a match whose arms include `arrayPattern` — **which
REFUSES** — and the scrape counted it as stated, reporting 42/66 and 6,634
tests. Both were false. The honest count is against the COMMITTED baseline
plus the kinds actually implemented: **40/66, 5,154**.

**A scrape that cannot tell an implementing arm from a refusing arm is not a
coverage instrument.** It has been right until now only because every previous
inch happened to implement every arm it added. Recorded rather than fixed in
passing: the ledger number needs a real instrument, and that is its own inch.

### WHAT REFUSES

`ArrayPattern` (needs `GetIterator`, §7.4 — the iterator inch), and therefore
`RestElement` in array position: 959 slice tests use the two together.
`RestElement` in OBJECT position works. Object rest from a primitive
(`var {...r} = "ab"`) refuses — it needs `ToObject` and the String wrapper.

---

## 2026-08-24-es-5 — the ledger number was wrong, and the instrument that says so

`harness/es_coverage.py` (new). **§9.0 was `40/66`. It is `33/66`.**

    §9.0  node kinds stated: 33/66  (partial: 8, refusing: 2, absent: 23)

### WHY THE OLD NUMBER WAS NOT A MEASUREMENT

It came from scraping `| .kind =>` arms out of `Eval.lean` and counting them.
That counts an arm whose entire body is `SemM.refuseConstruct "…"` exactly the
same as one that evaluates. It had been right until 2026-08-24 **only because
every inch until then happened to implement every arm it added** — the measure
was ACCIDENTALLY correct, which is worse than wrong, because nothing announces
the day the accident ends. `bindPattern` ended it by adding a refusing
`arrayPattern` arm, and the scrape reported 42/66 and 6,634 in-vocabulary
tests where the truth was 40 and 5,154.

### THE DISTINCTION THAT MAKES THE NEW ONE SOUND

Not every refusal in an arm is a boundary. `internal: malformed IfStatement`
sits inside a **fully implemented** `if` — it guards against an AST that
cannot occur. Reading it as "`if` is unimplemented" would be as wrong as the
bug being fixed. So refusals split by message: `internal:` says nothing about
coverage; anything else is a boundary. Then

    REFUSING   the whole body is one boundary refusal
    PARTIAL    real evaluation AND a boundary refusal somewhere
    STATED     real evaluation, at most `internal:` guards

**PARTIAL is not in the numerator.** `objectExpression` evaluates `init`
properties and refuses get/set; counting it as stated claims a construct the
tier half-evaluates, and counting it absent denies work that is there. It
rides beside the number, the same argument §5.0a makes for declared
divergences.

### THREE BUGS IN THE INSTRUMENT ITSELF, ALL FOUND BY ITS OWN OUTPUT

Recorded because a measurement tool's own defects are the ones nothing else
catches:

1. **Under-counting the mirror of the original bug.** Five kinds — `program`,
   `variableDeclarator`, `catchClause`, `switchCase`, `literal` — are handled
   by DEDICATED CLAUSES with no `| .kind =>` to read, and the first version
   called them absent. Fixed with a `DEDICATED` table that names the handling
   definition and **verifies it exists**: delete `evalCatchClause` and this
   file goes red rather than quietly keeping the kind in the numerator. A
   hand-maintained exemption list nothing checks is the discipline-not-
   instrument shape MEAS-28 forbids.
2. **Nested arms were invisible.** `objectPattern` matches `| some .property =>`
   and `| some .restElement =>` INSIDE its own body, and the scan jumped past
   the body, reporting both absent. Same class of error as the original, in
   the opposite direction.
3. **It counted other inductives' constructors as node kinds** — `| .null |
   .undef =>` over `Val` — and reported DRIFT on them. Now filtered against
   `Ast.lean`'s vocabulary, so the reader is never told `undef` is an
   unhandled node.

Aggregation is order-independent by construction: a kind with arms in several
matches is `refusing` only if all refuse, `partial` if ANY arm carries a
boundary, else `stated`. The first version took "strongest wins" and the
answer depended on file order.

`--self-test` exercises all five classifier rules plus three REAL arms whose
verdicts this lane knows by hand (`arrayPattern` refusing, `objectExpression`
partial, `emptyStatement` stated), so the file is pinned against the code and
not only against fixtures.

### WHAT THE HONEST NUMBER SAYS

33 stated, 8 partial (`objectPattern`, `property`, `assignmentExpression`,
`unaryExpression`, `objectExpression`, `arrayExpression`, `updateExpression`,
`logicalExpression` — each evaluating its common case and refusing a named
corner), 2 refusing (`arrayPattern`, `spreadElement` — both the iterator
inch), 23 absent.

**Every §9.0 figure this lane reported before today was produced by the
scrape.** The reach numbers (+1,249, +1,036) were computed from an explicit
kind SET rather than the scrape and are unaffected; the `N/66` figures were
not, and 40/66 should be read as 33/66 + 8 partial.

---

## 2026-08-25-es-1 — the scoreboard: `test262 scored` leaves 0

`LeanModels/Es/Score.lean` (`es-score`), `harness/es_score.py`,
`harness/es_score_corpus.py`, `harness/es_scoreboard.py`,
`harness/es/slice_probe.mjs`, `docs/es-scoreboard-corpus.json`.

**§9.0: 33/66 stated + 8 partial; vocabulary 5,464; runnable 1,816;
test262 scored — first real number this run; declared-divergences 1.**

### THE REALM WAS NOT THE PREREQUISITE. THREE BINDINGS WERE.

The realm inch was priced and then withdrawn by its own census. Measuring the
prelude's intrinsic surface gave six property paths, not six intrinsics — and
then **every one of them turned out to sit in failure formatting**:

    formatIdentityFreeValue   JSON.stringify, String()
    formatSimpleValue         String(), Object.prototype
    assert.compareArray       String()
    compareArray.format       Array.prototype.map

`assert(mustBeTrue, message)` opens `if (mustBeTrue === true) { return; }`, and
`assert.sameValue` opens with the same early return over `_isSameValue`, which
uses only `===`, `1/a` and `a !== a`. `sta.js` needs nothing at all.
**A passing test touches no intrinsic.** What was missing was that
`undefined`, `NaN` and `Infinity` are properties of the global object this
tier does not have — three bindings, added as immutable declarative ones
(§19.1's attributes, reproduced for every observable the tier can reach).

This corrected the lane's own "decisive fact" from the previous entry: *no
test can reach a verdict without those four intrinsics* was wrong. No test can
reach a FAILURE MESSAGE without them.

### THE POPULATION IS NAMED, AND PINNED BY CONTENT

`docs/es-scoreboard-corpus.json` carries the rule as data, the test262 commit,
the count, and a **digest over content** — sha256 of the sorted
`<relpath> <sha256>` lines. Re-derive and it matches or the corpus moved.
1,816 admitted; rejected 8,505 kind-outside-the-evaluator, 4,745
out-of-slice-flag, 4,201 not-parsed, 3,415 needs-an-intrinsic, 311
negative-test. **The states sum to 22,993**, the file count.

The full list is not in `docs/`: it is ~1,800 lines derivable from the rule
plus the pinned commit, and a digest anyone can recompute is a stronger pin
than a list nobody diffs.

### THE ZEROES ARE NOT THE SAME ZERO

Eleven states, and they sum: `passed`, `failed`, `refused-construct`,
`refused-intrinsic`, `refused-host`, `timeout`, `threw-other`,
`prelude-failed`, `not-parsed`, `not-ingested`, `runner-error`. The three ES
refusal causes stay apart because §3.6 says so; `prelude-failed` is its own
state because a broken prelude would otherwise print 1,816 identical
refusals and look like a frontier instead of one file.

`harness/es_score.py` re-derives the driver's summary from the per-test lines
by a different program and **compares them line for line** — agreement is
evidence, disagreement is a defect in one of the two. The first non-pass is
printed verbatim IN LOG ORDER, because `sort -u` answers "which distinct
outcomes exist" and a reader asks "what went wrong first".

### THE FIRST TENURE WENT GATES-RED, AND THE REFUSAL WAS THE INSTRUMENT'S OWN

Build GREEN, corpus verified (1,816, digest unchanged), and then
`es_scoreboard.py` refused: **`.lake/build/bin/es-score is not built`.**

The cause was the lakefile. `es-score` is a new `lean_exe` and is NOT in
`defaultTargets`, so `lake build <all default targets>` — which is what a
tenure runs — never built it. Adding it to `defaultTargets` would fix it by
making **every other lane's triad** build this tier's scoreboard binary: a
fleet-wide cost for one lane's gate, which is the wrong place to put it. The
gate builds what the gate needs.

`lake exe` builds-and-runs in one step and is what the C lane's torture gate
uses, but it writes build progress to STDOUT — the same stream the per-test
lines travel on — and the scorer would then refuse a non-data line correctly
and unhelpfully. So: `lake build es-score`, then run the binary, with build
output kept on stderr.

**The red is the absent-corpus discipline firing one layer up.** The
scoreboard refused to report a number when its own runner was missing, rather
than printing `0 scored` and passing. That is what the state partition is
for, and the first thing it caught was the harness rather than the model.

### EVERY EARLIER NUMBER WAS A PROXY

`+1,249`, `+1,036`, `33/66`, `5,464` are predictions computed from the
evaluator's own arms — four inches of exact prediction-vs-actual measuring
the instrument against itself. This is the first instrument in the lane that
runs the tests.

---

## 2026-08-25-es-2 — the envelope's node type was being overwritten by ESTree's own `kind`, and no test262 test had ever been ingestible

`extractors/es/extract.py`, `LeanModels/Es/{Json,Load}.lean`,
`docs/es-envelope-schema.md`, `Examples/es/test262/` — **schema `es-0.1` -> `es-0.2`.**

### WHAT THE SECOND SCOREBOARD RUN FOUND

Build GREEN, corpus verified, runner built and RUN — and `attempted 0`, with
every one of the eleven zero-states genuinely zero. The bucket-level
conservation held; the population-level check said nobody was ever attempted.

Running the built binary on five tests gave the answer in one line:

    es-score: prelude 'assert-….json' is not an envelope: parse: program:
    property 'body': property 'body': property 'body': kind 'var' is outside
    the pinned vocabulary

### THE DEFECT

The extractor wrote the node TYPE into a field called `kind`, then merged the
node's ESTree properties over it. **ESTree gives `VariableDeclaration` a
property called `kind`** (`"var"`/`"let"`/`"const"`) — and `Property`
(`"init"`/`"get"`/`"set"`) and `MethodDefinition` the same. The property won.
Every declaration serialized as `{"kind": "var", …}` with its type GONE, and
the ingester refused it as an unknown kind.

So **no test262 test had ever been ingestible**, because `assert.js` is full of
`var` and every test loads it.

### WHY NOTHING CAUGHT IT FOR FOUR INCHES

Three independent gaps, and each looked reasonable alone:

* **Both round-trip fixtures happened to contain no declaration.**
  `if_cptn.json` is all `ExpressionStatement`s; `class_dup_binding.json` is a
  negative parse. The gate was real and simply never saw a `var`.
* **The vocabulary census reads acorn DIRECTLY**, not through the extractor,
  so `VariableDeclaration` counted as present at every step.
* **The evaluator's guards build `Node` terms BY HAND** — `Node.mk
  .variableDeclaration … [("kind", .str "var")]` — so the Lean side was
  correct and tested, and the JSON side was never exercised with a
  declaration.

**Every instrument was measuring something true. None of them was measuring
the path a test actually takes**, and that path did not exist until the
scoreboard. This is the first defect in this lane that only a running corpus
could find, and it is the strongest argument for the scoreboard that could
have been produced.

### THE FIX

The node type moves to `node_kind`, which is not an ESTree property name, so
the collision cannot recur for any node type. ESTree's `kind` flows through as
an ordinary scalar — which is what the evaluator already reads (`n.str?
"kind"`), so **no evaluator code changed**. Schema bumped to `es-0.2` and the
ingester pins it.

### THE GATES THAT WERE MISSING, NOW PRESENT

* `extract.py --self-test` lowers a `VariableDeclaration`, a `Property` and a
  `MethodDefinition` that each carry their own `kind`, and asserts BOTH the
  node type and the property survive.
* `Examples/es/test262/var_decl.json` is a new fixture that CONTAINS a
  declaration, with a guard that its `kindOf` is `variableDeclaration` and its
  `kind` scalar is `"var"` — the round trip the old fixtures could not test.
