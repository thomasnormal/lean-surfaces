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
