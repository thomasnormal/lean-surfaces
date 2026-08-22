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
