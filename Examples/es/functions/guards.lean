import LeanModels.Es

/-!
# M2 inch 3's acceptance: environments, `[[Call]]`, `[[Construct]]`, `this`

`docs/es-semantics-design.md` inch 4 of the ladder (this lane's inch 3).
Every `#guard` is decided by the KERNEL.

The centrepiece is the `sta.js` CONSTRUCTION shape:

    function Test262Error(message) { … }
    Test262Error.prototype.toString = function () { … };
    new Test262Error("boom")   →   an object whose [[Prototype]] is
                                   Test262Error.prototype, and which
                                   `instanceof Test262Error`

Everything but the BODY statements is exercised below; the body is inch 5,
and its refusal is pinned rather than hidden.
-/

namespace Examples.es.functions

open LeanModels.Es

def runs (m : EsW Bool) (v : Bool) : Bool :=
  match SemM.run m default with
  | .ok (.ok r, _) => r == v
  | _ => false

def yields (m : EsW Val) (v : Val) : Bool :=
  match SemM.run m default with
  | .ok (.ok r, _) => Val.sameValue r v
  | _ => false

/-- Did it THROW (a program outcome in `ρ`), with a message starting `k`? -/
def throwsKind (m : EsW α) (k : String) : Bool :=
  match SemM.run m default with
  | .ok (.error (.throw (.str s)), _) => s.startsWith k
  | _ => false

/-- Did it REFUSE (not in `ρ`, so no `try` can reach it), with this cause? -/
def refuses (m : EsW α) (cls : String) : Bool :=
  match SemM.run m default with
  | .error (.unsupported c _ _) => c.className == cls
  | _ => false

/-! ## The `sta.js` construction shape -/

/- `new F()` on a base constructor returns the OBJECT it made — §10.2.2
step 13 — not the body's `undefined`. -/
#guard match SemM.run (do
    let f ← ordinaryFunctionCreate none (.builtin "%identity%") none .strict true
    makeConstructor f none
    constructValue 10 (.obj f) []) default with
  | .ok (.ok (.obj _), _) => true
  | _ => false

/- …and that object's `[[Prototype]]` IS `F.prototype`, which is what
makes `instanceof` work. -/
#guard runs (do
  let f ← ordinaryFunctionCreate none (.builtin "%identity%") none .strict true
  makeConstructor f none
  let inst ← constructValue 10 (.obj f) []
  ordinaryHasInstance 10 (.obj f) inst) true

/- `MakeConstructor` sets `F.prototype.constructor === F` — §10.2.5 step 6,
the back-link `sta.js` depends on. -/
#guard runs (do
  let f ← ordinaryFunctionCreate none (.builtin "%identity%") none .strict true
  makeConstructor f none
  match ← getV 10 f (.str "prototype") (.obj f) with
  | .obj p => do
    let c ← getV 10 p (.str "constructor") (.obj p)
    return Val.sameValue c (.obj f)
  | _ => return false) true

/- An unrelated object is NOT an instance. -/
#guard runs (do
  let f ← ordinaryFunctionCreate none (.builtin "%identity%") none .strict true
  makeConstructor f none
  let other ← ordinaryObjectCreate none
  ordinaryHasInstance 10 (.obj f) (.obj other)) false

/-! ## `this` binding — §10.2.1.2, the three modes -/

/- STRICT binds the argument EXACTLY, `undefined` included — no coercion. -/
#guard yields (do
  let f ← ordinaryFunctionCreate none (.builtin "%thisValue%") none .strict true
  esCall f .undef []) .undef

#guard yields (do
  let f ← ordinaryFunctionCreate none (.builtin "%thisValue%") none .strict true
  let o ← ordinaryObjectCreate none
  esCall f (.obj o) []) (.obj 1)

/- SLOPPY mode coerces, and that needs the realm — so it REFUSES rather
than inventing a global object. -/
#guard refuses (do
  let f ← ordinaryFunctionCreate none (.builtin "%thisValue%") none .global false
  esCall f .undef []) "environment"

/- A LEXICAL (arrow) function binds NOTHING, so its record has no `this`
and the lookup walks outward — §10.2.1.2 step 1. -/
#guard runs (do
  let f ← ordinaryFunctionCreate none (.builtin "%identity%") none .lexical true
  let env ← newFunctionEnvironment f .undef
  envHasThisBinding env) false

/-! ## `Call` — §7.3.14 -/

#guard yields (do
  let f ← ordinaryFunctionCreate none (.builtin "%identity%") none .strict true
  callValue (.obj f) .undef [.num 42.0]) (.num 42.0)

#guard yields (do
  let f ← ordinaryFunctionCreate none (.builtin "%argCount%") none .strict true
  callValue (.obj f) .undef [.undef, .undef, .undef]) (.num 3.0)

/- Calling a NON-callable THROWS `TypeError` — a program outcome in `ρ`,
catchable, never a refusal. -/
#guard throwsKind (do
  let o ← ordinaryObjectCreate none
  callValue (.obj o) .undef []) "TypeError"

#guard throwsKind (callValue (.num 1.0) .undef []) "TypeError"

/- `new` on a non-constructor throws too — a callable is not automatically
a constructor (§7.2.4). -/
#guard throwsKind (do
  let f ← ordinaryFunctionCreate none (.builtin "%identity%") none .strict true
  constructValue 10 (.obj f) []) "TypeError"

/-! ## THE ACCESSOR REFUSAL IS RETIRED — inch 2's boundary, moved

An accessor whose getter is a BUILTIN now RUNS through `getV`. What
remains is one boundary — body evaluation — rather than a refusal per
feature. -/

#guard yields (do
  let g ← ordinaryFunctionCreate none (.builtin "%argCount%") none .strict true
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "g")
            { get := some (.obj g), enumerable := some true, configurable := some true }
  getV 10 o (.str "g") (.obj o)) (.num 0.0)

/- …and the getter receives the RECEIVER as its `this` — §10.1.8.1 step 8. -/
#guard runs (do
  let g ← ordinaryFunctionCreate none (.builtin "%thisValue%") none .strict true
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "g")
            { get := some (.obj g), enumerable := some true, configurable := some true }
  return Val.sameValue (← getV 10 o (.str "g") (.obj o)) (.obj o)) true

/- An ECMASCRIPT body was inch 3's one boundary. Inch 5 retired it — bodies
RUN, and `Examples/es/statements/guards.lean` is where they are pinned.
What this guard now holds is the LAYERING: `esCall` here is still the
FRAGMENT, and it must keep refusing rather than quietly answering
`undefined`, because a fragment that returns a plausible value is how a
caller that forgot to move to `Eval.callComplete` scores a false pass. -/
#guard refuses (do
  let f ← ordinaryFunctionCreate none (.ecmascript { params := [], body := default })
            none .strict true
  esCall f .undef []) "unsupported"

/-! ## Environment Records — §9.1.1.1

The TDZ is the rule worth pinning: an uninitialized binding is not
`undefined`, and telling them apart is why `Binding.value` is an `Option`. -/

#guard throwsKind (do
  let e ← newDeclarativeEnvironment none
  envCreateMutableBinding e "x" false
  envGetBindingValue e "x") "ReferenceError"

#guard yields (do
  let e ← newDeclarativeEnvironment none
  envCreateMutableBinding e "x" false
  envInitializeBinding e "x" (.num 7.0)
  envGetBindingValue e "x") (.num 7.0)

/- Assigning to a `const` throws `TypeError` in strict code… -/
#guard throwsKind (do
  let e ← newDeclarativeEnvironment none
  envCreateImmutableBinding e "c" true
  envInitializeBinding e "c" (.num 1.0)
  envSetMutableBinding e "c" (.num 2.0) true) "TypeError"

/- …and in SLOPPY code is SILENTLY IGNORED — §9.1.1.1.5 step 7.b, the one
place the spec asks a write to do nothing. -/
#guard yields (do
  let e ← newDeclarativeEnvironment none
  envCreateImmutableBinding e "c" false
  envInitializeBinding e "c" (.num 1.0)
  envSetMutableBinding e "c" (.num 2.0) false
  envGetBindingValue e "c") (.num 1.0)

/- Only a `deletable` binding deletes — §9.1.1.1.7. -/
#guard runs (do
  let e ← newDeclarativeEnvironment none
  envCreateMutableBinding e "d" true
  envDeleteBinding e "d") true

#guard runs (do
  let e ← newDeclarativeEnvironment none
  envCreateMutableBinding e "d" false
  envDeleteBinding e "d") false

/-! ## The scope chain — §9.4.2 -/

/- A name resolves in an OUTER environment. -/
#guard yields (do
  let outer ← newDeclarativeEnvironment none
  envCreateMutableBinding outer "v" false
  envInitializeBinding outer "v" (.str "found")
  let inner ← newDeclarativeEnvironment (some outer)
  lookupName 10 inner "v") (.str "found")

/- An unresolvable name THROWS `ReferenceError` — §9.4.2 step 3. It is a
program outcome, so it is in `ρ` and catchable. -/
#guard throwsKind (do
  let e ← newDeclarativeEnvironment none
  lookupName 10 e "nope") "ReferenceError"

/- An inner binding SHADOWS an outer one. -/
#guard yields (do
  let outer ← newDeclarativeEnvironment none
  envCreateMutableBinding outer "v" false
  envInitializeBinding outer "v" (.str "outer")
  let inner ← newDeclarativeEnvironment (some outer)
  envCreateMutableBinding inner "v" false
  envInitializeBinding inner "v" (.str "inner")
  lookupName 10 inner "v") (.str "inner")

/-! ## Fuel is an INDEX: exhaustion is `timeout`, never a wrong answer -/

#guard match SemM.run (do
    let outer ← newDeclarativeEnvironment none
    let inner ← newDeclarativeEnvironment (some outer)
    lookupName 0 inner "v") default with
  | .error .timeout => true
  | _ => false

end Examples.es.functions
