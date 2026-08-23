import LeanModels.Es.Ordinary

/-!
# Environment Records — ES2026 §9.1, §9.4

M2 inch 3, first half: the Declarative and Function Environment Records,
and the execution-context operations that resolve a name or a `this`.

**Correspondence**: one definition per typed clause, cited
`(ES2026, clause-id, step)`. The clauses realized here carry **84**
numbered steps in the pinned text (33 declarative + 10 function + 10
env-ops + 21 execution-context + 10 shared).

**A `ReferenceError` here is a THROW, not a refusal**, and the difference
is the tier's whole point: an unresolvable name is a program outcome the
spec defines (§9.4.2 step 3), so it lands in `ρ` where a `try` can catch
it. Only things the tier does not model refuse.
-/

namespace LeanModels.Es

/-- Read an environment record, or fail internally — a dangling `EnvRef`
is a tier fault, not a program error, so it is not catchable. -/
def derefEnv (r : EnvRef) : EsW EnvRec := fun w =>
  match w.envs[r]? with
  | some e => .ok (.ok e, w)
  | none => .error (.unsupported (esRefusal .construct "internal")
              s!"internal: dangling environment reference {r} (report this)" none)

def storeEnv (r : EnvRef) (e : EnvRec) : EsW Unit := fun w =>
  .ok (.ok (), { w with envs := w.envs.set! r e })

def allocEnv (e : EnvRec) : EsW EnvRef := fun w =>
  .ok (.ok w.envs.size, { w with envs := w.envs.push e })

/-! ## Throwing the errors the spec names

Until the intrinsics exist (inch 6) an error VALUE cannot be a real
`Error` object, so it is thrown as a string carrying the class name. The
shape is honest about itself: `throwError` is the ONE place that changes
when `%ReferenceError%` arrives, and every clause below already routes
through it. -/

def throwError (kind msg : String) : EsW α :=
  SemM.raise (.throw (.str s!"{kind}: {msg}"))

/-! ## Declarative Environment Records — §9.1.1.1 -/

namespace EnvRec

def find? (e : EnvRec) (n : String) : Option Binding :=
  (e.bindings.find? (fun b => b.1 == n)).map (·.2)

def put (e : EnvRec) (n : String) (b : Binding) : EnvRec :=
  if e.bindings.any (fun p => p.1 == n) then
    { e with bindings := e.bindings.map (fun p => if p.1 == n then (n, b) else p) }
  else { e with bindings := e.bindings ++ [(n, b)] }

def erase (e : EnvRec) (n : String) : EnvRec :=
  { e with bindings := e.bindings.filter (fun p => p.1 != n) }

end EnvRec

/-- `HasBinding(N)` — §9.1.1.1.1, 2 steps. -/
def envHasBinding (r : EnvRef) (n : String) : EsW Bool :=
  return ((← derefEnv r).find? n).isSome

/-- `CreateMutableBinding(N, D)` — §9.1.1.1.2, 3 steps. -/
def envCreateMutableBinding (r : EnvRef) (n : String) (deletable : Bool) : EsW Unit := do
  storeEnv r ((← derefEnv r).put n { mutable := true, deletable := deletable })

/-- `CreateImmutableBinding(N, S)` — §9.1.1.1.3, 3 steps. -/
def envCreateImmutableBinding (r : EnvRef) (n : String) (strict : Bool) : EsW Unit := do
  storeEnv r ((← derefEnv r).put n { mutable := false, strictImmutable := strict })

/-- `InitializeBinding(N, V)` — §9.1.1.1.4, 4 steps. -/
def envInitializeBinding (r : EnvRef) (n : String) (v : Val) : EsW Unit := do
  let e ← derefEnv r
  match e.find? n with
  | none => SemM.refuseConstruct
              s!"internal: InitializeBinding on absent '{n}' (report this)"
  | some b => storeEnv r (e.put n { b with value := some v })

/--
`SetMutableBinding(N, V, S)` — §9.1.1.1.5, **14 steps**, and the longest
of the declarative operations because it carries three distinct failures.

Steps 2-3: assigning to a name with NO binding creates one when
non-strict, and throws `ReferenceError` when strict. Step 5: an
uninitialized binding throws `ReferenceError` — the temporal dead zone.
Step 7: assigning to an immutable binding throws `TypeError` in strict
code and is SILENTLY IGNORED otherwise, which is the one place the spec
asks a write to do nothing.
-/
def envSetMutableBinding (r : EnvRef) (n : String) (v : Val) (strict : Bool) : EsW Unit := do
  let e ← derefEnv r
  match e.find? n with
  | none =>
    if strict then throwError "ReferenceError" s!"{n} is not defined"
    else do
      storeEnv r (e.put n { value := some v, mutable := true, deletable := true })
  | some b =>
    if b.value.isNone then
      throwError "ReferenceError" s!"Cannot access '{n}' before initialization"
    else if b.mutable then
      storeEnv r (e.put n { b with value := some v })
    else if b.strictImmutable || strict then
      throwError "TypeError" s!"Assignment to constant variable '{n}'"
    else
      pure ()                                    -- step 7.b: silently ignored

/-- `GetBindingValue(N, S)` — §9.1.1.1.6, 3 steps. An uninitialized
binding throws `ReferenceError` — the TDZ again, on the read side. -/
def envGetBindingValue (r : EnvRef) (n : String) : EsW Val := do
  match (← derefEnv r).find? n with
  | none => SemM.refuseConstruct
              s!"internal: GetBindingValue on absent '{n}' (report this)"
  | some b =>
    match b.value with
    | none => throwError "ReferenceError" s!"Cannot access '{n}' before initialization"
    | some v => return v

/-- `DeleteBinding(N)` — §9.1.1.1.7, 4 steps. -/
def envDeleteBinding (r : EnvRef) (n : String) : EsW Bool := do
  let e ← derefEnv r
  match e.find? n with
  | none => return true
  | some b =>
    if !b.deletable then return false
    else do storeEnv r (e.erase n); return true

/-! ## Function Environment Records — §9.1.1.3 -/

/-- `BindThisValue(V)` — §9.1.1.3.1, 5 steps. Binding `this` TWICE is a
`ReferenceError`: it is what a derived constructor calling `super()` twice
must do. -/
def envBindThisValue (r : EnvRef) (v : Val) : EsW Val := do
  let e ← derefEnv r
  if e.thisStatus == .initialized then
    throwError "ReferenceError" "Super constructor may only be called once"
  else do
    storeEnv r { e with thisValue := v, thisStatus := .initialized }
    return v

/-- `HasThisBinding()` — §9.1.1.3.2, 2 steps. An arrow function's record
answers `false`, which is exactly what makes `this` lexical in one. -/
def envHasThisBinding (r : EnvRef) : EsW Bool :=
  return (← derefEnv r).thisStatus != .lexical

/-- `GetThisBinding()` — §9.1.1.3.3, 3 steps. -/
def envGetThisBinding (r : EnvRef) : EsW Val := do
  let e ← derefEnv r
  if e.thisStatus == .uninitialized then
    throwError "ReferenceError"
      "Must call super constructor before accessing 'this'"
  else return e.thisValue

/-! ## Creating environments — §9.1.2 -/

/-- `NewDeclarativeEnvironment(E)` — §9.1.2.2, 3 steps. -/
def newDeclarativeEnvironment (outer : Option EnvRef) : EsW EnvRef :=
  allocEnv { outer := outer, thisStatus := .lexical }

/-- `NewFunctionEnvironment(F, newTarget)` — §9.1.2.4, 7 steps.

`[[ThisBindingStatus]]` is `lexical` for an arrow and **`uninitialized`
for everything else** — read from the spec after the first version wrote
`initialized` for a non-derived function and every `[[Call]]` then threw
"Super constructor may only be called once". `BindThisValue` (§9.1.1.3.1)
is what moves it to `initialized`, so a record that starts there has
already been bound and the second bind is the error. **`derived` plays no
part in THIS clause** — it decides only whether `[[Construct]]` makes
`thisArgument` up front (§10.2.2 step 5). -/
def newFunctionEnvironment (f : ObjRef) (newTarget : Val) : EsW EnvRef := do
  let fo ← deref f
  let isLexical : Bool := match fo.callable with
    | some fd => fd.thisMode == .lexical
    | none => false
  allocEnv {
    outer := (fo.callable.bind (·.env)),
    functionObject := some f,
    newTarget := newTarget,
    thisStatus := if isLexical then .lexical else .uninitialized }

/-! ## Execution-context operations — §9.4 -/

/-- `GetThisEnvironment()` — §9.4.1, 7 steps: walk OUT until a record has
a `this` binding. An arrow function's record has none, so the walk passes
straight through it — which IS lexical `this`, not a special case. -/
def getThisEnvironment : Nat → EnvRef → EsW EnvRef
  | 0, _ => fun _ => .error .timeout
  | n + 1, r => do
    if ← envHasThisBinding r then return r
    match (← derefEnv r).outer with
    | some o => getThisEnvironment n o
    | none => SemM.refuseConstruct
                "internal: no `this` environment in the chain (report this)"

/-- `ResolveThisBinding()` — §9.4.2, 2 steps. -/
def resolveThisBinding (fuel : Nat) (r : EnvRef) : EsW Val := do
  envGetThisBinding (← getThisEnvironment fuel r)

/--
`GetIdentifierReference(env, name, strict)` — §9.4.2.1, 7 steps, plus
`ResolveBinding` (§9.4.2, 5 steps) which is its caller.

Returns the ENVIRONMENT that binds the name, or throws the
`ReferenceError` the spec's step 2.b names for an unresolvable one. A
Reference Record proper (§6.2.5) arrives with the expression evaluator;
until then the resolved environment is what a caller needs.
-/
def resolveBinding : Nat → EnvRef → String → EsW EnvRef
  | 0, _, _ => fun _ => .error .timeout
  | n + 1, r, name => do
    if ← envHasBinding r name then return r
    match (← derefEnv r).outer with
    | some o => resolveBinding n o name
    | none => throwError "ReferenceError" s!"{name} is not defined"

/-- Read a name through the scope chain — `ResolveBinding` then
`GetValue`. -/
def lookupName (fuel : Nat) (r : EnvRef) (name : String) : EsW Val := do
  envGetBindingValue (← resolveBinding fuel r name) name

/-- Assign to a name through the scope chain. -/
def assignName (fuel : Nat) (r : EnvRef) (name : String) (v : Val) (strict : Bool) :
    EsW Unit := do
  envSetMutableBinding (← resolveBinding fuel r name) name v strict

end LeanModels.Es
