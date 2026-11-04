import LeanModels.Es.Env

/-!
# Function objects: `[[Call]]`, `[[Construct]]`, and `this` — ES2026 §10.2

M2 inch 3, second half. The clauses realized here carry **120** numbered
steps in the pinned text, of which `[[Construct]]` is 24,
`OrdinaryFunctionCreate` 23 and `OrdinaryCallBindThis` 18.

**THE BOUNDARY, and it is sharper than inch 2's.** `[[Call]]` runs
`OrdinaryCallEvaluateBody` (§10.2.1.4), which evaluates a function BODY —
the statement evaluator, inch 5. So an `ecmascript`-bodied function
refuses there, while a `builtin` runs. That RETIRES inch 2's
accessor-shaped refusal: an accessor whose getter is a builtin now works,
and what remains is one boundary — *body evaluation* — rather than a
refusal per feature. The refusal moved down the stack and got narrower,
which is what a rung is supposed to do.
-/

namespace LeanModels.Es

/-! ## The builtin table

A builtin is dispatched by NAME (`Body.builtin`), keeping the heap
first-order. The table is a function rather than a stored closure for the
same reason: an `Obj` must stay `Repr`-able and kernel-inspectable. -/

/-- Dispatch a builtin. Unknown names REFUSE with `unmodeledIntrinsic` —
the cause `docs/es-charter.md` §3.6 reserves for a built-in outside the
modeled slice, which retires by widening the slice and is never a
language-tier gap. -/
def callBuiltin (name : String) (thisArg : Val) (args : List Val) : EsW Val :=
  match name with
  | "%identity%" => return args.headD .undef
  | "%thisValue%" => return thisArg
  | "%argCount%" => return .num (Float.ofNat args.length)
  | _ => SemM.refuseIntrinsic s!"builtin '{name}' is not modeled"

/-! ## `IsCallable` / `IsConstructor` — §7.2.3, §7.2.4

Both are 3 steps and both are a SLOT TEST, not a guess: `IsCallable` asks
whether the object has `[[Call]]`, which here is `callable.isSome`. -/

def isCallable (v : Val) : EsW Bool := do
  match v with
  | .obj r => return (← deref r).callable.isSome
  | _ => return false

def isConstructor (v : Val) : EsW Bool := do
  match v with
  | .obj r =>
    match (← deref r).callable with
    | some fd => return fd.constructorDerived.isSome
    | none => return false
  | _ => return false

/-! ## Creating a function — §10.2.3, §10.2.5 -/

/-- `OrdinaryFunctionCreate(proto, …, thisMode, env)` — §10.2.3, 23 steps.
The `[[ThisMode]]` is `lexical` for an arrow, `strict` under strict code
and `global` otherwise (steps 9-11), and it is what `OrdinaryCallBindThis`
branches on. -/
def ordinaryFunctionCreate (proto : Option ObjRef) (body : Body)
    (env : Option EnvRef) (thisMode : ThisMode) (strict : Bool) : EsW ObjRef := fun w =>
  let fd : FuncData := { body := body, env := env, thisMode := thisMode, strict := strict }
  let (r, w') := w.alloc { proto := proto, callable := some fd }
  .ok (.ok r, w')

/--
`MakeConstructor(F, writablePrototype, prototype)` — §10.2.5, 13 steps.

Gives `F` a `[[Construct]]` slot and the `prototype` property, and — the
step that makes `x instanceof F` work — sets `prototype.constructor` back
to `F`. `sta.js` relies on exactly this pair.
-/
def makeConstructor (f : ObjRef) (protoObj : Option ObjRef) : EsW Unit := do
  let fo ← deref f
  match fo.callable with
  | none => SemM.refuseConstruct
              "internal: MakeConstructor on a non-callable (report this)"
  | some fd =>
    store f { fo with callable := some { fd with constructorDerived := some false } }
    let p ← match protoObj with
      | some p => pure p
      | none => ordinaryObjectCreate none
    -- step 6: prototype.constructor = F, writable + configurable, NOT enumerable
    let _ ← ordinaryDefineOwnProperty p (.str "constructor")
              (PropDesc.data (.obj f) true false true)
    -- step 7: F.prototype = p, writable, NOT enumerable, NOT configurable
    let _ ← ordinaryDefineOwnProperty f (.str "prototype")
              (PropDesc.data (.obj p) true false false)
    pure ()

/-! ## The call protocol — §10.2.1 -/

/--
`OrdinaryCallBindThis(F, calleeContext, thisArgument)` — §10.2.1.2,
**18 steps**, and the one that decides what `this` IS.

Three cases, and the third is the one people are surprised by:
* `[[ThisMode]]` is `lexical` — an arrow — **bind nothing**, so `this`
  resolves outward (step 1);
* strict — bind the argument **exactly as given**, `undefined` included
  (step 5);
* otherwise (`global`) — `undefined`/`null` become the global object and a
  PRIMITIVE is boxed by `ToObject` (steps 6.a-6.c). That is sloppy mode's
  `this` coercion, and it is why `function f(){return this}` called bare
  answers an object rather than `undefined`.

The global-object substitution needs the global object (inch 6), so that
sub-arm refuses; the boxing of a primitive needs `ToObject`, which needs
the wrapper intrinsics, so it refuses too. **Strict mode — which is what
test262 runs half its corpus in, and what `sta.js` is — is complete.**
-/
def ordinaryCallBindThis (f : ObjRef) (calleeEnv : EnvRef) (thisArg : Val) : EsW Unit := do
  let fo ← deref f
  match fo.callable with
  | none => SemM.refuseConstruct
              "internal: OrdinaryCallBindThis on a non-callable (report this)"
  | some fd =>
    match fd.thisMode with
    | .lexical => pure ()                                   -- step 1
    | .strict => do let _ ← envBindThisValue calleeEnv thisArg; pure ()
    | .global =>
      match thisArg with
      | .undef | .null =>
        SemM.refuseHost
          "sloppy-mode `this`: undefined/null becomes the global object, which needs the realm (inch 6)"
      | .obj _ => do let _ ← envBindThisValue calleeEnv thisArg; pure ()
      | _ =>
        SemM.refuseIntrinsic
          "sloppy-mode `this`: a primitive is boxed by ToObject, which needs the wrapper intrinsics (inch 6)"

/-- `PrepareForOrdinaryCall(F, newTarget)` — §10.2.1.1, 14 steps: build the
callee's environment and make it the running context's. -/
def prepareForOrdinaryCall (f : ObjRef) (newTarget : Val) : EsW EnvRef :=
  newFunctionEnvironment f newTarget

/--
`OrdinaryCallEvaluateBody(F, argumentsList)` — §10.2.1.4, 1 step, which
delegates to `EvaluateBody` — **the statement evaluator, inch 5**.

A `builtin` body runs now. An `ecmascript` body needs the statement
evaluator, which imports this file, so **this is the fragment and
`Eval.evalCallBody` is the complete clause** — the same layering that
leaves the accessor-free `[[Get]]` in `Ordinary.lean` and the complete one
in `getV` below. Nothing in the model calls this arm any more: `Eval`'s
`callValue'` supersedes `callValue`. It refuses rather than answering
`undefined`, because a silent `undefined` here would let every function
call in the corpus score as a pass.
-/
def ordinaryCallEvaluateBody (f : ObjRef) (thisArg : Val) (args : List Val) : EsW Val := do
  match (← deref f).callable with
  | none => SemM.refuseConstruct
              "internal: evaluate body of a non-callable (report this)"
  | some fd =>
    match fd.body with
    | .builtin n => callBuiltin n thisArg args
    | .ecmascript _ =>
      SemM.refuseConstruct
        "ECMAScript function body: this is the FRAGMENT; Eval.evalCallBody is the complete clause"

/-- `[[Call]](thisArgument, argumentsList)` — §10.2.1, 14 steps. -/
def esCall (f : ObjRef) (thisArg : Val) (args : List Val) : EsW Val := do
  let calleeEnv ← prepareForOrdinaryCall f .undef
  ordinaryCallBindThis f calleeEnv thisArg
  ordinaryCallEvaluateBody f thisArg args

/-- `Call(F, V, argumentsList)` — §7.3.14, 3 steps: the abstract operation
callers use, which THROWS `TypeError` when `F` is not callable. That is a
program outcome, so it lands in `ρ`. -/
def callValue (fv : Val) (thisArg : Val) (args : List Val) : EsW Val := do
  if ← isCallable fv then
    match fv with
    | .obj r => esCall r thisArg args
    | _ => throwError "TypeError" "not a function"
  else throwError "TypeError" "is not a function"

/-! ## Construction — §10.2.2, §7.3.15, §10.1.13 -/

/-- `GetPrototypeFromConstructor(constructor, intrinsic)` — §10.1.14, 6
steps: read `constructor.prototype`, falling back to the intrinsic when it
is not an object. The fallback needs the realm (inch 6), so a
non-object `prototype` refuses rather than inventing one. -/
def getPrototypeFromConstructor (fuel : Nat) (c : ObjRef) : EsW (Option ObjRef) := do
  match ← ordinaryGet fuel c (.str "prototype") (.obj c) with
  | .obj p => return some p
  | _ => SemM.refuseIntrinsic
           "GetPrototypeFromConstructor's fallback is a realm intrinsic (inch 6)"

/-- `OrdinaryCreateFromConstructor(newTarget, intrinsic)` — §10.1.13, 5
steps. -/
def ordinaryCreateFromConstructor (fuel : Nat) (c : ObjRef) : EsW ObjRef := do
  ordinaryObjectCreate (← getPrototypeFromConstructor fuel c)

/--
`[[Construct]](argumentsList, newTarget)` — §10.2.2, **24 steps**.

The shape: a BASE constructor creates `thisArgument` from
`newTarget.prototype` BEFORE the body runs (step 5) and binds it as
`this`; a DERIVED one does not, which is why `this` before `super()`
throws. Step 13 is the return rule — an object result wins, otherwise the
bound `this` is returned, which is why `function F(){ this.x=1 }` used with
`new` yields the object and not `undefined`.
-/
def esConstruct (fuel : Nat) (f : ObjRef) (args : List Val) (newTarget : ObjRef) :
    EsW Val := do
  let fo ← deref f
  match fo.callable with
  | none => throwError "TypeError" "is not a constructor"
  | some fd =>
    if fd.constructorDerived.isNone then throwError "TypeError" "is not a constructor"
    else do
      let derived := fd.constructorDerived == some true
      -- step 5: a BASE constructor makes `this` up front
      let thisArg ← if derived then pure Val.undef
                    else do return .obj (← ordinaryCreateFromConstructor fuel newTarget)
      let calleeEnv ← prepareForOrdinaryCall f (.obj newTarget)
      if !derived then ordinaryCallBindThis f calleeEnv thisArg
      let result ← ordinaryCallEvaluateBody f thisArg args
      -- step 13: an object result wins; otherwise the bound `this`
      match result with
      | .obj _ => return result
      | _ => envGetThisBinding calleeEnv

/-- `Construct(F, argumentsList, newTarget)` — §7.3.15, 3 steps. -/
def constructValue (fuel : Nat) (fv : Val) (args : List Val) : EsW Val := do
  match fv with
  | .obj r =>
    if ← isConstructor fv then esConstruct fuel r args r
    else throwError "TypeError" "is not a constructor"
  | _ => throwError "TypeError" "is not a constructor"

/-! ## `Get`/`Set` WITH accessors — §7.3.2, §7.3.4, completing §10.1.8/§10.1.9

**This is where inch 2's accessor refusal retires.** `Ordinary.ordinaryGet`
could not call a getter because `[[Call]]` did not exist, and Lean forbids
`Ordinary.lean` importing this file (the import would cycle). So the
COMPLETE §10.1.8.1 lives here, where `esCall` is in scope, and
`ordinaryGet` remains its data-property fragment — its docstring says so.

The duplication is one prototype walk and it is deliberate: the
alternative was to parameterize `ordinaryGet` by a call-back at inch 2,
which would have put a hole in the object model for a caller that did not
exist yet. -/

/-- `Get(O, P)` — §7.3.2, and the complete `OrdinaryGet` (§10.1.8.1)
including step 8's `Call(getter, Receiver)`. -/
def getV : Nat → ObjRef → PropKey → Val → EsW Val
  | 0, _, _, _ => fun _ => .error .timeout
  | n + 1, r, k, receiver => do
    match ← ordinaryGetOwnProperty r k with
    | none =>
      match (← deref r).proto with
      | none => return .undef                              -- step 3.b
      | some p => getV n p k receiver                       -- step 3.c
    | some d =>
      if d.isData then return d.value.getD .undef           -- step 5
      else
        match d.get.getD .undef with
        | .undef => return .undef                           -- step 7
        | g => callValue g receiver []                      -- step 8

/-- `Set(O, P, V, Throw)` — §7.3.4, completing §10.1.9.2's step 5 by
CALLING the setter. -/
def setV (fuel : Nat) (r : ObjRef) (k : PropKey) (v : Val) (receiver : Val) : EsW Bool := do
  match ← ordinaryGetOwnProperty r k with
  | some d =>
    if d.isAccessor then
      match d.set.getD .undef with
      | .undef => return false                              -- step 4
      | s => do let _ ← callValue s receiver [v]; return true
    else ordinarySet fuel r k v receiver
  | none => ordinarySet fuel r k v receiver

/-! ## `instanceof`'s ordinary half — §13.10.2

`OrdinaryHasInstance(C, O)` — 8 steps: walk `O`'s prototype chain looking
for `C.prototype`. `sta.js`'s `this instanceof Test262Error` is this. -/
def ordinaryHasInstance (fuel : Nat) (c : Val) (o : Val) : EsW Bool := do
  if !(← isCallable c) then return false
  match c, o with
  | .obj cr, .obj _ =>
    match ← ordinaryGet fuel cr (.str "prototype") (.obj cr) with
    | .obj protoRef =>
      let rec walk : Nat → Val → EsW Bool
        | 0, _ => fun _ => .error .timeout
        | n + 1, .obj orf => do
          match (← deref orf).proto with
          | none => return false
          | some p => if p == protoRef then return true else walk n (.obj p)
        | _, _ => return false
      walk fuel o
    | _ => throwError "TypeError" "prototype is not an object"
  | _, _ => return false

end LeanModels.Es
