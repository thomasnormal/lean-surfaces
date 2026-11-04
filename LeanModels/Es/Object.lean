import LeanModels.Es.Completion
import LeanModels.Es.Ast

/-!
# The ordinary object model (`LeanModels.Es`)

M2 inch 2. Property keys, Property Descriptors, the ordinary object's
internal methods, and the prototype walk — ES2026 §6.2.6 and §10.1.

**Why this is rung 0 and not a later rung.** `docs/es-semantics-design.md`
§0.1 measured it: every test262 test evaluates `harness/sta.js` first, and
that file defines `Test262Error` with `this instanceof Test262Error`,
`this.message = …` and `Test262Error.prototype.toString = …`. So a tier
that cannot create an ordinary object, define a data property on it and
walk a prototype chain cannot report a test failure, let alone a pass.

**Correspondence** (`docs/es-charter.md` §1.3): one definition per typed
clause, cited `(ES2026, clause-id, step)`. The 21 clauses realized here
carry **159 numbered steps** in the pinned text; `ValidateAndApplyPropertyDescriptor`
alone is 34 of them, which is why it gets its own section.

**The one refusal, and it is a boundary rather than a gap.** An ACCESSOR
property's `[[Get]]`/`[[Set]]` invoke the getter or setter, which needs
`[[Call]]` — inch 4. Those arms refuse with `unsupportedConstruct` rather
than inventing a value. Data properties are complete. `sta.js` uses only
data properties, so the floor is cleared without the refusal firing.
-/

namespace LeanModels.Es

/-! ## Property keys — ES2026 §6.2.5 -/

/-- A property key is a String or a Symbol, and nothing else (§6.2.5).
Symbols compare by IDENTITY, never by description, which is why the
description is not a field here — `Val.sameValue`'s Symbol arm makes the
same choice for the same reason. -/
inductive PropKey where
  | str (s : String)
  | sym (id : SymId)
  deriving DecidableEq, Repr, Inhabited

/-- A key's text, for messages and for `GetValue` on an environment
reference (where the "property name" IS the binding name). A Symbol has
no text — it is rendered by its id, never by its description, which is
the same identity rule `Val.sameValue` follows. -/
def PropKey.text : PropKey → String
  | .str s => s
  | .sym i => s!"Symbol({i})"

/-- Is this key an array index — a canonical numeric String in
`[0, 2^32 - 2]`? ES2026 §6.1.7 defines it, and §10.1.11 needs it because
integer-indexed keys are enumerated FIRST, in ascending numeric order,
before any other string key. -/
def PropKey.arrayIndex? : PropKey → Option Nat
  | .sym _ => none
  | .str s =>
    -- Over `toList`, NOT over `String.all`/`String.foldl`.  MEASURED on the
    -- pinned toolchain: `"10".toList` reduces by `rfl` and `"10".all
    -- Char.isDigit` does NOT — String's own iteration goes through
    -- `String.Pos` and gets stuck in the kernel.  The first version used
    -- `String.all` and `String.foldl`, and the result was a definition
    -- `#guard` could evaluate (the elaborator unfolds further) but no
    -- LEMMA could state: `rfl` and `decide` both stuck.  A primitive the
    -- guards can check and the proof layer cannot is a fidelity gap, so
    -- the definition moved rather than the claim.
    match s.toList with
    | [] => none
    | ['0'] => some 0
    | c :: cs =>
      if c == '0' then none                      -- no leading zeros
      else if (c :: cs).all Char.isDigit then
        let n := (c :: cs).foldl (fun acc d => acc * 10 + (d.toNat - 48)) 0
        if n < 4294967295 then some n else none
      else none

/-! ## Property Descriptors — ES2026 §6.2.6

Every field is OPTIONAL, and the present/absent distinction is load-bearing
rather than a convenience: §6.2.6.1-.3 classify a descriptor by WHICH
fields are present, and `ValidateAndApplyPropertyDescriptor` repeatedly
asks "if `Desc` has a `[[Value]]` field". A record of defaults could not
express the question. -/

structure PropDesc where
  value : Option Val := none
  writable : Option Bool := none
  /-- `undefined` or a callable object (§6.2.6). -/
  get : Option Val := none
  set : Option Val := none
  enumerable : Option Bool := none
  configurable : Option Bool := none
  deriving Repr, Inhabited

namespace PropDesc

/-- `IsAccessorDescriptor(Desc)` — ES2026 §6.2.6.1. -/
def isAccessor (d : PropDesc) : Bool := d.get.isSome || d.set.isSome

/-- `IsDataDescriptor(Desc)` — ES2026 §6.2.6.2. -/
def isData (d : PropDesc) : Bool := d.value.isSome || d.writable.isSome

/-- `IsGenericDescriptor(Desc)` — ES2026 §6.2.6.3: neither of the above. -/
def isGeneric (d : PropDesc) : Bool := !d.isAccessor && !d.isData

/-- A fully-populated data property, the shape `CreateDataProperty` makes. -/
def data (v : Val) (w e c : Bool) : PropDesc :=
  { value := some v, writable := some w, enumerable := some e, configurable := some c }

/-- `CompletePropertyDescriptor(Desc)` — ES2026 §6.2.6.6, 10 steps: fill
every absent field with its default, which is `undefined`/`false`. -/
def complete (d : PropDesc) : PropDesc :=
  if d.isAccessor then
    { d with get := d.get.getD .undef, set := d.set.getD .undef,
             enumerable := d.enumerable.getD false,
             configurable := d.configurable.getD false }
  else
    { d with value := d.value.getD .undef, writable := d.writable.getD false,
             enumerable := d.enumerable.getD false,
             configurable := d.configurable.getD false }

end PropDesc

/-! ## Function objects — the slots ES2026 §10.2 gives them

Declared here rather than in `Function.lean` because `Obj` carries them:
an ECMAScript function object IS an ordinary object with extra internal
slots, and modelling it as a separate type would make `[[Get]]` on a
function a different operation than `[[Get]]` on anything else. -/

/-- A reference to an Environment Record — §9.1. The records live in
`EsWorld.envs`, the same index-into-an-array shape as `ObjRef`. -/
abbrev EnvRef := Nat

/-- `[[ThisMode]]` — §10.2, and the three values the spec names. `lexical`
is an arrow function: it has no `this` of its own and does not get one
bound. -/
inductive ThisMode where
  | lexical
  | strict
  | global
  deriving DecidableEq, Repr, Inhabited

/--
`[[FormalParameters]]` and `[[ECMAScriptCode]]` — §10.2.3 steps 6-7.

The spec stores *Parse Nodes*, so this stores the ingested AST: a function
closes over its own source structure and nothing is re-parsed at call
time. Keeping the AST rather than a pre-compiled closure is what lets
`FunctionDeclarationInstantiation` read the parameter list's STATIC
semantics — `BoundNames`, `IsSimpleParameterList` — at the moment of the
call, which is exactly where §10.2.11 reads them.
-/
structure Code where
  params : List Node
  body : Node
  /-- True for an arrow whose `ConciseBody` is an `AssignmentExpression`
  rather than a `FunctionBody`: `x => x + 1`. Its value IS the return
  value (§15.3.5 step 4), so there is no statement list to run and no
  `return` completion to absorb. -/
  exprBody : Bool := false
  deriving Repr, Inhabited

/--
What a callable object's `[[Call]]` actually runs.

**A builtin is named, not embedded.** Storing a `List Val → …` closure in
`Obj` would cost `Repr`, `Inhabited` and every kernel `#guard` over a
heap — the whole first-order discipline the Python tier keeps for the same
reason. So a builtin carries its NAME and a table dispatches it.

`ecmascript` carries its `Code`. Inch 3 left this constructor EMPTY and
`OrdinaryCallEvaluateBody` refused on it, because the statement evaluator
did not exist; inch 5 gives it the AST and retires that refusal.
`Function.lean` still holds the refusing fragment for the same reason
`Ordinary.ordinaryGet` still holds the accessor-free `[[Get]]`: the
complete version needs the evaluator, and the evaluator imports this file.

**`DecidableEq` is gone from this type.** It was derivable while both
arms were finite; a `Code` holds a `Node`, whose equality is the AST's,
and no clause in the model branches on whether two function bodies are
the same term. Deriving it anyway would have manufactured an equality the
spec never asks for.
-/
inductive Body where
  | builtin (name : String)
  | ecmascript (code : Code)
  deriving Repr, Inhabited

/-- The internal slots §10.2 gives an ECMAScript function object. -/
structure FuncData where
  body : Body
  /-- `[[Environment]]` — the scope the function closes over. -/
  env : Option EnvRef := none
  /-- `[[ThisMode]]`. -/
  thisMode : ThisMode := .strict
  /-- `[[Strict]]`. -/
  strict : Bool := true
  /-- Non-`none` exactly when the object has `[[Construct]]`; the value is
  `[[ConstructorKind]]`'s `base`/`derived` distinction as a Bool
  (`true` = derived). §10.2.2. -/
  constructorDerived : Option Bool := none
  /-- `[[HomeObject]]`, for `super`. -/
  homeObject : Option ObjRef := none
  deriving Repr, Inhabited

/-! ## Environment Records — ES2026 §9.1 -/

/-- One binding in a Declarative Environment Record — §9.1.1.1.

`value = none` is the UNINITIALIZED state, which is not a niche: it is the
temporal dead zone. `let x; x` before the declaration must throw a
`ReferenceError`, and a record that defaulted the value to `undefined`
could not tell that apart from `let x = undefined`. -/
structure Binding where
  value : Option Val := none
  mutable : Bool := true
  deletable : Bool := false
  /-- A `const` in strict code: assigning throws rather than silently
  failing (§9.1.1.1.5 step 5). -/
  strictImmutable : Bool := false
  deriving Repr, Inhabited

/-- `[[ThisBindingStatus]]` — §9.1.1.3. -/
inductive ThisStatus where
  | lexical
  | uninitialized
  | initialized
  deriving DecidableEq, Repr, Inhabited

/--
An Environment Record — §9.1.

ONE structure covers the declarative and function kinds, because the
spec's Function Environment Record *is* a Declarative Environment Record
plus four fields (§9.1.1.3). A sum type would duplicate all seven
declarative operations to no benefit. The Object and Global kinds are NOT
here: both need the global object, which needs intrinsics (inch 6+).
-/
structure EnvRec where
  bindings : List (String × Binding) := []
  /-- `[[OuterEnv]]` — `none` only for the topmost record. -/
  outer : Option EnvRef := none
  /-- `[[ThisValue]]`, meaningful when `thisStatus ≠ .lexical`. -/
  thisValue : Val := .undef
  thisStatus : ThisStatus := .lexical
  /-- `[[FunctionObject]]`. -/
  functionObject : Option ObjRef := none
  /-- `[[NewTarget]]`. -/
  newTarget : Val := .undef
  deriving Repr, Inhabited

/--
Which EXOTIC object this is, if any — ES2026 §10.4.

Marked the way callability already is: `callable : Option FuncData` is what
makes `IsCallable` a field test rather than a guess (§7.2.3), and this is
the same shape for the same reason. An Array's `[[DefineOwnProperty]]`
differs from the ordinary one (§10.4.2.1), and a model that could not SEE
that it was holding an Array would have to guess.

One constructor today. It is an `inductive` rather than a `Bool` because
§10.4 has ten more — String, Arguments, Proxy — and each arrives by adding
an arm here plus a branch in the dispatcher, never by widening a flag.
-/
inductive ExoticKind where
  | array
  deriving DecidableEq, Repr, Inhabited

/-! ## Ordinary objects and the heap -/

/--
An ordinary object — ES2026 §10.1.

`props` is an ASSOCIATION LIST, not a map, and that is forced: §10.1.11
`OrdinaryOwnPropertyKeys` enumerates non-index string keys **in property
creation order**, so insertion order is observable and a structure that
lost it would be wrong about a fact the corpus tests.
-/
structure Obj where
  props : List (PropKey × PropDesc) := []
  /-- `[[Prototype]]` — an object, or `null` (`none`). -/
  proto : Option ObjRef := none
  /-- `[[Extensible]]`. -/
  extensible : Bool := true
  /-- The `[[Call]]`/`[[Construct]]` slots, when this object is callable.
  `none` for a plain object — which is what makes `IsCallable` a field test
  rather than a guess (§7.2.3). -/
  callable : Option FuncData := none
  /-- `none` for an ordinary object. See `ExoticKind`. -/
  exotic : Option ExoticKind := none
  deriving Repr, Inhabited

/-- The realm's heap. `ObjRef` is the index, the Python tier's shape. -/
structure EsWorld where
  heap : Array Obj := #[]
  /-- The Environment Records — §9.1. Kept beside the heap rather than
  inside it: an environment is a SPECIFICATION type (§6.2), not a value a
  program can hold, so it must not be reachable as an `ObjRef`. -/
  envs : Array EnvRec := #[]
  deriving Repr, Inhabited

/-- The tier's monad at its usual instantiation. -/
abbrev EsW := SemM EsWorld Abrupt

namespace Obj

/-- The own property at `k`, or `none`. -/
def find? (o : Obj) (k : PropKey) : Option PropDesc :=
  (o.props.find? (fun p => p.1 == k)).map (·.2)

/-- Insert or REPLACE, preserving position on replace — which is the
observable half: redefining an existing property must not move it to the
end of the enumeration order. -/
def put (o : Obj) (k : PropKey) (d : PropDesc) : Obj :=
  if o.props.any (fun p => p.1 == k) then
    { o with props := o.props.map (fun p => if p.1 == k then (k, d) else p) }
  else
    { o with props := o.props ++ [(k, d)] }

def erase (o : Obj) (k : PropKey) : Obj :=
  { o with props := o.props.filter (fun p => p.1 != k) }

end Obj

namespace EsWorld

def get? (w : EsWorld) (r : ObjRef) : Option Obj := w.heap[r]?

def set (w : EsWorld) (r : ObjRef) (o : Obj) : EsWorld :=
  { w with heap := w.heap.set! r o }

/-- `MakeBasicObject` — ES2026 §10.1.12.1 (9 steps), reduced to what an
ordinary object needs: allocate, return the reference. -/
def alloc (w : EsWorld) (o : Obj) : ObjRef × EsWorld :=
  (w.heap.size, { w with heap := w.heap.push o })

end EsWorld

end LeanModels.Es
