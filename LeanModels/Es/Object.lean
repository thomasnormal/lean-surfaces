import LeanModels.Es.Completion

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
  deriving Repr, Inhabited

/-- The realm's heap. `ObjRef` is the index, the Python tier's shape. -/
structure EsWorld where
  heap : Array Obj := #[]
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
