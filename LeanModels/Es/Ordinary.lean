import LeanModels.Es.Object

/-!
# The ordinary object's internal methods — ES2026 §10.1

M2 inch 2's second half. Each definition realizes one typed clause and is
cited `(ES2026, clause-id, step)`.

**Fuel is an INDEX, never a layer** (`docs/family-architecture.md` §3.4):
the prototype walk recurses, so `hasProperty`/`get`/`set` take a `fuel`
argument that decreases at the `[[Prototype]]` step. Exhaustion is
`.error .timeout` and nothing else. Hidden in the state it would not be the
recursion argument and the interpreter could not show termination.

**Accessor properties REFUSE.** `[[Get]]` on an accessor calls the getter,
which needs `[[Call]]` — inch 4. That arm raises
`unsupported`-class, loudly, rather than inventing a
value. Data properties are complete, and `sta.js` uses only data
properties, so §0.1's floor is cleared without the refusal firing.
-/

namespace LeanModels.Es

/-- Read an object, or refuse: a dangling `ObjRef` is an INTERNAL fault,
not a program error, so it is not in `ρ` and no `try` can catch it. -/
def deref (r : ObjRef) : EsW Obj := fun w =>
  match w.get? r with
  | some o => .ok (.ok o, w)
  | none => .error (.unsupported (esRefusal .construct "internal")
              s!"internal: dangling object reference {r} (report this)" none)

def store (r : ObjRef) (o : Obj) : EsW Unit := fun w =>
  .ok (.ok (), w.set r o)

/-! ## The simple slots -/

/-- `OrdinaryGetPrototypeOf(O)` — ES2026 §10.1.1.1, 1 step. -/
def ordinaryGetPrototypeOf (r : ObjRef) : EsW (Option ObjRef) :=
  return (← deref r).proto

/-- `OrdinaryIsExtensible(O)` — ES2026 §10.1.3.1, 1 step. -/
def ordinaryIsExtensible (r : ObjRef) : EsW Bool :=
  return (← deref r).extensible

/-- `OrdinaryPreventExtensions(O)` — ES2026 §10.1.4.1, 2 steps. -/
def ordinaryPreventExtensions (r : ObjRef) : EsW Bool := do
  store r { (← deref r) with extensible := false }
  return true

/-- `OrdinarySetPrototypeOf(O, V)` — ES2026 §10.1.2.1, 16 steps.

The cycle check (steps 8-11) is what the 16 steps are mostly for: walking
`V`'s prototype chain looking for `O`, and refusing the assignment rather
than building a cycle. It is fuel-bounded here for the same reason the
chain walks below are. -/
def ordinarySetPrototypeOf (fuel : Nat) (r : ObjRef) (v : Option ObjRef) : EsW Bool := do
  let o ← deref r
  if o.proto == v then return true
  if !o.extensible then return false
  -- steps 8-11: reject a prototype cycle
  let rec walk : Nat → Option ObjRef → EsW Bool
    | 0, _ => fun _ => .error .timeout
    | _, none => return true
    | n + 1, some p =>
      if p == r then return false
      else do walk n (← deref p).proto
  if ← walk fuel v then
    store r { o with proto := v }
    return true
  else
    return false

/-! ## `[[GetOwnProperty]]` — §10.1.5 -/

/-- `OrdinaryGetOwnProperty(O, P)` — ES2026 §10.1.5.1, 13 steps. Returns a
COMPLETE descriptor (steps 4-8 populate every field) or `undefined`. It
never throws. -/
def ordinaryGetOwnProperty (r : ObjRef) (k : PropKey) : EsW (Option PropDesc) := do
  match (← deref r).find? k with
  | none => return none
  | some d => return some d.complete

/-! ## `[[DefineOwnProperty]]` — §10.1.6, and its 34-step validator -/

/--
`ValidateAndApplyPropertyDescriptor(O, P, extensible, Desc, current)` —
ES2026 §10.1.6.3, **34 steps**, the longest algorithm in the ordinary
object model and the one an implementation most often gets subtly wrong.

`O` is `undefined` when the caller only wants the VALIDATION (that is
step 1's whole point: `IsCompatiblePropertyDescriptor` calls it with no
object), so here it is an `Option ObjRef` and the write is skipped when it
is absent.

The shape is: absent `current` means "creating" (steps 2-5); present
`current` means "redefining", and steps 6-15 are the permission checks a
non-configurable property imposes.
-/
def validateAndApplyPropertyDescriptor
    (target : Option ObjRef) (k : PropKey) (extensible : Bool)
    (desc : PropDesc) (current : Option PropDesc) : EsW Bool := do
  match current with
  | none =>
    -- step 2: the property does not exist yet
    if !extensible then return false
    if let some r := target then
      -- steps 2.c-2.d: an accessor descriptor becomes an accessor
      -- property; anything else becomes a data property with the absent
      -- fields defaulted (which is exactly `complete`'s job).
      store r ((← deref r).put k desc.complete)
    return true
  | some cur =>
    -- step 3: every field of `Desc` absent => nothing to do
    if desc.value.isNone && desc.writable.isNone && desc.get.isNone
       && desc.set.isNone && desc.enumerable.isNone && desc.configurable.isNone then
      return true
    -- steps 4-5: a non-configurable property refuses most changes
    if cur.configurable == some false then
      if desc.configurable == some true then return false
      if desc.enumerable.isSome && desc.enumerable != cur.enumerable then return false
      -- step 5.c: a non-configurable property cannot change KIND
      if !desc.isGeneric && (desc.isAccessor != cur.isAccessor) then return false
      -- step 5.d: a non-configurable ACCESSOR cannot change its functions
      if cur.isAccessor then
        if desc.get.isSome && !(Val.sameValue (desc.get.getD .undef) (cur.get.getD .undef)) then
          return false
        if desc.set.isSome && !(Val.sameValue (desc.set.getD .undef) (cur.set.getD .undef)) then
          return false
      -- step 5.e: a non-configurable, non-writable DATA property is frozen
      else if cur.writable == some false then
        if desc.writable == some true then return false
        if desc.value.isSome && !(Val.sameValue (desc.value.getD .undef) (cur.value.getD .undef)) then
          return false
    -- step 6: apply
    if let some r := target then
      let o ← deref r
      -- Changing KIND resets the other half's fields to their defaults
      -- (steps 6.b-6.c), which is why this is not a simple field merge.
      let merged : PropDesc :=
        if desc.isData && cur.isAccessor then
          { value := desc.value.orElse (fun _ => some .undef),
            writable := desc.writable.orElse (fun _ => some false),
            enumerable := desc.enumerable.orElse (fun _ => cur.enumerable),
            configurable := desc.configurable.orElse (fun _ => cur.configurable) }
        else if desc.isAccessor && cur.isData then
          { get := desc.get.orElse (fun _ => some .undef),
            set := desc.set.orElse (fun _ => some .undef),
            enumerable := desc.enumerable.orElse (fun _ => cur.enumerable),
            configurable := desc.configurable.orElse (fun _ => cur.configurable) }
        else
          { value := desc.value.orElse (fun _ => cur.value),
            writable := desc.writable.orElse (fun _ => cur.writable),
            get := desc.get.orElse (fun _ => cur.get),
            set := desc.set.orElse (fun _ => cur.set),
            enumerable := desc.enumerable.orElse (fun _ => cur.enumerable),
            configurable := desc.configurable.orElse (fun _ => cur.configurable) }
      store r (o.put k merged)
    return true

/-- `OrdinaryDefineOwnProperty(O, P, Desc)` — ES2026 §10.1.6.1, 3 steps. -/
def ordinaryDefineOwnProperty (r : ObjRef) (k : PropKey) (desc : PropDesc) : EsW Bool := do
  let current ← ordinaryGetOwnProperty r k
  let extensible := (← deref r).extensible
  validateAndApplyPropertyDescriptor (some r) k extensible desc current

/-! ## The chain walks — §10.1.7, §10.1.8, §10.1.9 -/

/-- `OrdinaryHasProperty(O, P)` — ES2026 §10.1.7.1, 6 steps. Walks
`[[Prototype]]`; fuel bounds the walk. -/
def ordinaryHasProperty : Nat → ObjRef → PropKey → EsW Bool
  | 0, _, _ => fun _ => .error .timeout
  | n + 1, r, k => do
    if (← ordinaryGetOwnProperty r k).isSome then return true
    match (← deref r).proto with
    | none => return false
    | some p => ordinaryHasProperty n p k

/--
`OrdinaryGet(O, P, Receiver)` — ES2026 §10.1.8.1, 10 steps.

Step 8 invokes the getter, which needs `[[Call]]`.  **SUPERSEDED as of
inch 3 by `Function.getV`**, which is the complete §10.1.8.1; this
remains its DATA-PROPERTY fragment, because Lean forbids `Ordinary.lean`
importing `Function.lean` (the import would cycle).  An accessor refuses
HERE and succeeds through `getV`. A data
property is complete, and step 7's "if the getter is `undefined` return
`undefined`" is honoured before the refusal, because that arm needs no
call.
-/
def ordinaryGet : Nat → ObjRef → PropKey → Val → EsW Val
  | 0, _, _, _ => fun _ => .error .timeout
  | n + 1, r, k, receiver => do
    match ← ordinaryGetOwnProperty r k with
    | none =>
      match (← deref r).proto with
      | none => return .undef                          -- step 3.b
      | some p => ordinaryGet n p k receiver           -- step 3.c
    | some d =>
      if d.isData then return d.value.getD .undef      -- step 5
      else
        let getter := d.get.getD .undef
        match getter with
        | .undef => return .undef                      -- step 7
        | _ => SemM.refuseConstruct
                 "accessor property: [[Get]] must call the getter, which needs [[Call]] (inch 4)"

/-! ## Array exotic objects — ES2026 §10.4.2

An Array's `length` is LIVE in both directions: writing an index at or past
it grows it (§10.4.2.1 step 3.h), and writing a smaller `length` DELETES the
elements above it (§10.4.2.4). Neither happens for an ordinary object with a
`length` data property, which is exactly why `Obj` carries `ExoticKind` and
this is a different `[[DefineOwnProperty]]` rather than a convention.

**No `Nat`/`Float` conversion appears below.** An earlier shape converted the
length through `ToUint32` into a `Nat` and needed `Int64.toInt`/`Int.toNat`.
Indices arrive from `PropKey.arrayIndex?` as `Nat` and lengths live as
`Float`, and `Nat.toFloat` is total and exact over `[0, 2^32)` — so every
comparison happens in `Float` and the conversion that could clamp is simply
never made. `n.toInt64` is `@[extern]` (kernel-opaque) AND saturating; that
is the defect that withdrew `%` in inch 4.
-/

/-- Is this Number an exact non-negative integer below `2^32` — the
`ToUint32` fixpoint §10.4.2.4 step 5 tests with `SameValueZero`?

A ROUND TRIP through `Float.Model`, not a range check on a converted
value: the `@[extern]` path SATURATES, so `1e30` would convert to
`2^63 - 1` and then pass a naive range test. The two expressions are the
ones `numberToString` already uses. -/
def isExactUint32 (n : Float) : Bool :=
  Float.ofModel (Float.Model.ofInt64 n.toModel.toInt64) == n
    && n ≥ 0.0 && n < 4294967296.0

/-- The `length` of an Array, and whether it is writable. -/
def arrayLength (o : Obj) : Float × Bool :=
  let d := o.find? (.str "length")
  ((match d.bind (·.value) with | some (.num f) => f | _ => 0.0),
   (match d.bind (·.writable) with | some b => b | none => true))

/-- Store a new `length` VALUE while preserving its attributes — which are
`writable: true, enumerable: false, configurable: false` and must stay so
(§10.4.2.2 step 6). -/
def putLength (o : Obj) (n : Float) : Obj :=
  let d := (o.find? (.str "length")).getD (PropDesc.data (.num 0.0) true false false)
  o.put (.str "length") { d with value := some (.num n) }

/--
`ArraySetLength(A, Desc)` — ES2026 §10.4.2.4, 34 steps.

The truncating half of the live `length`. `a.length = 1` on `[10, 20]`
must DELETE index 1, not merely renumber — `hasOwnProperty(1)` is `false`
afterwards, and that is the oracle case this clause exists for.

**The descending walk is replaced by a filter, and the arm where that
would differ REFUSES.** §10.4.2.4 steps 17+ count DOWN so that a
non-configurable element stops the truncation partway and `length` is left
just above it. Deleting every own index at or above the new length is the
same SET whenever every element is configurable — which is true of every
index this tier can create, since only `Object.defineProperty` (inch 6)
can make one otherwise. So the difference is unreachable, and rather than
rely on that it is checked and refused.
-/
def arraySetLength (r : ObjRef) (desc : PropDesc) : EsW Bool := do
  match desc.value with
  -- step 1: no [[Value]] means this is an attribute-only redefinition
  | none => ordinaryDefineOwnProperty r (.str "length") desc
  | some (.num newLen) =>
    -- steps 3-5: ToUint32 must be a FIXPOINT of ToNumber, else RangeError.
    -- `throwError` lives in `Env.lean`, which is ABOVE this file, so the
    -- raise is spelled out; it is the same `SemM.raise` that clause uses.
    if !isExactUint32 newLen then
      SemM.raise (.throw (.str "RangeError: Invalid array length"))
    else do
      let o ← deref r
      let (oldLen, writable) := arrayLength o
      if newLen ≥ oldLen then                                  -- step 11
        store r (putLength o newLen)
        return true
      else if !writable then return false                      -- step 12
      else do
        let doomed := o.props.filter (fun p =>
          match p.1.arrayIndex? with
          | some i => newLen ≤ i.toFloat
          | none => false)
        if doomed.any (fun p => p.2.configurable == some false) then
          SemM.refuseConstruct
            "array truncation across a non-configurable element needs §10.4.2.4's descending walk"
        else do
          let kept := o.props.filter (fun p =>
            match p.1.arrayIndex? with
            | some i => i.toFloat < newLen
            | none => true)
          store r (putLength { o with props := kept } newLen)
          return true
  | some _ => SemM.raise (.throw (.str "RangeError: Invalid array length"))

/--
`[[DefineOwnProperty]]` for an Array — ES2026 §10.4.2.1, 18 steps.

The growing half: defining an index at or past `length` sets `length` to
`index + 1` (step 3.h), which is why `a = [10, 20]; a[5] = 99` leaves
`a.length` at 6 and not 2.
-/
def arrayDefineOwnProperty (r : ObjRef) (k : PropKey) (desc : PropDesc) : EsW Bool := do
  if k == PropKey.str "length" then arraySetLength r desc      -- step 1
  else
    match k.arrayIndex? with
    | none => ordinaryDefineOwnProperty r k desc               -- step 3 falls through
    | some idx => do
      let (oldLen, writable) := arrayLength (← deref r)
      -- step 3.i: past the end of a non-writable length is a refusal to write
      if idx.toFloat ≥ oldLen && !writable then return false
      if !(← ordinaryDefineOwnProperty r k desc) then return false
      if idx.toFloat ≥ oldLen then                             -- step 3.h
        store r (putLength (← deref r) (idx.toFloat + 1.0))
      return true

/-- `O.[[DefineOwnProperty]](P, Desc)` — the DISPATCHER, and the spelling
every caller of the internal method should use. `ordinaryDefineOwnProperty`
is §10.1.6's ordinary implementation; this is the method itself. -/
def esDefineOwnProperty (r : ObjRef) (k : PropKey) (desc : PropDesc) : EsW Bool := do
  match (← deref r).exotic with
  | some .array => arrayDefineOwnProperty r k desc
  | none => ordinaryDefineOwnProperty r k desc

/-- `ArrayCreate(length)` — ES2026 §10.4.2.2, 7 steps. The prototype is
`%Array.prototype%`, a realm intrinsic (inch 6), so it is `none` here for
the same reason `ordinaryFunctionCreate`'s is. -/
def arrayCreate (len : Nat) : EsW ObjRef := fun w =>
  let (r, w') := w.alloc
    { proto := none, exotic := some .array,
      props := [(.str "length", PropDesc.data (.num len.toFloat) true false false)] }
  .ok (.ok r, w')

/-- `CreateDataProperty(O, P, V)` — ES2026 §7.3.4, 2 steps: a fresh
enumerable, writable, configurable data property, through the object's OWN
`[[DefineOwnProperty]]`. **Every literal's property goes through here** —
an evaluator that appended to `props` directly would lose both the
duplicate-key rule and the Array's live `length`. -/
def createDataProperty (r : ObjRef) (k : PropKey) (v : Val) : EsW Bool :=
  esDefineOwnProperty r k (PropDesc.data v true true true)

/-- `CreateDataPropertyOrThrow(O, P, V)` — ES2026 §7.3.5, 3 steps. -/
def createDataPropertyOrThrow (r : ObjRef) (k : PropKey) (v : Val) : EsW Unit := do
  if ← createDataProperty r k v then pure ()
  else SemM.raise (.throw (.str s!"TypeError: cannot create property {k.text}"))

/--
`OrdinarySetWithOwnDescriptor(O, P, V, Receiver, ownDesc)` —
ES2026 §10.1.9.2, 20 steps, and `OrdinarySet` (§10.1.9.1, 2 steps) is its
caller.

The subtlety the 20 steps exist for: when `Receiver` is not `O`, the write
lands on the RECEIVER, and only if the receiver's own property is a
writable data property. That is what makes `obj.x = 1` through a prototype
create an own property on `obj` rather than mutating the prototype.
-/
def ordinarySetWithOwnDescriptor :
    Nat → ObjRef → PropKey → Val → Val → Option PropDesc → EsW Bool
  | 0, _, _, _, _, _ => fun _ => .error .timeout
  | n + 1, r, k, v, receiver, ownDesc => do
    match ownDesc with
    | none =>
      match (← deref r).proto with
      | some p =>
        -- step 1.b.i: RETURN the parent's [[Set]] — a real recursion, not a
        -- peek at the parent's own descriptor.  The difference is
        -- observable when the parent also lacks the property (the walk must
        -- continue) or when the parent's property is an accessor (the
        -- parent's SETTER is what runs).
        ordinarySetWithOwnDescriptor n p k v receiver (← ordinaryGetOwnProperty p k)
      | none =>
        -- step 1.c: treat as a fresh writable data property and fall through
        ordinarySetWithOwnDescriptor n r k v receiver
          (some (PropDesc.data .undef true true true))
    | some d =>
      if d.isData then
        if d.writable == some false then return false            -- step 2.b
        match receiver with
        | .obj rr =>
          match ← ordinaryGetOwnProperty rr k with
          | some existing =>
            if existing.isAccessor then return false             -- step 2.e.ii
            if existing.writable == some false then return false -- step 2.e.iii
            -- step 2.e.iv: a VALUE-ONLY redefinition on the receiver.
            -- Through the DISPATCHER, not the ordinary implementation: on an
            -- Array this is the step that grows `length`, and `a[5] = 99`
            -- arrives here.
            esDefineOwnProperty rr k { value := some v }
          | none =>
            -- step 2.f: CreateDataProperty on the receiver — the AO by name,
            -- which is itself the dispatcher.
            createDataProperty rr k v
        | _ => return false                                      -- step 2.c
      else
        match d.set.getD .undef with
        | .undef => return false                                 -- step 4
        | _ => SemM.refuseConstruct
                 "accessor property: [[Set]] must call the setter, which needs [[Call]] (inch 4)"

/-- `OrdinarySet(O, P, V, Receiver)` — ES2026 §10.1.9.1, 2 steps. -/
def ordinarySet (fuel : Nat) (r : ObjRef) (k : PropKey) (v : Val) (receiver : Val) : EsW Bool := do
  ordinarySetWithOwnDescriptor fuel r k v receiver (← ordinaryGetOwnProperty r k)

/-! ## `[[Delete]]` and `[[OwnPropertyKeys]]` -/

/-- `OrdinaryDelete(O, P)` — ES2026 §10.1.10.1, 6 steps. A
non-configurable property refuses deletion. -/
def ordinaryDelete (r : ObjRef) (k : PropKey) : EsW Bool := do
  match ← ordinaryGetOwnProperty r k with
  | none => return true                                      -- step 3
  | some d =>
    if d.configurable == some true then
      store r ((← deref r).erase k)
      return true
    else return false                                        -- step 5

/--
`OrdinaryOwnPropertyKeys(O)` — ES2026 §10.1.11.1, 8 steps.

The ORDER is normative and is the reason this is not just `props.map (·.1)`:
integer-index keys first in ASCENDING NUMERIC order, then the remaining
string keys in property-creation order, then symbol keys in creation
order.
-/
def ordinaryOwnPropertyKeys (r : ObjRef) : EsW (List PropKey) := do
  let ks := (← deref r).props.map (·.1)
  let idx := (ks.filterMap (fun k => (k.arrayIndex?).map (fun n => (n, k)))).mergeSort
               (fun a b => a.1 ≤ b.1)
  let strs := ks.filter (fun k => k.arrayIndex?.isNone && match k with | .str _ => true | _ => false)
  let syms := ks.filter (fun k => match k with | .sym _ => true | _ => false)
  return idx.map (·.2) ++ strs ++ syms

/-- `OrdinaryObjectCreate(proto)` — ES2026 §10.1.12.1, 5 steps. -/
def ordinaryObjectCreate (proto : Option ObjRef) : EsW ObjRef := fun w =>
  let (r, w') := w.alloc { proto := proto }
  .ok (.ok r, w')

end LeanModels.Es
