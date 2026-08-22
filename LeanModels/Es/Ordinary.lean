import LeanModels.Es.Object

/-!
# The ordinary object's internal methods — ES2026 §10.1

M2 inch 2's second half. Each definition realizes one typed clause and is
cited `(ES2026, clause-id, step)`.

**Fuel is an INDEX, never a layer** (`docs/family-architecture.md` §3.4):
the prototype walk recurses, so `hasProperty`/`get`/`set` take a `fuel`
argument that decreases at the `[[Prototype]]` step. Exhaustion is
`Halt.timeout` and nothing else. Hidden in the state it would not be the
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
  | some o => Halt.ok (.ok o, w)
  | none => Halt.unsupported (esRefusal .construct "internal")
              s!"internal: dangling object reference {r} (report this)"

def store (r : ObjRef) (o : Obj) : EsW Unit := fun w =>
  Halt.ok (.ok (), w.set r o)

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
    | 0, _ => fun _ => Halt.timeout
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
  | 0, _, _ => fun _ => Halt.timeout
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
  | 0, _, _, _ => fun _ => Halt.timeout
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
  | 0, _, _, _, _, _ => fun _ => Halt.timeout
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
            -- step 2.e.iv: a VALUE-ONLY redefinition on the receiver
            ordinaryDefineOwnProperty rr k { value := some v }
          | none =>
            -- step 2.f: CreateDataProperty on the receiver
            ordinaryDefineOwnProperty rr k (PropDesc.data v true true true)
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
  Halt.ok (.ok r, w')

end LeanModels.Es
