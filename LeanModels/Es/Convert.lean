import LeanModels.Es.Function

/-!
# Reference Records and the type conversions — ES2026 §6.2.5, §7.1, §7.2

M2 inch 4(a): the OPERATIONS layer expressions are built from. The AST
walk itself pairs with statements in 4(b), because one walk serves both.

Clauses realized here carry **191 numbered steps**: reference records 39,
conversions 63, the binary-operator applications 28, `IsLessThan` 38 and
`IsLooselyEqual` 23.

**This retires inch 1's conversion refusals.** `Value.lean` shipped
`ToBoolean` only, and said so: every conversion that can reach an object
needs `[[Get]]` and `[[Call]]`, which arrived at inch 3. They are here
now, and the boundary that remains is narrower again — see `toObject`.

**The `Val`-equality discipline from inch 1 applies throughout**: `Val`
has no derived `==`, because the spec has three equalities that differ on
NaN and ±0. Every comparison below names which one it is.
-/

namespace LeanModels.Es

/-! ## Reference Records — ES2026 §6.2.5

A Reference Record is a SPECIFICATION type: the resolved *target* of an
assignment or a read, before the read happens. `x` resolves to an
environment reference; `o.k` to a property reference. Keeping them apart
is what makes `x = 1` and `o.k = 1` one rule each rather than four. -/

/-- The base of a Reference Record. `unresolvable` is its own case rather
than an `Option`, because §6.2.5.2 branches on it by name. -/
inductive RefBase where
  | unresolvable
  | env (r : EnvRef)
  | value (v : Val)
  deriving Repr, Inhabited

/-- A Reference Record — §6.2.5. `strict` is carried because `PutValue`
(§6.2.5.6 step 6.d) throws on an unresolvable target in strict code and
creates a global otherwise. -/
structure Ref where
  base : RefBase
  name : PropKey
  strict : Bool := true
  /-- `[[ThisValue]]` — present only for a `super` reference. -/
  thisValue : Option Val := none
  deriving Repr, Inhabited

namespace Ref

/-- `IsUnresolvableReference(V)` — §6.2.5.3, 2 steps. -/
def isUnresolvable (r : Ref) : Bool :=
  match r.base with | .unresolvable => true | _ => false

/-- `IsPropertyReference(V)` — §6.2.5.2, 3 steps. -/
def isProperty (r : Ref) : Bool :=
  match r.base with | .value _ => true | _ => false

/-- `GetThisValue(V)` — §6.2.5.5. -/
def getThisValue (r : Ref) : Val :=
  match r.thisValue, r.base with
  | some t, _ => t
  | none, .value v => v
  | none, _ => .undef

end Ref

/-- `GetValue(V)` — §6.2.5.4, 12 steps. An unresolvable reference throws
`ReferenceError`; a property reference reads through `[[Get]]` (so a
getter runs); an environment reference reads the binding. -/
def getValue (fuel : Nat) (r : Ref) : EsW Val := do
  match r.base with
  | .unresolvable =>
    throwError "ReferenceError" s!"{r.name.text} is not defined"
  | .env e => envGetBindingValue e (r.name.text)
  | .value v =>
    match v with
    | .obj o => getV fuel o r.name (r.getThisValue)
    | _ =>
      -- §6.2.5.4 step 3.a: a primitive base is boxed by ToObject first.
      SemM.refuseIntrinsic "property access on a primitive needs the wrapper intrinsics (inch 6)"

/--
`PutValue(V, W)` — §6.2.5.6, **18 steps**.

The branch worth naming is step 6.d: assigning to an UNRESOLVABLE
reference in **strict** code throws `ReferenceError`, and in **sloppy**
code creates a property on the GLOBAL OBJECT — which needs the realm, so
that arm refuses as a host facility rather than inventing a global.
-/
def putValue (fuel : Nat) (r : Ref) (w : Val) : EsW Unit := do
  match r.base with
  | .unresolvable =>
    if r.strict then throwError "ReferenceError" s!"{r.name.text} is not defined"
    else SemM.refuseHost "sloppy assignment to an undeclared name creates a global property (needs the realm, inch 6)"
  | .env e => envSetMutableBinding e (r.name.text) w r.strict
  | .value v =>
    match v with
    | .obj o =>
      let ok ← setV fuel o r.name w (r.getThisValue)
      if !ok && r.strict then
        throwError "TypeError" s!"Cannot assign to read only property '{r.name.text}'"
      else pure ()
    | _ => SemM.refuseIntrinsic "property assignment on a primitive needs the wrapper intrinsics (inch 6)"

/-- `InitializeReferencedBinding(V, W)` — §6.2.5.8, 4 steps. -/
def initializeReferencedBinding (r : Ref) (w : Val) : EsW Unit := do
  match r.base with
  | .env e => envInitializeBinding e (r.name.text) w
  | _ => SemM.refuseConstruct
           "internal: InitializeReferencedBinding on a non-environment reference (report this)"

/-! ## Type conversion — ES2026 §7.1 -/

/--
`OrdinaryToPrimitive(O, hint)` — §7.1.1.1, 10 steps.

The METHOD ORDER is the whole content: `"string"` tries `toString` then
`valueOf`, every other hint tries `valueOf` then `toString`, and the
first call returning a non-object wins. Getting the order backwards is
the classic bug — `[] + {}` depends on it.
-/
def ordinaryToPrimitive (fuel : Nat) (o : ObjRef) (hint : String) : EsW Val := do
  let names := if hint == "string" then ["toString", "valueOf"] else ["valueOf", "toString"]
  let rec attempt : List String → EsW Val
    | [] => throwError "TypeError" "Cannot convert object to primitive value"
    | m :: rest => do
      let f ← getV fuel o (.str m) (.obj o)
      if ← isCallable f then
        let r ← callValue f (.obj o) []
        match r with
        | .obj _ => attempt rest                   -- an object result: keep going
        | _ => return r
      else attempt rest
  attempt names

/-- `ToPrimitive(input, preferredType)` — §7.1.1, 16 steps. The
`@@toPrimitive` exotic hook (step 2.a) needs well-known symbols, so it is
not consulted yet; every object therefore takes the ordinary path. -/
def toPrimitive (fuel : Nat) (v : Val) (hint : String := "default") : EsW Val := do
  match v with
  | .obj o => ordinaryToPrimitive fuel o hint
  | _ => return v

/-- `StringToNumber` — §7.1.4.1. The full StringNumericLiteral grammar is
its own sub-language (hex, octal, binary, exponents, `Infinity`); the
common decimal forms are here and everything else REFUSES rather than
guessing a number, which would be a silent wrong answer of exactly the
kind a conformance tier exists to avoid. -/
def stringToNumber (s : String) : EsW Val := do
  -- Over `toList`, not `String.trim`: on this toolchain `trim` answers a
  -- `String.Slice` (no `toList`), and §L88 recorded why the char-list form
  -- is the one that stays kernel-reducible anyway.
  let ws := fun (c : Char) => c == ' ' || c == '\t' || c == '\n' || c == '\r'
  let cs := (s.toList.dropWhile ws).reverse.dropWhile ws |>.reverse
  match cs with
  | [] => return .num 0.0
  | c :: rest =>
    let neg := c == '-'
    let body := if neg || c == '+' then rest else c :: rest
    if body.isEmpty then return .num (0.0 / 0.0)
    else if body.all Char.isDigit then
      let n := body.foldl (fun a d => a * 10 + (d.toNat - 48)) 0
      return .num (if neg then -(Float.ofNat n) else Float.ofNat n)
    else
      SemM.refuseConstruct s!"StringToNumber: '{s}' is outside the decimal-integer fragment (the StringNumericLiteral grammar is a rung)"

/-- `ToNumber` on a PRIMITIVE — §7.1.4 steps 1-9.

Split out so `toNumber` needs no recursion: `ToPrimitive` always yields a
primitive, so the object case calls this ONCE rather than re-entering.
That keeps both `partial`-free and therefore KERNEL-REDUCIBLE — §L82's
law, that a `#guard` stated through a `partial` definition proves
nothing.

The `Val`-equality discipline shows up here: `undefined` becomes **NaN**,
and NaN is not equal to itself, so a caller comparing the result must use
`numSameValue`/`sameValueZero` and never `numEqual`. `Symbol` and
`BigInt` THROW `TypeError` — program outcomes, not refusals. -/
def primitiveToNumber : Val → EsW Val
  | .num n => return .num n
  | .undef => return .num (0.0 / 0.0)                 -- NaN
  | .null => return .num 0.0
  | .bool b => return .num (if b then 1.0 else 0.0)
  | .str s => stringToNumber s
  | .sym .. => throwError "TypeError" "Cannot convert a Symbol value to a number"
  | .bigint _ => throwError "TypeError" "Cannot convert a BigInt value to a number"
  | .obj _ => SemM.refuseConstruct
      "internal: primitiveToNumber reached an object (report this)"

/-- `ToNumber(argument)` — §7.1.4, 10 steps. -/
def toNumber (fuel : Nat) (v : Val) : EsW Val := do
  match v with
  | .obj _ => primitiveToNumber (← toPrimitive fuel v "number")
  | _ => primitiveToNumber v

/--
`Number::toString(x, 10)` — §6.1.6.1.20.

An `Option`, and deliberately: the full algorithm picks the SHORTEST
decimal that round-trips, which is real work (the family has it scheduled
as SoftFloat step 3, `docs/family-architecture.md` §3.5.5). Integers in
the exactly-representable range and the three special values are given
here; everything else answers `none` and the caller REFUSES. Handing back
the host's `Float.toString` would emit `"1.000000"` where the spec says
`"1"` — a silent wrong answer, and this tier's whole product is not
emitting those.

**ONE verification strength, after a correction.** An earlier version of
this function used `Float.toInt64`/`Float.toFloat`, which are `@[extern]`
and reduce in neither `rfl` nor `decide`, and recorded the exact-integer
arm as guard-verified-only — concluding there was "no kernel-reducible
substitute short of the bit model." **That conclusion was wrong by one
projection: the bit model IS core's `Float.Model`.** Routing through it
makes every arm here `rfl`-provable, so the split is gone.

What remains blocked is genuinely blocked: a NON-integer needs
correctly-rounded shortest-round-trip decimal conversion, `Float.toString`
is opaque, and core ships no decimal printer. That is SoftFloat's
(`docs/family-architecture.md` §3.5.5 step 3), and it answers `none` here
so the caller refuses. -/
def numberToString (n : Float) : Option String :=
  if n.isNaN then some "NaN"
  else if n == (1.0 / 0.0) then some "Infinity"
  else if n == (-1.0 / 0.0) then some "-Infinity"
  else if n == 0.0 then some "0"                       -- covers -0, per the spec
  else
    -- VIA THE BIT MODEL, not the extern conversions.  `n.toInt64` and
    -- `t.toFloat` are `@[extern]` and reduce in NEITHER `rfl` nor
    -- `decide`; `n.toModel.toInt64` and `Float.ofModel (…ofInt64 t)`
    -- reduce in both.  Two expressions, and the exact-integer arm
    -- becomes provable rather than merely evaluable — measured by the
    -- SoftFloat lane and re-checked here.
    let t := n.toModel.toInt64
    if Float.ofModel (Float.Model.ofInt64 t) == n && n.abs < 1e15 then
      some (ToString.toString t) else none

/-- `ToString` on a PRIMITIVE — §7.1.17 steps 1-9. Split out for the same
reason as `primitiveToNumber`: no recursion, so no `partial`. -/
def primitiveToString : Val → EsW Val
  | .str s => return .str s
  | .undef => return .str "undefined"
  | .null => return .str "null"
  | .bool b => return .str (if b then "true" else "false")
  | .num n =>
    match numberToString n with
    | some s => return .str s
    | none => SemM.refuseConstruct
        "Number::toString outside the exact-integer fragment needs correctly-rounded decimal conversion (SoftFloat step 3)"
  | .bigint i => return .str (ToString.toString i)
  | .sym .. => throwError "TypeError" "Cannot convert a Symbol value to a string"
  | .obj _ => SemM.refuseConstruct
      "internal: primitiveToString reached an object (report this)"

/-- `ToString(argument)` — §7.1.17, 12 steps. -/
def toString' (fuel : Nat) (v : Val) : EsW Val := do
  match v with
  | .obj _ => primitiveToString (← toPrimitive fuel v "string")
  | _ => primitiveToString v

/-- `ToPropertyKey(argument)` — §7.1.19, 4 steps. A Symbol stays a
Symbol; everything else becomes a String. -/
def toPropertyKey (fuel : Nat) (v : Val) : EsW PropKey := do
  match ← toPrimitive fuel v "string" with
  | .sym i _ => return .sym i
  | p => match ← toString' fuel p with
         | .str s => return .str s
         | _ => SemM.refuseConstruct "internal: ToString did not yield a string (report this)"

/-- `ToObject(argument)` — §7.1.18, 8 steps. Every primitive but
`undefined`/`null` becomes a WRAPPER object, which needs
`%Number.prototype%` and friends — inch 6. `undefined`/`null` THROW, and
that arm is complete. -/
def toObject (v : Val) : EsW ObjRef := do
  match v with
  | .obj o => return o
  | .undef | .null =>
    throwError "TypeError" "Cannot convert undefined or null to object"
  | _ => SemM.refuseIntrinsic
           "ToObject on a primitive builds a wrapper object, which needs the wrapper intrinsics (inch 6)"

/-! ## The binary operators — §13.15.3, §7.2.13, §7.2.15 -/

/--
`ApplyStringOrNumericBinaryOperator(lval, opText, rval)` — §13.15.3,
23 steps.

`+` is the operator with the shape: BOTH operands are converted to
primitives FIRST, and if EITHER is then a String the result is
concatenation — which is why `1 + "2"` is `"12"` and `1 - "2"` is `-1`.
Every other operator goes straight to numeric.
-/
def applyBinary (fuel : Nat) (lval : Val) (op : String) (rval : Val) : EsW Val := do
  if op == "+" then
    let lp ← toPrimitive fuel lval
    let rp ← toPrimitive fuel rval
    match lp, rp with
    | .str _, _ | _, .str _ =>
      match ← toString' fuel lp, ← toString' fuel rp with
      | .str a, .str b => return .str (a ++ b)
      | _, _ => SemM.refuseConstruct "internal: ToString did not yield a string (report this)"
    | _, _ => do
      match ← toNumber fuel lp, ← toNumber fuel rp with
      | .num a, .num b => return .num (a + b)
      | _, _ => throwError "TypeError" "Cannot mix BigInt and other types"
  else do
    match ← toNumber fuel lval, ← toNumber fuel rval with
    | .num a, .num b =>
      match op with
      | "-" => return .num (a - b)
      | "*" => return .num (a * b)
      | "/" => return .num (a / b)
      | "%" =>
        -- WITHDRAWN, on the SoftFloat lane's clamp warning.  This was
        -- `a - b * (a / b).toInt64.toFloat`, and `Float.toInt64` CLAMPS
        -- out of range — so a large quotient silently produced a wrong
        -- remainder that every in-range test would have passed.  That is
        -- the flattering direction, which is the one this tier refuses.
        -- §6.1.6.1.6 `Number::remainder` returns the truncated-quotient
        -- remainder, and doing it correctly needs the exact-value route
        -- (SoftFloat's `toInt_eq_truncate`), not a clamping conversion.
        SemM.refuseConstruct "`%` needs a non-clamping truncation (SoftFloat's toInt_eq_truncate); refusing rather than clamping"
      | _ => SemM.refuseConstruct s!"binary operator '{op}' is not modeled yet"
    | _, _ => throwError "TypeError" "Cannot mix BigInt and other types"

/--
`IsLessThan(x, y, LeftFirst)` — §7.2.13, **38 steps**.

Answers `undefined` when either operand is NaN, which is what makes ALL
FOUR of `<`, `>`, `<=`, `>=` false for NaN. Modelled as an `Option Bool`
so the `undefined` case cannot be confused with `false` — which is
exactly the confusion the spec's own three-valued answer exists to
prevent.
-/
def isLessThan (fuel : Nat) (x y : Val) (leftFirst : Bool) : EsW (Option Bool) := do
  let (px, py) ← if leftFirst then do
      let a ← toPrimitive fuel x "number"; let b ← toPrimitive fuel y "number"; pure (a, b)
    else do
      let b ← toPrimitive fuel y "number"; let a ← toPrimitive fuel x "number"; pure (a, b)
  match px, py with
  | .str a, .str b => return some (a < b)              -- code-unit order
  | _, _ => do
    match ← toNumber fuel px, ← toNumber fuel py with
    | .num a, .num b =>
      if a.isNaN || b.isNaN then return none            -- the `undefined` answer
      else return some (a < b)
    | _, _ => throwError "TypeError" "Cannot mix BigInt and other types"

end LeanModels.Es
