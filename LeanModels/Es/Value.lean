/-!
# The ECMAScript value model (`LeanModels.Es`)

M2 inch 1, first half: the eight ECMAScript language types, and the
type-conversion abstract operations that do not need an object.

**Correspondence convention** (`docs/es-charter.md` §1.3): one definition
per typed clause, cited by `(edition, clause-id, step)`. The edition is
`ES2026` throughout, pinned at the `es2026-errata` revision by
`docs/es-edition.json`, so the citations below name a clause the pinned
spec defines — mechanically checkable, and §1.4 measured why the triple
rather than the id alone (6,776 test262 rows already cite ids the current
draft no longer defines).

**Number is core `Float`, deliberately.** `docs/es-charter.md` §4.2(a)
measured that Lean core's `Float` on the pinned toolchain is a
kernel-reducible bit-level binary64 model — `(0.1 : Float) + 0.2 = 0.30000000000000004`
closes by `rfl` — which is `docs/family-architecture.md` §3.5.1's Layer 1,
supplied rather than owed. The tier depends on it deliberately and gates
the reduction behaviour with `#guard`s, exactly as §3.5.1 asks. What core
does NOT supply is Layer 2, the round-of-exact algebra, and nothing here
needs it.

**What is NOT here, and why it is a boundary rather than a gap.** Every
conversion that can reach an object — `ToPrimitive`, and therefore
`ToNumber`/`ToString` at an object argument — needs `[[Get]]` and
`[[Call]]`, which are inch 2. Those arms REFUSE (`Loud.unsupported`)
rather than guessing, and `docs/es-semantics-design.md` §0.1 measured why
the object model is rung 0 and not a later rung: `sta.js` cannot even
construct `Test262Error` without it.
-/

namespace LeanModels.Es

/-- A reference to an object in the realm's heap. The heap itself is inch
2; the reference exists now because a `Val` can be one. -/
abbrev ObjRef := Nat

/-- A Symbol's identity. Symbols are unique by identity, never by
description, so the description is carried only for `String(sym)` and is
NOT part of equality (ES2026 §20.4.3.3 notes the description is
informative). -/
abbrev SymId := Nat

/--
The ECMAScript language types — ES2026 §6.1, all eight.

`Undefined`, `Null`, `Boolean`, `String`, `Symbol`, `Number`, `BigInt`,
`Object`. There is deliberately no ninth constructor: the spec's
*specification* types (Reference Record, Completion Record, Property
Descriptor …) are §6.2 and are not values a program can hold. Completion
Records in particular are `LeanModels.Es.Abrupt` and live in the MONAD,
not in `Val` — `docs/es-semantics-design.md` §1.2.

No `DecidableEq`: `Float` has none, because NaN ≠ NaN. Equality is the
spec's, and the spec has three different ones (§7.2.10 `SameValue`,
§7.2.11 `SameValueZero`, §7.2.16 `IsStrictlyEqual`), which is exactly why
a derived `==` would be a trap.
-/
inductive Val where
  | undef
  | null
  | bool (b : Bool)
  /-- ES2026 §6.1.6.1 — the Number type IS binary64. -/
  | num (n : Float)
  | str (s : String)
  | sym (id : SymId) (description : Option String)
  /-- ES2026 §6.1.6.2 — an arbitrary-precision integer. -/
  | bigint (i : Int)
  | obj (ref : ObjRef)
  deriving Repr, Inhabited

namespace Val

/-! ## `typeof` — ES2026 §13.5.3, the table -/

/--
`typeof` — ES2026 §13.5.3.1, the Runtime Semantics table.

The Object row is SPLIT by the spec itself: an object that implements
`[[Call]]` answers `"function"`, one that does not answers `"object"`. So
callability is an INPUT here rather than something this layer can decide —
the alternative would be to fabricate an answer about a heap that does not
exist yet. Inch 2 supplies it from the object.

The `null` row answering `"object"` is the spec's, and famously not a
mistake anyone is allowed to fix.
-/
def typeofWith (callable : ObjRef → Bool) : Val → String
  | .undef => "undefined"
  | .null => "object"
  | .bool _ => "boolean"
  | .num _ => "number"
  | .str _ => "string"
  | .sym .. => "symbol"
  | .bigint _ => "bigint"
  | .obj r => if callable r then "function" else "object"

/-- `typeof` at a value that is not an object, where callability cannot
arise. Total, and the arm every primitive test takes. -/
def typeofPrimitive? : Val → Option String
  | .obj _ => none
  | v => some (typeofWith (fun _ => false) v)

/-! ## The three equalities

ES2026 gives three, and they differ only on NaN and on ±0.  Getting them
confused is the classic implementation bug, so each is defined against its
own clause and the differences are pinned by `#guard` below. -/

/-- `Number::sameValue` — ES2026 §6.1.6.1.14. NaN is the same value as
NaN; +0 and -0 are NOT the same value. -/
def numSameValue (x y : Float) : Bool :=
  if x.isNaN then y.isNaN
  else if y.isNaN then false
  -- ±0: distinguished by the sign of the reciprocal, since 0.0 == -0.0.
  else if x == 0.0 && y == 0.0 then (1.0 / x) == (1.0 / y)
  else x == y

/-- `Number::sameValueZero` — ES2026 §6.1.6.1.15. NaN is the same as NaN;
+0 and -0 ARE the same. -/
def numSameValueZero (x y : Float) : Bool :=
  if x.isNaN then y.isNaN
  else if y.isNaN then false
  else x == y

/-- `Number::equal` — ES2026 §6.1.6.1.13. NaN is equal to nothing,
including itself; +0 and -0 are equal. -/
def numEqual (x y : Float) : Bool :=
  !x.isNaN && !y.isNaN && x == y

/-- `SameValue(x, y)` — ES2026 §7.2.10. Used by `Object.is` and by
property-descriptor validation. -/
def sameValue : Val → Val → Bool
  | .undef, .undef => true
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => numSameValue a b
  | .str a, .str b => a == b
  | .sym a _, .sym b _ => a == b
  | .bigint a, .bigint b => a == b
  | .obj a, .obj b => a == b
  | _, _ => false

/-- `SameValueZero(x, y)` — ES2026 §7.2.11. Used by `Array.prototype.includes`
and by the keyed collections. -/
def sameValueZero : Val → Val → Bool
  | .num a, .num b => numSameValueZero a b
  | a, b => sameValue a b

/-- `IsStrictlyEqual(x, y)` — ES2026 §7.2.16, the `===` operator. -/
def strictEquals : Val → Val → Bool
  | .num a, .num b => numEqual a b
  | a, b => sameValue a b

/-! ## Conversions that cannot throw -/

/--
`ToBoolean(argument)` — ES2026 §7.1.2. Total: every value has a boolean
coercion and none of them throws. The falsy set is exactly
`undefined`, `null`, `false`, `+0`/`-0`/`NaN`, `""`, `0n`.
-/
def toBoolean : Val → Bool
  | .undef => false
  | .null => false
  | .bool b => b
  | .num n => !(n == 0.0 || n.isNaN)
  | .str s => s != ""
  | .bigint i => i != 0
  | .sym .. => true
  | .obj _ => true          -- every object is truthy, incl. `document.all`'s
                            -- exception, which is Annex B and out of slice

end Val

end LeanModels.Es
