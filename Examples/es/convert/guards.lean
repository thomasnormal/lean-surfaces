import LeanModels.Es

/-!
# M2 inch 4(a)'s acceptance: reference records and the type conversions

`docs/backlog/es.md`'s inch 4(a). Every `#guard` is kernel-decided — the
conversions are deliberately NOT `partial` (§L82: a `#guard` through a
`partial` definition proves nothing), which is why `toNumber`/`toString'`
split their primitive case out instead of recursing.

**Inch 1's conversion refusals retire here.** `Value.lean` shipped
`ToBoolean` alone because everything else can reach an object; objects
arrived at inch 2 and `[[Call]]` at inch 3, so `ToPrimitive` and its
dependents are real now.
-/

namespace Examples.es.convert

open LeanModels.Es

def yields (m : EsW Val) (v : Val) : Bool :=
  match SemM.run m default with
  | .ok (.ok r, _) => Val.sameValue r v
  | _ => false

def throwsKind (m : EsW α) (k : String) : Bool :=
  match SemM.run m default with
  | .ok (.error (.throw (.str s)), _) => s.startsWith k
  | _ => false

def refusesClass (m : EsW α) (cls : String) : Bool :=
  match SemM.run m default with
  | .error (.unsupported c _ _) => c.className == cls
  | _ => false

/-! ## `ToNumber` — §7.1.4, and the NaN paths need `sameValue`

`Val.sameValue` is what compares these, never a derived `==`: `undefined`
becomes NaN, and NaN is not `numEqual` to itself. Inch 1's discipline,
applied. -/

#guard yields (toNumber 10 .undef) (.num (0.0 / 0.0))     -- NaN, by sameValue
#guard yields (toNumber 10 .null) (.num 0.0)
#guard yields (toNumber 10 (.bool true)) (.num 1.0)
#guard yields (toNumber 10 (.bool false)) (.num 0.0)
#guard yields (toNumber 10 (.str "42")) (.num 42.0)
#guard yields (toNumber 10 (.str "-7")) (.num (-7.0))
#guard yields (toNumber 10 (.str "")) (.num 0.0)
#guard yields (toNumber 10 (.str "   12  ")) (.num 12.0)
#guard yields (toNumber 10 (.str "+5")) (.num 5.0)

/- `ToNumber(undefined)` is NaN, so it is NOT strictly equal to itself —
the row that shows the three equalities still matter after conversion. -/
#guard match SemM.run (toNumber 10 .undef) default with
  | .ok (.ok r, _) => (Val.strictEquals r r) == false && (Val.sameValue r r) == true
  | _ => false

/- A Symbol and a BigInt THROW — program outcomes in `ρ`, not refusals. -/
#guard throwsKind (toNumber 10 (.sym 0 none)) "TypeError"
#guard throwsKind (toNumber 10 (.bigint 1)) "TypeError"

/- A string outside the decimal-integer fragment REFUSES rather than
guessing: the StringNumericLiteral grammar is its own rung. -/
#guard refusesClass (toNumber 10 (.str "0x10")) "unsupported"
#guard refusesClass (toNumber 10 (.str "1e3")) "unsupported"

/-! ## `ToString` — §7.1.17 -/

#guard yields (toString' 10 .undef) (.str "undefined")
#guard yields (toString' 10 .null) (.str "null")
#guard yields (toString' 10 (.bool true)) (.str "true")
#guard yields (toString' 10 (.num 42.0)) (.str "42")
#guard yields (toString' 10 (.num (-7.0))) (.str "-7")
#guard yields (toString' 10 (.num (0.0 / 0.0))) (.str "NaN")
#guard yields (toString' 10 (.num (1.0 / 0.0))) (.str "Infinity")

/- `-0` renders as `"0"` — §6.1.6.1.20, and it is the row that separates
`String(-0)` from `Object.is(-0, 0)`. -/
#guard yields (toString' 10 (.num (-0.0))) (.str "0")

/- A non-integer REFUSES rather than emitting the host's `"1.000000"`.
The correctly-rounded shortest-round-trip algorithm is SoftFloat step 3. -/
#guard refusesClass (toString' 10 (.num 0.5)) "unsupported"

#guard throwsKind (toString' 10 (.sym 0 none)) "TypeError"

/-! ## `ToPrimitive` — §7.1.1, and the METHOD ORDER is the content

`"string"` tries `toString` then `valueOf`; every other hint tries
`valueOf` then `toString`. `[] + {}` depends on it. -/

#guard yields (do
  let vo ← ordinaryFunctionCreate none (.builtin "%identity%") none .strict true
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "valueOf") (PropDesc.data (.obj vo) true false true)
  toPrimitive 10 (.obj o) "number") .undef

/- A NON-callable `valueOf` is skipped, and the walk continues — §7.1.1.1
step 3.b tests callability, it does not assume. -/
#guard yields (do
  let ts ← ordinaryFunctionCreate none (.builtin "%argCount%") none .strict true
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "valueOf") (PropDesc.data (.num 1.0) true false true)
  let _ ← ordinaryDefineOwnProperty o (.str "toString") (PropDesc.data (.obj ts) true false true)
  toPrimitive 10 (.obj o) "number") (.num 0.0)

/- An object with NEITHER method throws `TypeError` — §7.1.1.1 step 4. -/
#guard throwsKind (do
  let o ← ordinaryObjectCreate none
  toPrimitive 10 (.obj o) "number") "TypeError"

/-! ## `ToPropertyKey` — §7.1.19: a Symbol stays a Symbol -/

#guard match SemM.run (toPropertyKey 10 (.sym 7 none)) default with
  | .ok (.ok k, _) => k == PropKey.sym 7
  | _ => false

#guard match SemM.run (toPropertyKey 10 (.num 3.0)) default with
  | .ok (.ok k, _) => k == PropKey.str "3"
  | _ => false

/-! ## `ToObject` — §7.1.18: the `undefined`/`null` arm is COMPLETE -/

#guard throwsKind (toObject .undef) "TypeError"
#guard throwsKind (toObject .null) "TypeError"
/- …and a primitive needs the wrapper intrinsics, so it refuses. -/
#guard refusesClass (toObject (.num 1.0)) "environment"

/-! ## Reference Records — §6.2.5 -/

/- An unresolvable reference THROWS on read — §6.2.5.4 step 1. -/
#guard throwsKind (getValue 10 { base := .unresolvable, name := .str "x" }) "ReferenceError"

/- An environment reference reads the binding. -/
#guard yields (do
  let e ← newDeclarativeEnvironment none
  envCreateMutableBinding e "x" false
  envInitializeBinding e "x" (.num 5.0)
  getValue 10 { base := .env e, name := .str "x" }) (.num 5.0)

/- A property reference reads through `[[Get]]`, so a GETTER runs. -/
#guard yields (do
  let g ← ordinaryFunctionCreate none (.builtin "%argCount%") none .strict true
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "p")
            { get := some (.obj g), enumerable := some true, configurable := some true }
  getValue 10 { base := .value (.obj o), name := .str "p" }) (.num 0.0)

/- `PutValue` writes through, and a STRICT write to a read-only property
throws `TypeError` — §6.2.5.6 step 5.e. -/
#guard throwsKind (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 1.0) false true true)
  putValue 10 { base := .value (.obj o), name := .str "k", strict := true } (.num 2.0))
  "TypeError"

/- A strict assignment to an UNDECLARED name throws; the sloppy arm needs
the realm and refuses as a HOST facility — the split earning its keep. -/
#guard throwsKind
  (putValue 10 { base := .unresolvable, name := .str "x", strict := true } (.num 1.0))
  "ReferenceError"
#guard refusesClass
  (putValue 10 { base := .unresolvable, name := .str "x", strict := false } (.num 1.0))
  "environment"

/-! ## `+` and the numeric operators — §13.15.3 -/

#guard yields (applyBinary 10 (.num 1.0) "+" (.num 2.0)) (.num 3.0)
#guard yields (applyBinary 10 (.num 5.0) "-" (.num 2.0)) (.num 3.0)
#guard yields (applyBinary 10 (.num 3.0) "*" (.num 4.0)) (.num 12.0)

/- `+` is the operator with the shape: if EITHER primitive is a String the
result is concatenation, which is why `1 + "2"` is `"12"`… -/
#guard yields (applyBinary 10 (.num 1.0) "+" (.str "2")) (.str "12")
#guard yields (applyBinary 10 (.str "a") "+" (.bool true)) (.str "atrue")

/- …while every other operator goes straight to numeric, so `1 - "2"` is
`-1` and NOT a string. -/
#guard yields (applyBinary 10 (.num 1.0) "-" (.str "2")) (.num (-1.0))

/- `null` converts to +0, `undefined` to NaN — so `1 + null` is 1 and
`1 + undefined` is NaN. -/
#guard yields (applyBinary 10 (.num 1.0) "+" .null) (.num 1.0)
#guard match SemM.run (applyBinary 10 (.num 1.0) "+" .undef) default with
  | .ok (.ok (.num n), _) => n.isNaN
  | _ => false

/-! ## `IsLessThan` — §7.2.13 answers THREE values, not two

NaN makes all four relational operators false, and that only works if the
comparison can say `undefined` rather than `false`. -/

#guard match SemM.run (isLessThan 10 (.num 1.0) (.num 2.0) true) default with
  | .ok (.ok (some true), _) => true | _ => false
#guard match SemM.run (isLessThan 10 (.num 2.0) (.num 1.0) true) default with
  | .ok (.ok (some false), _) => true | _ => false

/- The three-valued answer: NaN gives `none`, which is NOT `some false`. -/
#guard match SemM.run (isLessThan 10 (.num (0.0/0.0)) (.num 1.0) true) default with
  | .ok (.ok none, _) => true | _ => false

/- Two strings compare by code unit, never numerically — so "10" < "9". -/
#guard match SemM.run (isLessThan 10 (.str "10") (.str "9") true) default with
  | .ok (.ok (some true), _) => true | _ => false

end Examples.es.convert
