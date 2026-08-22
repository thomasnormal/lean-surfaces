import LeanModels.Es

/-!
# M2 inch 2's acceptance: the ordinary object model

`docs/es-semantics-design.md` inch 2 (§0.1's floor). Every `#guard` is
decided by the KERNEL — nothing here is `partial`.

The centrepiece is the **`sta.js` floor**: `docs/es-semantics-design.md`
§0.1 measured that no test262 test can even report a failure until a tier
can create an ordinary object, define a data property on it, and walk a
prototype chain, because `harness/sta.js` builds `Test262Error` out of
exactly those three. §"the sta.js floor" below is that shape.
-/

namespace Examples.es.objects

open LeanModels.Es

/-- Run a computation from an empty realm and ask whether it answered `v`. -/
def answers (m : EsW Bool) (v : Bool) : Bool :=
  match SemM.run m default with
  | .ok (.ok r, _) => r == v
  | _ => false

/-- …and the same for a `Val` result. -/
def yields (m : EsW Val) (v : Val) : Bool :=
  match SemM.run m default with
  | .ok (.ok r, _) => Val.sameValue r v
  | _ => false

/-- Did the computation REFUSE, with this cause? -/
def refusesWith (m : EsW α) (cls : String) : Bool :=
  match SemM.run m default with
  | .unsupported c _ => c.className == cls
  | _ => false

/-! ## The `sta.js` floor

    function Test262Error(message) { this.message = message || ""; }
    Test262Error.prototype.toString = function () { … };

An object, a data property on it, a prototype, and a read THROUGH the
prototype. If any of these four fails, no test262 test can be scored. -/

#guard yields (do
  let proto ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty proto (.str "toString")
            (PropDesc.data (.str "fn") true false true)
  let inst ← ordinaryObjectCreate (some proto)
  let _ ← ordinaryDefineOwnProperty inst (.str "message")
            (PropDesc.data (.str "boom") true true true)
  ordinaryGet 10 inst (.str "message") (.obj inst)) (.str "boom")

/- …and `toString` is found on the PROTOTYPE, not on the instance. -/
#guard yields (do
  let proto ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty proto (.str "toString")
            (PropDesc.data (.str "fn") true false true)
  let inst ← ordinaryObjectCreate (some proto)
  ordinaryGet 10 inst (.str "toString") (.obj inst)) (.str "fn")

/- An absent property is `undefined`, never a refusal — §10.1.8.1 step 3.b. -/
#guard yields (do
  let o ← ordinaryObjectCreate none
  ordinaryGet 10 o (.str "nope") (.obj o)) .undef

/-! ## The receiver rule — what §10.1.9.2's 20 steps are FOR

`obj.x = 1` where `x` lives on the prototype must create an OWN property
on `obj` and leave the prototype untouched. Getting this wrong makes every
object on a shared prototype alias. -/

#guard match SemM.run (do
    let proto ← ordinaryObjectCreate none
    let _ ← ordinaryDefineOwnProperty proto (.str "x")
              (PropDesc.data (.num 1.0) true true true)
    let inst ← ordinaryObjectCreate (some proto)
    let ok ← ordinarySet 10 inst (.str "x") (.num 2.0) (.obj inst)
    let onInst ← ordinaryGetOwnProperty inst (.str "x")
    let onProto ← ordinaryGet 10 proto (.str "x") (.obj proto)
    return (ok, onInst.isSome, onProto)) default with
  | .ok (.ok (true, true, .num p), _) => p == 1.0   -- prototype UNCHANGED
  | _ => false

/- A non-writable data property refuses `[[Set]]` — §10.1.9.2 step 2.b. -/
#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k")
            (PropDesc.data (.num 1.0) false true true)
  ordinarySet 10 o (.str "k") (.num 2.0) (.obj o)) false

/-! ## `ValidateAndApplyPropertyDescriptor` — §10.1.6.3, the 34 steps -/

/- A configurable property may be redefined. -/
#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 1.0) true true true)
  ordinaryDefineOwnProperty o (.str "k") { value := some (.num 2.0) }) true

/- A NON-configurable, NON-writable one may not change value — step 5.e. -/
#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 1.0) false true false)
  ordinaryDefineOwnProperty o (.str "k") { value := some (.num 2.0) }) false

/- …but redefining it to the SAME value is allowed — the step-5.e test is
`SameValue`, not "is a value present". -/
#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 1.0) false true false)
  ordinaryDefineOwnProperty o (.str "k") { value := some (.num 1.0) }) true

/- A non-configurable property cannot become configurable — step 5.a. -/
#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 1.0) true true false)
  ordinaryDefineOwnProperty o (.str "k") { configurable := some true }) false

/- A non-configurable property cannot change KIND — step 5.c. -/
#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 1.0) true true false)
  ordinaryDefineOwnProperty o (.str "k") { get := some .undef }) false

/-! ## Extensibility — §10.1.4, §10.1.6.3 step 2 -/

#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryPreventExtensions o
  ordinaryDefineOwnProperty o (.str "fresh") (PropDesc.data (.num 1.0) true true true)) false

/- …but an EXISTING property is still writable after preventExtensions. -/
#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 1.0) true true true)
  let _ ← ordinaryPreventExtensions o
  ordinarySet 10 o (.str "k") (.num 2.0) (.obj o)) true

/-! ## `[[Delete]]` — §10.1.10.1 -/

#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 1.0) true true true)
  ordinaryDelete o (.str "k")) true

/- A non-configurable property refuses deletion — step 5. -/
#guard answers (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "k") (PropDesc.data (.num 1.0) true true false)
  ordinaryDelete o (.str "k")) false

/-! ## `[[OwnPropertyKeys]]` order — §10.1.11.1, and the order is NORMATIVE

Integer indices ascending FIRST, then string keys in creation order, then
symbols in creation order — regardless of the order they were defined. -/

#guard match SemM.run (do
    let o ← ordinaryObjectCreate none
    let d := PropDesc.data .undef true true true
    let _ ← ordinaryDefineOwnProperty o (.str "b") d
    let _ ← ordinaryDefineOwnProperty o (.str "10") d
    let _ ← ordinaryDefineOwnProperty o (.sym 7) d
    let _ ← ordinaryDefineOwnProperty o (.str "2") d
    let _ ← ordinaryDefineOwnProperty o (.str "a") d
    ordinaryOwnPropertyKeys o) default with
  | .ok (.ok ks, _) =>
      ks == [.str "2", .str "10", .str "b", .str "a", .sym 7]
  | _ => false

/- `"10"` is an array index; `"01"` and `"x"` are not — §6.1.7. -/
#guard (PropKey.str "10").arrayIndex? == some 10
#guard (PropKey.str "0").arrayIndex? == some 0
#guard (PropKey.str "01").arrayIndex?.isNone
#guard (PropKey.str "x").arrayIndex?.isNone
#guard (PropKey.sym 0).arrayIndex?.isNone

/-! ## `[[SetPrototypeOf]]` refuses a CYCLE — §10.1.2.1 steps 8-11 -/

#guard answers (do
  let a ← ordinaryObjectCreate none
  let b ← ordinaryObjectCreate (some a)
  ordinarySetPrototypeOf 10 a (some b)) false        -- a→b→a would cycle

#guard answers (do
  let a ← ordinaryObjectCreate none
  let b ← ordinaryObjectCreate none
  ordinarySetPrototypeOf 10 a (some b)) true

/-! ## The ACCESSOR boundary refuses LOUDLY

Inch 2 has no `[[Call]]`, so a getter cannot run. The arm must REFUSE, not
quietly answer `undefined` — a silent `undefined` here would be a wrong
answer that every accessor test would then score as a pass. -/

#guard refusesWith (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "g")
            { get := some (.obj 0), enumerable := some true, configurable := some true }
  ordinaryGet 10 o (.str "g") (.obj o)) "unsupported"

/- …but a getter that is literally `undefined` answers `undefined`
without needing a call — §10.1.8.1 step 7, honoured BEFORE the refusal. -/
#guard yields (do
  let o ← ordinaryObjectCreate none
  let _ ← ordinaryDefineOwnProperty o (.str "g")
            { get := some .undef, set := some .undef,
              enumerable := some true, configurable := some true }
  ordinaryGet 10 o (.str "g") (.obj o)) .undef

/-! ## Fuel is an INDEX: exhaustion is `timeout`, never a wrong answer -/

#guard match SemM.run (do
    let a ← ordinaryObjectCreate none
    let b ← ordinaryObjectCreate (some a)
    ordinaryGet 0 b (.str "k") (.obj b)) default with
  | .timeout => true
  | _ => false

end Examples.es.objects
