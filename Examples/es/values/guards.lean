import LeanModels.Es

/-!
# M2 inch 1's acceptance: the value model, pinned by kernel evaluation

`docs/es-semantics-design.md` inch 1. Every `#guard` below is decided by
the KERNEL, which is possible only because nothing here is `partial` and
core `Float` is kernel-reducible on the pinned toolchain
(`harness/es/float_probe.lean`).

The rows are chosen to be the ones an implementation gets WRONG: the
three equalities differ only on NaN and ±0, and `typeof null` is the
spec's own famous answer. A guard that pinned `1 === 1` would pin nothing.
-/

namespace Examples.es.values

open LeanModels.Es LeanModels.Es.Val

/-! ## The falsy set — ES2026 §7.1.2 -/

#guard toBoolean .undef == false
#guard toBoolean .null == false
#guard toBoolean (.bool false) == false
#guard toBoolean (.num 0.0) == false
#guard toBoolean (.num (-0.0)) == false
#guard toBoolean (.num (0.0 / 0.0)) == false
#guard toBoolean (.str "") == false
#guard toBoolean (.bigint 0) == false

/-! …and everything else is truthy, including the ones that surprise. -/

#guard toBoolean (.str "0") == true
#guard toBoolean (.str "false") == true
#guard toBoolean (.num (1.0 / 0.0)) == true
#guard toBoolean (.obj 0) == true

/-! ## The three equalities differ on exactly two rows -/

-- NaN: SameValue and SameValueZero say yes, `===` says no.
#guard sameValue (.num (0.0 / 0.0)) (.num (0.0 / 0.0)) == true
#guard sameValueZero (.num (0.0 / 0.0)) (.num (0.0 / 0.0)) == true
#guard strictEquals (.num (0.0 / 0.0)) (.num (0.0 / 0.0)) == false

-- ±0: SameValue says no, the other two say yes.
#guard sameValue (.num 0.0) (.num (-0.0)) == false
#guard sameValueZero (.num 0.0) (.num (-0.0)) == true
#guard strictEquals (.num 0.0) (.num (-0.0)) == true

-- Everywhere else the three agree.
#guard sameValue (.str "a") (.str "a") == true
#guard strictEquals (.str "a") (.str "b") == false
#guard strictEquals .undef .null == false
#guard strictEquals (.num 1.0) (.str "1") == false

/-! ## `typeof` — ES2026 §13.5.3.1 -/

#guard typeofWith (fun _ => false) .undef == "undefined"
#guard typeofWith (fun _ => false) .null == "object"
#guard typeofWith (fun _ => false) (.num 1.0) == "number"
#guard typeofWith (fun _ => false) (.sym 0 none) == "symbol"
#guard typeofWith (fun _ => false) (.bigint 1) == "bigint"
#guard typeofWith (fun _ => false) (.obj 0) == "object"
#guard typeofWith (fun _ => true) (.obj 0) == "function"

/-! ## Number IS binary64, and the tier depends on that deliberately

`docs/es-charter.md` §4.2(a): core `Float` is Layer 1, supplied. These
pin that the dependency actually reduces in the kernel — the property the
whole value model rests on. -/

#guard sameValue (.num (0.1 + 0.2)) (.num 0.30000000000000004) == true
#guard strictEquals (.num (0.1 + 0.2)) (.num 0.3) == false
#guard strictEquals (.num (1.0 + 1e16)) (.num 1e16) == true

/-! ## A refusal is not catchable

It is not in `ρ`, so no `try` can reach it. This is the property the
scoreboard's REFUSE bucket depends on, and it is a fact about the STACK
rather than about any operation. -/

#guard match SemM.run (W := Unit) (ρ := Abrupt) (α := Unit)
              (SemM.refuse .unmodeledIntrinsic "Symbol.species") () with
  | .unsupported .unmodeledIntrinsic _ => true
  | _ => false

#guard match SemM.run (W := Unit) (ρ := Abrupt) (α := Unit) SemM.timeout () with
  | .timeout => true
  | _ => false

/-! ## The three refusal causes are distinct — §3.6 says they are never pooled -/

#guard (RefusalCause.unsupportedConstruct == RefusalCause.unmodeledIntrinsic) == false
#guard (RefusalCause.unmodeledIntrinsic == RefusalCause.environment) == false

end Examples.es.values
