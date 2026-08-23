import LeanModels.Es.Convert
import LeanModels.Es.SpecAttr

/-!
# `@[es_spec]` — the tier's specification-lemma registry

M2 inch 1's third piece. One registry, and lemmas at **ARM-LEVEL
granularity**: a lemma per arm of each primitive, not one per function.

**Why arm-level.** A whole-function lemma of the form
`toBoolean v = <a big match>` is true and useless — it restates the
definition and a rewrite through it lands the caller back in a case split.
The arms are what a proof actually wants (`toBoolean (.str "") = false`),
they are what a `#guard` can pin, and — the fidelity point — **an arm is
the granularity at which a spec clause's STEP is stated**, so an
arm-level lemma is citable against `(edition, clause, step)` while a
whole-function one is citable only against the clause.

The attribute itself is declared in `LeanModels/Es/SpecAttr.lean`, and
that separation is forced: a `register_label_attr` attribute becomes
available at an IMPORT boundary, so it cannot be used in the file that
declares it. It follows the Python lane's `py_spec` — a label attribute,
per lane, so the ES vcgen's registry can never be confused with a
sibling's.

**Everything below is a `Bool` equation closed by `rfl`**, i.e. by KERNEL
reduction — which is only possible because none of these definitions is
`partial` and because core `Float` is kernel-reducible on the pin
(`harness/es/float_probe.lean`). §L66 recorded the trap: a `partial`
definition is opaque to the kernel, so a lemma or `#guard` stated through
one proves nothing.
-/

namespace LeanModels.Es

open Val

/-! ## `ToBoolean` — ES2026 §7.1.2, one lemma per row of the table -/

@[es_spec] theorem toBoolean_undef : toBoolean .undef = false := rfl
@[es_spec] theorem toBoolean_null : toBoolean .null = false := rfl
@[es_spec] theorem toBoolean_true : toBoolean (.bool true) = true := rfl
@[es_spec] theorem toBoolean_false : toBoolean (.bool false) = false := rfl
@[es_spec] theorem toBoolean_str_empty : toBoolean (.str "") = false := rfl
@[es_spec] theorem toBoolean_sym (i : SymId) (d : Option String) :
    toBoolean (.sym i d) = true := rfl
@[es_spec] theorem toBoolean_obj (r : ObjRef) : toBoolean (.obj r) = true := rfl

/-- The Number row is the one with edges, so it gets a lemma per edge.
`+0`, `-0` and `NaN` are falsy; every other Number is truthy. -/
@[es_spec] theorem toBoolean_pos_zero : toBoolean (.num 0.0) = false := rfl
@[es_spec] theorem toBoolean_neg_zero : toBoolean (.num (-0.0)) = false := rfl
@[es_spec] theorem toBoolean_nan : toBoolean (.num (0.0 / 0.0)) = false := rfl
@[es_spec] theorem toBoolean_one : toBoolean (.num 1.0) = true := rfl
@[es_spec] theorem toBoolean_inf : toBoolean (.num (1.0 / 0.0)) = true := rfl

/-- The BigInt row: `0n` is the only falsy BigInt. -/
@[es_spec] theorem toBoolean_bigint_zero : toBoolean (.bigint 0) = false := rfl
@[es_spec] theorem toBoolean_bigint_one : toBoolean (.bigint 1) = true := rfl

/-! ## The three equalities, pinned where they DIFFER

ES2026 §7.2.10 `SameValue`, §7.2.11 `SameValueZero`, §7.2.16
`IsStrictlyEqual` agree everywhere except on NaN and on ±0. Those two rows
are the whole content of the distinction and the classic implementation
bug, so each is a lemma in all three operations rather than a comment. -/

@[es_spec] theorem sameValue_nan :
    sameValue (.num (0.0 / 0.0)) (.num (0.0 / 0.0)) = true := rfl
@[es_spec] theorem sameValueZero_nan :
    sameValueZero (.num (0.0 / 0.0)) (.num (0.0 / 0.0)) = true := rfl
/-- `NaN === NaN` is FALSE — the row that separates `===` from the other two. -/
@[es_spec] theorem strictEquals_nan :
    strictEquals (.num (0.0 / 0.0)) (.num (0.0 / 0.0)) = false := rfl

/-- `SameValue(+0, -0)` is FALSE — the row that separates `Object.is` from
`===`. -/
@[es_spec] theorem sameValue_zeros :
    sameValue (.num 0.0) (.num (-0.0)) = false := rfl
@[es_spec] theorem sameValueZero_zeros :
    sameValueZero (.num 0.0) (.num (-0.0)) = true := rfl
@[es_spec] theorem strictEquals_zeros :
    strictEquals (.num 0.0) (.num (-0.0)) = true := rfl

/-- Cross-type comparison is `false` in all three, never a coercion:
`===` does not coerce, which is what distinguishes it from `==` (§7.2.15,
not modelled at this inch). -/
@[es_spec] theorem strictEquals_cross : strictEquals (.num 1.0) (.str "1") = false := rfl
@[es_spec] theorem strictEquals_undef_null : strictEquals .undef .null = false := rfl

/-- A Symbol is equal only to itself, and the DESCRIPTION is not part of
identity (§20.4.3.3 makes it informative). -/
@[es_spec] theorem sameValue_sym (i j : SymId) (d e : Option String) :
    sameValue (.sym i d) (.sym j e) = (i == j) := rfl

/-- …and therefore the description is irrelevant to identity, which is the
consequence a proof actually uses. Not `rfl`: `i == i` at a VARIABLE needs
`Nat.beq` to reduce, which it does only at a literal. -/
@[es_spec] theorem sameValue_sym_desc_irrelevant (i : SymId) (d e : Option String) :
    sameValue (.sym i d) (.sym i e) = true := by
  simp [sameValue]

/-! ## `typeof` — ES2026 §13.5.3.1, one lemma per row -/

@[es_spec] theorem typeof_undef (c) : typeofWith c .undef = "undefined" := rfl
/-- The famous row, and it is the spec's. -/
@[es_spec] theorem typeof_null (c) : typeofWith c .null = "object" := rfl
@[es_spec] theorem typeof_bool (c b) : typeofWith c (.bool b) = "boolean" := rfl
@[es_spec] theorem typeof_num (c n) : typeofWith c (.num n) = "number" := rfl
@[es_spec] theorem typeof_str (c s) : typeofWith c (.str s) = "string" := rfl
@[es_spec] theorem typeof_sym (c i d) : typeofWith c (.sym i d) = "symbol" := rfl
@[es_spec] theorem typeof_bigint (c i) : typeofWith c (.bigint i) = "bigint" := rfl
/-- The Object row is SPLIT by callability, which is why it is an input. -/
@[es_spec] theorem typeof_obj_callable (r : ObjRef) :
    typeofWith (fun _ => true) (.obj r) = "function" := rfl
@[es_spec] theorem typeof_obj_plain (r : ObjRef) :
    typeofWith (fun _ => false) (.obj r) = "object" := rfl

/-! ## The refusal covenant

A refusal is not an error a program can catch: it is not in `ρ`, so it
cannot be reached by `try`. These pin that, which is the property the
scoreboard's REFUSE bucket depends on. -/

@[es_spec] theorem refuse_is_not_catchable (W : Type) (w : W) (c : EsRefusal) (m : String) :
    SemM.run (ρ := Abrupt) (α := Unit) (SemM.refuse c m) w = .error (.unsupported c m none) := rfl

@[es_spec] theorem timeout_is_not_catchable (W : Type) (w : W) :
    SemM.run (ρ := Abrupt) (α := Unit) SemM.timeout w = .error .timeout := rfl

/-! ## The Property Descriptor classification — ES2026 §6.2.6.1-.3

Three predicates, and §10.1.6.3 branches on all three, so each gets its
arms rather than one lemma per predicate. -/

@[es_spec] theorem isData_of_value (v : Val) :
    PropDesc.isData { value := some v } = true := rfl
@[es_spec] theorem isData_of_writable (b : Bool) :
    PropDesc.isData { writable := some b } = true := rfl
@[es_spec] theorem isAccessor_of_get (g : Val) :
    PropDesc.isAccessor { get := some g } = true := rfl
@[es_spec] theorem isAccessor_of_set (s : Val) :
    PropDesc.isAccessor { set := some s } = true := rfl

/- The empty descriptor is GENERIC — neither data nor accessor. It is the
one §10.1.6.3 step 3 short-circuits on. -/
@[es_spec] theorem isGeneric_empty : PropDesc.isGeneric {} = true := rfl
@[es_spec] theorem isData_empty : PropDesc.isData {} = false := rfl
@[es_spec] theorem isAccessor_empty : PropDesc.isAccessor {} = false := rfl

/- A descriptor carrying only `enumerable`/`configurable` is STILL generic:
the classification asks about value/writable/get/set and nothing else. -/
@[es_spec] theorem isGeneric_of_enumerable (b : Bool) :
    PropDesc.isGeneric { enumerable := some b } = true := rfl

/-! ## `CompletePropertyDescriptor` — ES2026 §6.2.6.6, its two arms -/

@[es_spec] theorem complete_data_defaults (v : Val) :
    PropDesc.complete { value := some v }
      = { value := some v, writable := some false,
          enumerable := some false, configurable := some false } := rfl

@[es_spec] theorem complete_accessor_defaults (g : Val) :
    PropDesc.complete { get := some g }
      = { get := some g, set := some .undef,
          enumerable := some false, configurable := some false } := rfl

/-! ## Array indices — ES2026 §6.1.7

The rule an implementation gets wrong is leading zeros: `"01"` is a plain
string key, not index 1, so it enumerates with the string keys. -/

@[es_spec] theorem arrayIndex_zero : (PropKey.str "0").arrayIndex? = some 0 := rfl
@[es_spec] theorem arrayIndex_ten : (PropKey.str "10").arrayIndex? = some 10 := rfl
@[es_spec] theorem arrayIndex_leading_zero : (PropKey.str "01").arrayIndex? = none := rfl
@[es_spec] theorem arrayIndex_nonnumeric : (PropKey.str "x").arrayIndex? = none := rfl
@[es_spec] theorem arrayIndex_empty : (PropKey.str "").arrayIndex? = none := rfl
@[es_spec] theorem arrayIndex_symbol (i : SymId) : (PropKey.sym i).arrayIndex? = none := rfl

/-! ## Own-property storage

`put` REPLACES in place rather than appending, which is the half
`OrdinaryOwnPropertyKeys`'s creation order depends on. -/

@[es_spec] theorem find_empty (k : PropKey) : Obj.find? {} k = none := rfl

/-! ## Environment bindings — ES2026 §9.1.1.1

The TDZ is the distinction worth arms: an UNINITIALIZED binding is not a
binding holding `undefined`, and `Binding.value : Option Val` is what
keeps them apart. -/

@[es_spec] theorem binding_fresh_is_uninitialized :
    (Binding.value { mutable := true }) = none := rfl
@[es_spec] theorem binding_undefined_is_initialized :
    (Binding.value { value := some .undef, mutable := true }) = some .undef := rfl

@[es_spec] theorem env_find_empty (n : String) : EnvRec.find? {} n = none := rfl

/-! ## `[[ThisBindingStatus]]` — §9.1.1.3, §9.1.2.4

A fresh declarative record is `lexical` — it has no `this` at all, which is
what makes `GetThisEnvironment` walk THROUGH it. -/

@[es_spec] theorem fresh_env_is_lexical : (EnvRec.thisStatus {}) = ThisStatus.lexical := rfl

/-- The three statuses are distinct — `GetThisBinding` branches on
`uninitialized` and `BindThisValue` on `initialized`, so conflating any
two would silently change both. -/
@[es_spec] theorem thisStatus_distinct₁ :
    (ThisStatus.lexical == ThisStatus.uninitialized) = false := rfl
@[es_spec] theorem thisStatus_distinct₂ :
    (ThisStatus.uninitialized == ThisStatus.initialized) = false := rfl

/-! ## `IsCallable` / `IsConstructor` are SLOT TESTS — §7.2.3, §7.2.4

Neither inspects a value's shape: a non-object is never callable, and a
callable is not automatically a constructor. -/

@[es_spec] theorem thisMode_lexical_ne_strict :
    (ThisMode.lexical == ThisMode.strict) = false := rfl

/-- A plain function has `[[Call]]` and NOT `[[Construct]]` until
`MakeConstructor` runs — §10.2.5 is what adds the slot. -/
@[es_spec] theorem plain_function_is_not_constructor (b : Body) :
    (FuncData.constructorDerived { body := b }) = none := rfl

@[es_spec] theorem plain_object_is_not_callable : (Obj.callable {}) = none := rfl

/-! ## `Body` — inch 3's one boundary, now closed

A `builtin` runs; an `ecmascript` body CARRIES its `Code` as of inch 5 and
`Eval.evalCallBody` runs it. The constructors stay distinct, so the arm
still cannot be taken by accident — but the statement is `noConfusion`
rather than `== … = false`, because `Code` holds a `Node` and `Body` no
longer derives `DecidableEq`. Deriving it would have manufactured an
equality on function bodies that no clause of the spec asks for. -/

@[es_spec] theorem body_builtin_ne_ecmascript (n : String) (c : Code) :
    Body.builtin n ≠ Body.ecmascript c := by
  intro h; exact Body.noConfusion h

/-- The `Code` a function closes over survives into its slot unchanged —
§10.2.3 steps 6-7 store the Parse Nodes, they do not compile them. -/
@[es_spec] theorem ecmascript_body_keeps_its_code (ps : List Node) (b : Node) :
    (match Body.ecmascript { params := ps, body := b } with
     | .ecmascript c => (c.params, c.body)
     | .builtin _ => ([], b)) = (ps, b) := rfl

/-! ## The four REFUSE classes — §5.2, adopted at `14bdd7a`

Arms for the class map, and the two EXPECTED-EMPTY gates restated at the
lemma level (their proofs live in `Completion.lean`, where the constructor
they are about is). -/

@[es_spec] theorem class_construct (n : String) :
    (esRefusal .construct n).className = "unsupported" := rfl
@[es_spec] theorem class_intrinsic (n : String) :
    (esRefusal .unmodeledIntrinsic n).className = "environment" := rfl
@[es_spec] theorem class_host (n : String) :
    (esRefusal .hostFacility n).className = "environment" := rfl

/-- The payload keeps the retirement-schedule split the ruling preserved
as a candidate FIFTH class. -/
@[es_spec] theorem payload_keeps_the_split (n : String) :
    (match esRefusal .unmodeledIntrinsic n with
     | .environment d => d.kind
     | _ => EsCause.construct) = EsCause.unmodeledIntrinsic := rfl

/-! ## `Number::toString` — §6.1.6.1.20, the arms that are total

An `Option`: `none` is "outside the exact-integer fragment", and the
caller REFUSES rather than emitting the host's rendering. -/

@[es_spec] theorem numberToString_nan : numberToString (0.0 / 0.0) = some "NaN" := rfl
@[es_spec] theorem numberToString_inf : numberToString (1.0 / 0.0) = some "Infinity" := rfl
@[es_spec] theorem numberToString_neg_inf : numberToString (-1.0 / 0.0) = some "-Infinity" := rfl
@[es_spec] theorem numberToString_zero : numberToString 0.0 = some "0" := rfl

/-- **`-0` renders as `"0"`** — the row that separates `String(-0)` from
`Object.is(-0, 0)`, and the reason the zero arm tests `== 0.0` (which is
true of both zeros) rather than `sameValue`. -/
@[es_spec] theorem numberToString_neg_zero : numberToString (-0.0) = some "0" := rfl

/-! ### The exact-integer arm — PROVABLE, after a correction

An earlier version of this file recorded these as unprovable and named a
"second verification strength" for them. **That was wrong by one
projection**: `numberToString` went through `Float.toInt64`/`Float.toFloat`,
which are `@[extern]`, and the substitute is core's own `Float.Model` —
`n.toModel.toInt64` and `Float.ofModel (Float.Model.ofInt64 t)` reduce
where the extern pair does not. Measured by the SoftFloat lane and
re-checked here; the split is gone and these are ordinary `rfl` lemmas. -/

@[es_spec] theorem numberToString_int : numberToString 42.0 = some "42" := rfl
@[es_spec] theorem numberToString_neg_int : numberToString (-7.0) = some "-7" := rfl
@[es_spec] theorem numberToString_thousand : numberToString 1000.0 = some "1000" := rfl

/-- A non-integer answers `none`, so the caller refuses instead of
guessing — and this direction is provable too, now. What stays blocked is
the RENDERING of a non-integer, which needs correctly-rounded decimal
conversion (SoftFloat step 3), not the DETECTION of one. -/
@[es_spec] theorem numberToString_half : numberToString 0.5 = none := rfl

/-! ## Property-key text — §6.2.5's environment references use it -/

@[es_spec] theorem keyText_str (s : String) : (PropKey.str s).text = s := rfl

/-! ## Reference Records — §6.2.5.2, §6.2.5.3, one arm each -/

@[es_spec] theorem ref_unresolvable (n : PropKey) :
    Ref.isUnresolvable { base := .unresolvable, name := n } = true := rfl
@[es_spec] theorem ref_env_is_not_unresolvable (e : EnvRef) (n : PropKey) :
    Ref.isUnresolvable { base := .env e, name := n } = false := rfl
@[es_spec] theorem ref_value_is_property (v : Val) (n : PropKey) :
    Ref.isProperty { base := .value v, name := n } = true := rfl
@[es_spec] theorem ref_env_is_not_property (e : EnvRef) (n : PropKey) :
    Ref.isProperty { base := .env e, name := n } = false := rfl

end LeanModels.Es
